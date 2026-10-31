-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.node_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:54:03.390799+00:00
-- url     : https://prove2.me/submissions/46a71ea9-4820-4ed2-8078-034bacae8318

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation_nodeSource_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation_prepare_native_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeSourceBounds_headBounds
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeSourceBounds_retainedCap
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StreamedQueryCostBudgets_actual_key_inventory_le_maxRank
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StreamedQueryMeasuredCost_pair_cost_le_assembled
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_TupleRunBudgets_run_bounds

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/

variable {V R : Type*} [DecidableEq V] [CommRing R]

private theorem localBudget_mono (n B d u J N a : ℕ)
    (hn : n ≤ a) (hB : B ≤ a) (hd : d ≤ a) (hu : u ≤ a) (hJ : J ≤ a) (hN : N ≤ a) :
    localBudget n B d u J N ≤ localBudget a a a a a a := by
  dsimp [localBudget, normalizationBudget, additionBudget, scalingBudget, productBudget,
    Product.stepEnvelope, MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  gcongr

/-- The degree and constant are fixed before every runtime dimension. -/
theorem localBudget_le (n B d u J N : ℕ) :
    localBudget n B d u J N ≤ 3000000 * (n + B + d + u + J + N + 1) ^ 10 := by
  let a := n + B + d + u + J + N + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  refine (localBudget_mono n B d u J N a (by dsimp [a]; omega) (by dsimp [a]; omega)
    (by dsimp [a]; omega) (by dsimp [a]; omega) (by dsimp [a]; omega)
    (by dsimp [a]; omega)).trans ?_
  change localBudget a a a a a a ≤ 3000000 * a ^ 10
  have h0 : 1 ≤ a ^ 10 := Nat.one_le_pow 10 a ha
  have h1 : a ≤ a ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h2 : a ^ 2 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h3 : a ^ 3 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h4 : a ^ 4 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h5 : a ^ 5 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h6 : a ^ 6 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h7 : a ^ 7 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h8 : a ^ 8 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h9 : a ^ 9 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  dsimp [localBudget, normalizationBudget, additionBudget, scalingBudget, productBudget,
    Product.stepEnvelope, MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  ring_nf
  omega

theorem additionBudget_le_local (n B d u J N : ℕ) :
    additionBudget n B d u J ≤ localBudget n B d u J N := by
  unfold localBudget
  omega

theorem scalingBudget_le_local (n B d u J N : ℕ) :
    scalingBudget n B d u J ≤ localBudget n B d u J N := by
  unfold localBudget
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSwapMultiplicity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Multiplicities of register-swap eigenvalue labels

The negative local labels are strictly below the diagonal and the positive
labels are on or above it. Counting these labels and their tensor words is
independent of the characteristic of the coefficient field.
-/

namespace SubexponentialSAT.SubexpSwapMultiplicity

open scoped BigOperators

/-- The local negative probability belongs to the range used in the paper. -/
theorem negativeProbability_bounds (r : ℕ) (hr : 2 ≤ r) :
    (1 / 4 : ℚ) ≤ negativeProbability r ∧ negativeProbability r < 1 / 2 := by
  have hrQ : (2 : ℚ) ≤ r := by exact_mod_cast hr
  have hden : (0 : ℚ) < 2 * r := by linarith
  constructor
  · unfold negativeProbability
    apply (le_div_iff₀ hden).mpr
    linarith
  · unfold negativeProbability
    apply (div_lt_iff₀ hden).mpr
    linarith

/-! ## General binomial second moment and the interval tail -/

end SubexponentialSAT.SubexpSwapMultiplicity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TailInterval
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A computable centered interval for the multicolor binomial tail

The swap mean is between (Q - 1) / 4 and (Q - 1) / 2.  Taking the natural
floor of mean - R / 2 gives an interval of R consecutive integer weights.
The rounding error is at most one, absorbed by R ≥ 4.
-/

namespace SubexponentialSAT.Subexp.TailInterval

open SubexponentialSAT.SubexpSwapMultiplicity
open scoped BigOperators

theorem centeredStart_bounds {μ : ℚ} {R : ℕ} (hcenter : (R : ℚ) / 2 ≤ μ) :
    (centeredStart μ R : ℚ) ≤ μ - (R : ℚ) / 2 ∧
      μ - (R : ℚ) / 2 < (centeredStart μ R : ℚ) + 1 := by
  exact ⟨Nat.floor_le (by linarith), Nat.lt_floor_add_one _⟩

theorem mean_bounds (r Q : ℕ) (hr : 2 ≤ r) :
    ((Q - 1 : ℕ) : ℚ) / 4 ≤ mean r Q ∧
      mean r Q ≤ ((Q - 1 : ℕ) : ℚ) / 2 := by
  obtain ⟨hlo, hhi⟩ := negativeProbability_bounds r hr
  have hlo' := mul_le_mul_of_nonneg_left hlo (show (0 : ℚ) ≤ (Q - 1 : ℕ) from Nat.cast_nonneg _)
  have hhi' := mul_le_mul_of_nonneg_left hhi.le (show (0 : ℚ) ≤ (Q - 1 : ℕ) from Nat.cast_nonneg _)
  dsimp [mean]
  constructor <;> linarith

theorem half_width_le_mean {r Q R : ℕ} (hr : 2 ≤ r)
    (hsize : 4 * R ≤ Q) :
    (R : ℚ) / 2 ≤ mean r Q := by
  have hq : 2 * R ≤ Q - 1 := by omega
  have hqQ : (2 : ℚ) * R ≤ (Q - 1 : ℕ) := by exact_mod_cast hq
  have hlo := (mean_bounds r Q hr).1
  linarith

/-- The interval fits within the available weights 0,...,Q-1. -/
theorem intervalStart_end_le {r Q R : ℕ} (hr : 2 ≤ r)
    (hR : 4 ≤ R) (hsize : 4 * R ≤ Q) :
    intervalStart r Q R + R ≤ Q := by
  have hcenter := half_width_le_mean hr hsize
  have hlo := (centeredStart_bounds hcenter).1
  have hmean := (mean_bounds r Q hr).2
  have hq : ((Q - 1 : ℕ) : ℚ) ≤ Q := by
    exact_mod_cast Nat.sub_le Q 1
  have hRQ : (R : ℚ) ≤ Q := by
    exact_mod_cast (show R ≤ Q by omega)
  have hend : (centeredStart (mean r Q) R : ℚ) + R ≤ Q := by linarith
  exact_mod_cast hend

end SubexponentialSAT.Subexp.TailInterval

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramMagnitudeOffset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact unsigned-pair budget accepted by the offset/signature pipeline. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

theorem denominator_le_scalarBound (Q R : ℕ) (hQ : 1 ≤ Q) :
    2^(R-1) ≤ (8*Q)^(2*R) := by
  calc
    _ ≤ 2^(2*R) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ (8*Q)^(2*R) := Nat.pow_le_pow_left (by omega) _

theorem constraintMassBound_le (Q R : ℕ) (hQ : 1 ≤ Q) :
    constraintMassBound Q R ≤ 2*(8*Q)^(2*R) := by
  have h := denominator_le_scalarBound Q R hQ
  unfold constraintMassBound
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Composition of the concrete streamed query. The traversal resource lemma
keeps the per-head execution time separate from its prefix storage bound;
neither the number of assignments nor their running time is used as space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

theorem PrefixBound.mono {command : Code} {steps B D : ℕ} {a : Data}
    (h : PrefixBound command steps a B) (hBD : B ≤ D) :
    PrefixBound command steps a D :=
  ⟨fun q z hq hz i => (h.bound q z hq hz i).trans hBD⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer layout parameters agreed with the layout and spectral components.
The occurrence bound `b` is an explicit argument. Positivity assumptions are
kept on theorems rather than built into an opaque choice. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem layoutCutoff_ge_four (n b : ℕ) : 4 ≤ layoutCutoff n b := by
  unfold layoutCutoff
  omega

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact runtime parameter semantics. Every definition below uses natural
arithmetic; the executable refinements are separate from these specifications.
The original ambient dimension is retained through high-incidence branching. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

theorem produce_R_ge_four (x : Input) : 4 ≤ (produce x).R := Asymptotic.layoutCutoff_ge_four _ _

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedHeads
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual emitted original-ID head lists inherit the searched packing's
head bound. Taking the maximum is proof-only and introduces no new search. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes LeafHeadSetupProgram

variable {I : Type*} [Fintype I] [DecidableEq I] {n N r Q : ℕ}

theorem selected_le_max (n Q r : ℕ) (rows : List (List Bool)) (low : List Bool)
    (t : Fin Q) (g : Fin r) :
    (selectedHeads n rows low (t.val*r+g.val)).length ≤ maxSelected n Q r rows low :=
  Finset.le_sup (f := fun z : Fin Q × Fin r =>
    (selectedHeads n rows low (z.1.val*r+z.2.val)).length) (Finset.mem_univ (t,g))

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Explicit compact boundary, source and arithmetic caps for the actual head
sum. Their fixed polynomial certificates depend on source dimensions and
physical word lengths, independently of the number of head assignments. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open FactorTableBudgets

theorem compact_le (A : ℕ) : A+1 ≤ compactCap A := by
  unfold compactCap
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesScalars
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial numerical dimensions of every actual large-input query.
These bounds do not include serialized bucket or sparse-dictionary buffers. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend
open scoped Topology

 theorem input_ambient (q : Query) (k : ℕ) : (q.input k).ambient=ambient q := rfl
 theorem input_width (q : Query) (k : ℕ) : (q.input k).width=k := rfl
 theorem input_clauses (q : Query) (k : ℕ) (hv : q.Valid) :
    (q.input k).clauses=q.clauses.length := hv.2.2.2.2.2.1

end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical constructor for an actual query. Rank and maximum head size
are its two geometry arguments; ProducedQueryRank and LayoutProducedHeads
supply them from the actual packing. This module does not assert that an
arbitrary pair of natural numbers has those geometric bounds. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend CostAssembly
open scoped Topology

noncomputable section

 theorem make_bits_pos (q : Query) (k B rows size C d qi e : ℕ) :
    1 ≤ (make q k B rows size C d qi e).bits := by
  exact Nat.one_le_pow _ _ (by omega)

 theorem make_heads_pos (q : Query) (k B rows size C d qi e : ℕ) :
    1 ≤ (make q k B rows size C d qi e).heads :=
  (by have := layoutR_ge_two (q.input k).freeCount; exact Nat.le_trans (by decide) this)

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesPacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The resource geometry is read from the actual searched packing and its
emitted original-variable word rows. No rank or head-size number is supplied
as a machine input. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
open LeafQueryFrontend
noncomputable section

theorem selected_length_le (q : Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q))
    (t : Fin (problem q k hg).Q) (g : Fin (problem q k hg).r) :
    (LeafHeadSetupProgram.selectedHeads (problem q k hg).n
      (ProducedQueryRank.rows (problem q k hg) a tail) (lowBytes q)
      (t.val*(problem q k hg).r+g.val)).length ≤ (ofPacking q k B C d qi e hg a tail).headSize :=
  LayoutProducedHeads.selected_le_max _ _ _ _ _ t g

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryEnvelopeBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The original explicit resource record for the actual packing has the
sqrt-log bound from the new literal scope estimates. No identity with the old
selector history is used. These are numerical bounds on that record; a caller
still composes and bounds the actual streamed execution. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets

open Filter OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic
  OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources
  OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open scoped Topology

noncomputable section

/-- The original jet order is exactly the order of the actual serialized
parameter producer, including ambient precision and neutral factors. -/
theorem produced_order_eq (q : Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q)) (hv : q.Valid) :
    (LeafParametersProgram.produce (q.input k)).J =
      jetOrder k (ambient q) (ofPacking q k B C d qi e hg a tail) := by
  unfold LeafParametersProgram.produce jetOrder jetNumerator ofPacking make
  dsimp only
  rw [input_ambient, input_width, input_clauses q k hv]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NodeTimeColumns
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing SubexpSetupStorage
open LeafHeadSetupProgram LeafHeadSetupProgram.Bounds
open LayoutProgram RowSelectionProgram

theorem inputBounds (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (h : Native.Ready s a) (B : ℕ) (hb : WordBound B a) : InputBounds s B := by
  have hp : (LayoutOwnerFiberProgram.stream s.plans).length ≤ B := by simpa only [h.plans] using hb 136
  have hc := Encoding.length_encodeList_lower (fun p : ℕ×ℕ => LayoutOwnerFiberProgram.pairPayload p.1 p.2) s.plans
  have hd : s.D ≤ B := by
    change s.plans.length+1 ≤ (LayoutOwnerFiberProgram.stream s.plans).length at hc
    rw [s.plans_length] at hc
    omega
  exact ⟨by simpa [h.ambient,unary] using hb 128,hd,
    by simpa [h.colors,unary] using hb 130,by simpa [h.nodes,unary] using hb 131,
    by simpa [h.order,unary] using hb 138,by simpa only [h.width] using hb 140,
    by simpa only [h.height] using hb 139,by simpa only [h.metadata] using hb 135,hp,
    by simpa [h.wordWidth,unary] using hb 132⟩

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A concrete numerical HeadBounds certificate for the actual visitor.
Source columns are bounded from its stored native input, all incidence rows
remain present, and the compact endpoint cap is separate from transient space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
open OAI BitProgram StructuredCalls SubexpSetupStorage SubexpLiftRing
open SqrtLog SqrtLog.LeafProgram SqrtLog.LeafHeadSetupProgram
open HeadSumBudgets FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

private theorem sourceSize_large (A : ℕ) : A+1 ≤ sourceSize A := by
  unfold sourceSize
  omega

private theorem scalarCap_large (A : ℕ) : sourceSize A+1 ≤ scalarCap A := by
  have h : sourceSize A+1 ≤ (sourceSize A+1)^10 := Nat.le_self_pow (by decide) _
  unfold scalarCap
  omega

theorem original_le_scalar (A : ℕ) : A+1 ≤ scalarCap A := by
  have h1 := sourceSize_large A
  have h2 := scalarCap_large A
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cursor semantics for the attained-signature tuple controller

The cursor stores an attained prefix and one numeric candidate. Suspended
ancestors are first occurrences, so the tree branches over attained keys only.
The traces and finite sums below are mathematical specifications; the actual
controller retains neither a trace nor a family of assignments or tuples.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

open scoped BigOperators
open SignatureTupleDFS

open Classical

variable {N : ℕ → ℕ} {κ : ℕ → Type*}

section KeyEncoding

theorem card_representative_kernel {n : ℕ} {A B : Type*}
    (actual : Fin n → A) (model : Fin n → B)
    (hkernel : ∀ i j, actual i = actual j ↔ model i = model j) :
    Nat.card (AttainedSignatures.Representative actual) =
      Nat.card (AttainedSignatures.Representative model) :=
  Nat.card_congr (representativeKernelEquiv actual model hkernel)

end KeyEncoding

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

/-- The retained cap has fixed degree36. No input-dependent exponent is
introduced by the depth, assignment counter or repeated head reconstruction. -/
theorem retainedEnvelope_polynomial (B A : ℕ) :
    retainedEnvelope B A ≤ (100000*20000^6+10050)*(A+B+2)^36 := by
  let X := A+B+2
  change retainedEnvelope B A ≤ (100000*20000^6+10050)*X^36
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h1 : X ≤ X^36 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1 ≤ 36)
  have h2 : X^2 ≤ X^36 := pow_le_pow_right₀ hX (by decide)
  have h6 : X^6 ≤ X^36 := pow_le_pow_right₀ hX (by decide)
  have h0 : 1 ≤ X^36 := one_le_pow₀ hX
  have hb : B ≤ X := by dsimp [X]; omega
  have hb1 : B+1 ≤ X := by dsimp [X]; omega
  have hb2 : B+2 ≤ X := by dsimp [X]; omega
  have ha : A ≤ X := by dsimp [X]; omega
  have hscan : scannerEnvelope B ≤ (100000*20000^6)*X^36 := by
    unfold scannerEnvelope
    rw [mul_pow,←pow_mul]
    change 100000*(20000^6*(B+2)^36) ≤ _
    calc
      _ ≤ 100000*(20000^6*X^36) := by gcongr
      _=_ := (Nat.mul_assoc _ _ _).symm
  have ho : 10000*(B+2)^6 ≤ 10000*X^36 := Nat.mul_le_mul_left 10000 ((Nat.pow_le_pow_left hb2 6).trans h6)
  have hf : 6*B*(B+1) ≤ 6*X^36 := by
    calc
      _ ≤ 6*X*X := by gcongr
      _=6*X^2 := by rw [pow_two,Nat.mul_assoc]
      _ ≤ 6*X^36 := Nat.mul_le_mul_left 6 h2
  have hs : B*B ≤ X^36 := (Nat.mul_le_mul hb hb).trans (by simpa only [pow_two] using h2)
  have hA := ha.trans h1
  have hB := hb.trans h1
  have hB1 := hb1.trans h1
  unfold retainedEnvelope
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of a node evaluation. The paid node read, layout
load, native cache bootstrap and pair setup are the fixed commands used by the
streaming query; no evaluator is supplied to these constructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

/-- The cache-copy bound follows the actual visible ring masters. It stays
independent of larger retained tuple and collector words. -/
theorem prepared_common_cache_bound {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {node : Fin Q} {H : Finset (Fin n)} {high : H → Bool} {P A : ℕ}
    {a b : Data} (h : QueryReadyConstruction.CommonReady q node H high P b)
    (hframe : ∀ i ∈ framePorts,b.stacks i=a.stacks i)
    (hambient : a.stacks 730=List.replicate n true)
    (hvisible : ∀ i ∈ cacheInputPorts,(a.stacks i).length ≤ A) :
    QueryReadyConstruction.CommonReady q node H high A b := by
  have h128 : (b.stacks 128).length ≤ A := by
    have hn := hvisible 730 (by decide)
    change (a.stacks 730).length ≤ A at hn
    rw [hambient,List.length_replicate] at hn
    simpa only [h.ambient,List.length_replicate] using hn
  have hword (i : Fin 768) (hi : i.castAdd 128 ∈ framePorts)
      (hv : i.castAdd 128 ∈ cacheInputPorts) :
      (b.stacks (i.castAdd 128)).length ≤ A := by
    rw [hframe _ hi]
    exact hvisible (i.castAdd 128) hv
  refine {h with
    cacheCaps := ?_
    ambientCap := h128
    oneCap := hword 207 (by decide) (by decide)}
  intro p hp
  simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,
    List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact h128 | exact hword _ (by decide) (by decide)

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TupleRunBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The same compact endpoint cap supports the actual tuple controller and
its visitor. Transient scanner/reload work is bounded separately; none of it
is fed back into the retained frame cap between pairs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open SignatureTupleSource SignatureTupleComplete SignatureTupleLoader

private theorem square_le_compact (T : ℕ) : T^2 ≤ HeadSumBudgets.compactCap T := by
  have hp : T*T ≤ FactorTableBudgets.payloadEnvelope T := by
    unfold FactorTableBudgets.payloadEnvelope
    calc
      T*T = T*T*1 := (Nat.mul_one _).symm
      _ ≤ T*T*(2*(T+T+T)+2*T*(2*T)+2) := Nat.mul_le_mul_left _ (by omega)
  unfold HeadSumBudgets.compactCap
  rw [pow_two]
  omega

/-- The fixed degree36 scanner and both persistent frame banks fit the
already chosen compact head cap, including at ambient size zero. -/
theorem retained_le_compact (B A : ℕ) (hB : B ≤ A) :
    retainedEnvelope B 0 ≤ QueryHeadBudgets.compact A := by
  have hsource : 100*(A+2)^2 ≤ QueryHeadBudgets.sourceSize A+1 := by
    have h := Nat.mul_le_mul_right (100*(A+2)^2+2) (show 1 ≤ A+1 by omega)
    unfold QueryHeadBudgets.sourceSize
    omega
  have hpower : (A+2)^36 ≤ (A+2)^40 := Nat.pow_le_pow_right (by omega) (by decide)
  have hscalar : (QueryHeadBudgets.sourceSize A+1)^20 ≤ (QueryHeadBudgets.scalarCap A)^2 := by
    unfold QueryHeadBudgets.scalarCap
    rw [mul_pow,←pow_mul]
    norm_num
  calc
    retainedEnvelope B 0 ≤ (100000*20000^6+10050)*(B+2)^36 := by
      simpa only [Nat.zero_add] using retainedEnvelope_polynomial B 0
    _ ≤ (100000*20000^6+10050)*(A+2)^36 := by gcongr
    _ ≤ 100^20*(A+2)^40 := Nat.mul_le_mul (by norm_num) hpower
    _ = (100*(A+2)^2)^20 := by rw [mul_pow,←pow_mul]
    _ ≤ (QueryHeadBudgets.sourceSize A+1)^20 := Nat.pow_le_pow_left hsource 20
    _ ≤ (QueryHeadBudgets.scalarCap A)^2 := hscalar
    _ ≤ QueryHeadBudgets.compact A := square_le_compact _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeSourceBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete capacities for the actual addressed node source. Its reference
snapshot is bounded only by retained query words, independently of caller
scratch, node index and the actual bootstrap cache witness. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds
open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram LeafParametersProgram LeafProgram
open QueryNodeEvaluation

/-- Ordinary cache and output arrays fit the same already fixed compact
cap; this bound contains no callback count or transient budget. -/
theorem compact_capacity (A : ℕ) : 20*(A+1)^4 ≤ QueryHeadBudgets.compact A := by
  have hp : (A+1)^4 ≤ (A+2)^6 :=
    (Nat.pow_le_pow_left (by omega : A+1≤A+2) 4).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  apply le_trans (b := SignatureTupleComplete.retainedEnvelope A 0) ?_
    (TupleRunBudgets.retained_le_compact A A (Nat.le_refl A))
  have hm : 20*(A+1)^4 ≤ 10000*(A+2)^6 := Nat.mul_le_mul (by decide) hp
  unfold SignatureTupleComplete.retainedEnvelope
  omega

/-- The full ordered output array fits before any node cache is produced. -/
theorem array_capacity (Q J d t A : ℕ)
    (hQ : Q≤A) (hJ : J≤A) (hd : d≤A) (ht : t≤A) :
    Q*(J*(d*SubexpLiftRing.baseWidth 3 t))≤QueryHeadBudgets.compact A ∧
    Q≤QueryHeadBudgets.compact A := by
  have hword : Q*(J*(d*SubexpLiftRing.baseWidth 3 t))≤A*(A*(A*(2*A))) := by
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  have hp : 2*A^4≤20*(A+1)^4 := Nat.mul_le_mul (by decide)
    (Nat.pow_le_pow_left (by omega) 4)
  have hA : A≤QueryHeadBudgets.compact A := by
    have h := QueryHeadBudgets.original_le_scalar A
    have hh := HeadSumBudgets.compact_le (QueryHeadBudgets.scalarCap A)
    change _ ≤ QueryHeadBudgets.compact A at hh
    omega
  refine ⟨?_,hQ.trans hA⟩
  apply hword.trans
  calc
    A*(A*(A*(2*A))) = 2*A^4 := by ring
    _ ≤ 20*(A+1)^4 := hp
    _ ≤ QueryHeadBudgets.compact A := compact_capacity A

/-- The paid native bootstrap's actual retained cache words fit the same
compact node boundary, independently of the chosen cache encoding witness. -/
theorem bootstrap_capacity_of_ready (s : Native.Inputs)
    (state : LeafHeadSetupProgram.Data) (A : ℕ)
    (ready : Native.Ready s state) (bounded : WordBound A state) :
    SignatureHeadLoader.bootstrapOutputBound s ≤ QueryHeadBudgets.compact A := by
  have hi := NodeTime.inputBounds s state ready A bounded
  have hm := Nat.mul_le_mul hi.R hi.width
  have hp1 : A+1 ≤ (A+1)^4 := Nat.le_self_pow (by decide) _
  have hp2 : A^2 ≤ (A+1)^4 :=
    (Nat.pow_le_pow_left (by omega : A≤A+1) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ 20*(A+1)^4 := by
    unfold SignatureHeadLoader.bootstrapOutputBound
    have hQr := hi.Qr
    have hr := hi.r
    have hD := hi.D
    have hw := hi.width
    have hh := hi.height
    have hR := hi.R
    rw [pow_two] at hp2
    omega
  exact hcap.trans (compact_capacity A)


variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
  (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
variable (a : QueryNodeEvaluation.Data) (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
  (hbank : NativeLayoutLoad.SourceBank (Native.queryInputsAddressed query k hg first tail node) a)
  (hparked : ∀ j : Fin 14,
    (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed query k hg first tail node).height
    (unary (Native.queryInputsAddressed query k hg first tail node).R)
    (Native.queryInputsAddressed query k hg first tail node).width words)


local notation "src" => nodeSource query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc

section Factor
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3^(m.val 34))
    (hv : query.Valid) (hJ : 0 < m.val 42)
    (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
    (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e hp
  hfield query hv hJ source hsource

/-- The complete ordered node-output prefix is paid for as an actual array,
not by a traversal-time bound. Q and every jet/coefficient dimension are fixed
by the same source and produced scalar bank. -/
theorem node_capacity (hvalues : ∀ i, m.val i ≤ A) :
    (src).input.Q*((spec).J*((m.val 34)*SubexpLiftRing.baseWidth 3 (spec).p.t)) ≤
        QueryHeadBudgets.compact A ∧
    (src).input.Q ≤ QueryHeadBudgets.compact A := by
  have hi := NodeTime.inputBounds (src).input (src).source (src).ready A (src).bounded
  exact array_capacity _ _ _ _ A hi.Q (hvalues 42) (hvalues 34) (hvalues 33)

end Factor

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamedQueryCostBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The new traversal charges only attained full integer signatures. Its
predecessor rescans and complete-tuple visitors are additive, and the pair
count is bounded by the square of the original ambient support count. These
numerical comparisons use fixed powers of the original explicit cost; they
do not assert a machine execution or supply an evaluator service. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog SignatureTupleDFS SignatureTupleTraversal
open MulticolorTypes Subexp.ConstructivePacking LayoutExactBuckets

noncomputable section
open Classical

/-- The actual query's owner-fiber scan and scheduled height discharge the
entry cap. The exponent is exactly its original queryLabelRows, including
all selected heads and all raw incidence rows. -/
theorem query_inventory_le_labelRows
    (q : LeafQueryFrontend.Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (t : Fin (LeafProgram.Query.packingProblem q k hg).Q) :
    let p := LeafProgram.Query.packingProblem q k hg
    let R := (LeafParametersProgram.produce (q.input k)).R
    let A := Subexp.TailInterval.intervalStart p.r p.Q R
    let selected := fun g : Fin p.r => LeafHeadSetupProgram.selectedHeads p.n
      (ProducedQueryRank.rows p first tail) (ProducedQueryRank.queryLow q) (t.val*p.r+g.val)
    (∏ g : Fin p.r, Fintype.card (AttainedSignatures.Representative
      (AttainedSignatures.integerKey (fun (j : Fin p.incidences) (i : Fin (selected g).length) =>
        LayoutProducedMatrix.literalNat (ProducedQueryRank.packing p first tail)
          (ProducedQueryRank.owner p) A R t j.val ((selected g).get i))))) ≤
      (2*p.n*ProducedQueryRank.queryHeight q k+1) ^
        ProducedQueryRank.queryLabelRows q k hg first tail := by
  let p := LeafProgram.Query.packingProblem q k hg
  let R := (LeafParametersProgram.produce (q.input k)).R
  let A := Subexp.TailInterval.intervalStart p.r p.Q R
  have hr : 2 ≤ p.r := LeafParametersProgram.produce_r_ge_two _
  have hR : 4 ≤ R := LeafParametersProgram.produce_R_ge_four _
  have hRQ : 4*R ≤ p.Q := hg.2.2.2.2.2.2.2.1
  have hAQ : A ≤ p.Q := by
    have he := Subexp.TailInterval.intervalStart_end_le hr hR hRQ
    dsimp only [A]
    omega
  have hQ : 1 ≤ p.Q := by omega
  have hh : (q.input k).occurrence * LayoutProgram.constraintMassBound p.Q R ≤
      ProducedQueryRank.queryHeight q k := by
    calc
      _ ≤ (q.input k).occurrence * (2*(8*p.Q)^(2*R)) :=
        Nat.mul_le_mul_left _ (LayoutProgram.constraintMassBound_le _ _ hQ)
      _ = _ := by
        change (q.input k).occurrence * (2*(8*(LeafParametersProgram.produce (q.input k)).Q)^(2*R)) = _
        unfold ProducedQueryRank.queryHeight
        dsimp only [R]
        ring
  let selected := fun g : Fin p.r => LeafHeadSetupProgram.selectedHeads p.n
    (ProducedQueryRank.rows p first tail) (ProducedQueryRank.queryLow q) (t.val*p.r+g.val)
  let key := fun g : Fin p.r => AttainedSignatures.integerKey
    (fun (j : Fin p.incidences) (i : Fin (selected g).length) =>
      LayoutProducedMatrix.literalNat (ProducedQueryRank.packing p first tail)
        (ProducedQueryRank.owner p) A R t j.val ((selected g).get i))
  have hk := actual_key_inventory_le_maxRank (r := p.r) (Q := p.Q)
    (D := p.incidences) (n := p.n) (κ := fun _ => Fin p.incidences → ℤ)
    (ProducedQueryRank.packing p first tail)
    (ProducedQueryRank.owner p) A R (q.input k).occurrence
    (ProducedQueryRank.queryHeight q k) hAQ
    (LeafPackingFiberBounds.query_owner_fiber_le q k hg) hh
    (ProducedQueryRank.rows p first tail) (ProducedQueryRank.queryLow q)
    Finset.univ t (Finset.mem_univ t) key (fun _ _ _ => Iff.rfl)
  simpa only [← Nat.card_eq_fintype_card, key, selected, ProducedQueryRank.queryLabelRows,
    ProducedQueryRank.labelRows, p, R, A] using hk

/-- The executed shifted key may be used directly once the actual loader's
full-row kernel identity is applied. The query itself discharges all entry,
height and rank fields; no successful bucket layout is a premise. -/
theorem query_key_inventory_le_labelRows
    (q : LeafQueryFrontend.Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (t : Fin (LeafProgram.Query.packingProblem q k hg).Q) :
    let p := LeafProgram.Query.packingProblem q k hg
    let R := (LeafParametersProgram.produce (q.input k)).R
    let A := Subexp.TailInterval.intervalStart p.r p.Q R
    let selected := fun g : Fin p.r => LeafHeadSetupProgram.selectedHeads p.n
      (ProducedQueryRank.rows p first tail) (ProducedQueryRank.queryLow q) (t.val*p.r+g.val)
    let matrix := fun (g : Fin p.r) (j : Fin p.incidences) (i : Fin (selected g).length) =>
      LayoutProducedMatrix.literalNat (ProducedQueryRank.packing p first tail)
        (ProducedQueryRank.owner p) A R t j.val ((selected g).get i)
    ∀ {κ : Fin p.r → Type*}
      (key : (g : Fin p.r) → Fin (2 ^ (selected g).length) → κ g),
      (∀ g x y, key g x = key g y ↔
        AttainedSignatures.integerKey (matrix g) x =
          AttainedSignatures.integerKey (matrix g) y) →
      (∏ g : Fin p.r, Fintype.card (AttainedSignatures.Representative (key g))) ≤
        (2*p.n*ProducedQueryRank.queryHeight q k+1) ^
          ProducedQueryRank.queryLabelRows q k hg first tail := by
  dsimp only
  intro κ key hkernel
  apply le_trans ?_ (query_inventory_le_labelRows q k hg first tail t)
  apply Finset.prod_le_prod'
  intro g _
  simpa only [Nat.card_eq_fintype_card] using
    (card_representative_kernel (key g) _ (hkernel g)).le

/-- The original explicit record uses the same ambient coefficient-height
base as the actual query rank theorem. This is only a definitional field read. -/
theorem ofPacking_labelBase (q : LeafQueryFrontend.Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)) :
    (ProducedQueryResources.ofPacking q k B C d qi e hg first tail).labelBase =
      2*(LeafProgram.Query.packingProblem q k hg).n*ProducedQueryRank.queryHeight q k+1 := rfl

/-- The same explicit record retains the maximum of actual selected ranks. -/
theorem ofPacking_labelRows (q : LeafQueryFrontend.Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)) :
    (ProducedQueryResources.ofPacking q k B C d qi e hg first tail).labelRows =
      ProducedQueryRank.queryLabelRows q k hg first tail := rfl

/-- A faithful actual emitted-key inventory fits the very same original
resource record that carries the scheduled sqrt-log estimate. No old selector
Origin or successful bucket-layout premise is introduced. -/
theorem query_key_inventory_le_ofPacking
    (q : LeafQueryFrontend.Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (t : Fin (LeafProgram.Query.packingProblem q k hg).Q) :
    let p := LeafProgram.Query.packingProblem q k hg
    let R := (LeafParametersProgram.produce (q.input k)).R
    let A := Subexp.TailInterval.intervalStart p.r p.Q R
    let selected := fun g : ℕ => LeafHeadSetupProgram.selectedHeads p.n
      (ProducedQueryRank.rows p first tail) (ProducedQueryRank.queryLow q) (t.val*p.r+g)
    let matrix := fun (g : Fin p.r) (j : Fin p.incidences)
      (i : Fin (selected g.val).length) =>
      LayoutProducedMatrix.literalNat (ProducedQueryRank.packing p first tail)
        (ProducedQueryRank.owner p) A R t j.val ((selected g.val).get i)
    ∀ {κ : ℕ → Type*}
      (key : (g : ℕ) → Fin (2 ^ (selected g).length) → κ g),
      (∀ (g : Fin p.r) x y, key g.val x = key g.val y ↔
        AttainedSignatures.integerKey (matrix g) x =
          AttainedSignatures.integerKey (matrix g) y) →
      SignatureTupleDFS.prefixCount
        (fun g => Fintype.card (AttainedSignatures.Representative (key g))) p.r ≤
        (ProducedQueryResources.ofPacking q k B C d qi e hg first tail).labelBase ^
          (ProducedQueryResources.ofPacking q k B C d qi e hg first tail).labelRows := by
  dsimp only
  intro κ key hkernel
  rw [ofPacking_labelBase, ofPacking_labelRows]
  unfold SignatureTupleDFS.prefixCount
  rw [← Fin.prod_univ_eq_prod_range]
  exact query_key_inventory_le_labelRows q k hg first tail t (fun g => key g.val) hkernel

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamedQueryMeasuredCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The measured callback pays native mask setup, the complete attained-tuple
run (including ascent), and the signed commit. Its finite-difference iterator
is compared to the original explicit resource record with one fixed power. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost

open OAI SqrtLog SubexpLiftRing SubexpQuarticRing
open SignatureTupleSource SignatureTupleTraversal SignatureTupleDFS
open CostAssembly.Polynomial
open scoped BigOperators

theorem commit_le {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (N A : ℕ)
    (hn : n ≤ A) (hN : N ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hJ : q.J ≤ A) :
    QueryPairEvaluation.commitBudget q N (QueryHeadBudgets.compact A) ≤ commitEnvelope A := by
  have hlocal := TruncatedRingProgram.localBudget_le n (baseWidth 3 q.p.t) d q.p.t q.J 0
  have hscale := TruncatedRingProgram.scalingBudget_le_local n (baseWidth 3 q.p.t) d q.p.t q.J 0
  have hadd := TruncatedRingProgram.additionBudget_le_local n (baseWidth 3 q.p.t) d q.p.t q.J 0
  have hb : TruncatedRingProgram.localBudget n (baseWidth 3 q.p.t) d q.p.t q.J 0 ≤
      3000000*(6*A+1)^10 := by
    apply hlocal.trans
    simp only [RingProgram.ternary_baseWidth]
    gcongr
    omega
  have hbytes : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤
      A*A*(2*(A+A+A)+2*(A*(2*A))+2) := by
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  unfold QueryPairEvaluation.commitBudget QueryProgram.pairUpdateBudget
    QueryProgram.signedAccumulateBudget QueryProgram.signedScalingBudget commitEnvelope
  omega

/-- This is precisely the all-prefix stack bound exported by the actual
pair run, with the same compact cap used at every callback boundary. -/
theorem pair_space_le (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (N A : ℕ)
    (hN : N ≤ s.input.n) (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A)
    (hu : q.u ≤ A) (hJ : q.J ≤ A) (hR : q.p.R = s.input.R)
    (hw : q.p.width = s.input.width) (hp : q.p.power = s.input.power) :
    max (QueryPairEvaluation.callbackSpace s q N (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A)) (896*QueryHeadBudgets.compact A+13) ≤ pairSpaceEnvelope A := by
  have hn := (NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded).n.trans hs
  have hstart : QueryPairEvaluation.startBudget s.input.n (QueryHeadBudgets.compact A) ≤
      QueryPairEvaluation.startBudget A (QueryHeadBudgets.compact A) := by
    unfold QueryPairEvaluation.startBudget
    omega
  have hcommit := commit_le q N A hn (hN.trans hn) hd ht hJ
  have hcomplete := (TupleRunBudgets.run_bounds s q A hs hd ht hu hJ hR hw hp).1
  unfold QueryPairEvaluation.callbackSpace pairSpaceEnvelope coefficient localEnvelope
  exact max_le (max_le (by omega) (by omega)) (by omega)

section Addressed

open MulticolorTypes LeafHeadSetupProgram LeafParametersProgram

variable (front : LeafQueryFrontend.Query) (k B C degree qi exponent : ℕ)
  (guard : LeafParametersProgram.Guard (front.input k))
  (first : Word (LeafProgram.Query.packingProblem front k guard).r
    (LeafProgram.Query.packingProblem front k guard).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem front k guard).r
    (LeafProgram.Query.packingProblem front k guard).Q))
  (node : Fin (LeafProgram.Query.packingProblem front k guard).Q)
  (physical : LeafHeadSetupProgram.Data)
  (ready : Native.Ready (Native.queryInputsAddressed front k guard first tail node) physical)
  (bound : ℕ) (bounded : SubexpSetupStorage.WordBound bound physical)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed front k guard first tail node).height
    (unary (Native.queryInputsAddressed front k guard first tail node).R)
    (Native.queryInputsAddressed front k guard first tail node).width words)

local notation "src" => QueryHeadSourceFacts.addressedSource front k guard first tail node
  physical ready bound bounded ra rd rc words hc
local notation "resources" => ProducedQueryResources.ofPacking front k B C degree qi exponent guard first tail

/-- The actual addressed loader's tuple count uses exactly the original
selected matrices. No key-kernel, rank or successful-layout premise remains. -/
theorem addressed_inventory :
    SignatureTupleRun.tupleCount (src).key (src).input.r ≤
      (resources).labelBase^(resources).labelRows := by
  have hk := StreamedQueryCostBudgets.query_key_inventory_le_ofPacking
    front k B C degree qi exponent guard first tail node (src).key (by
      intro g x y
      change AttainedSignatures.integerKey (fun j i => LayoutProducedMatrix.literalNat
        (ProducedQueryRank.packing (LeafProgram.Query.packingProblem front k guard) first tail)
        (ProducedQueryRank.owner (LeafProgram.Query.packingProblem front k guard))
        (unary (Subexp.TailInterval.intervalStart
          (LeafParametersProgram.produce (front.input k)).r
          (LeafParametersProgram.produce (front.input k)).Q
          (LeafParametersProgram.produce (front.input k)).R)).length
        (LeafParametersProgram.produce (front.input k)).R node j.val
        ((selectedHeads (src).input.n (src).input.rows (src).input.low
          (node.val*(src).input.r+g.val)).get i)) x =
        AttainedSignatures.integerKey (fun j i => LayoutProducedMatrix.literalNat
        (ProducedQueryRank.packing (LeafProgram.Query.packingProblem front k guard) first tail)
        (ProducedQueryRank.owner (LeafProgram.Query.packingProblem front k guard))
        (unary (Subexp.TailInterval.intervalStart
          (LeafParametersProgram.produce (front.input k)).r
          (LeafParametersProgram.produce (front.input k)).Q
          (LeafParametersProgram.produce (front.input k)).R)).length
        (LeafParametersProgram.produce (front.input k)).R node j.val
        ((selectedHeads (src).input.n (src).input.rows (src).input.low
          (node.val*(src).input.r+g.val)).get i)) y ↔ _
      simp only [unary,List.length_replicate]
      rfl)
  unfold SignatureTupleRun.tupleCount
  rw [show (src).input.r = (LeafProgram.Query.packingProblem front k guard).r by rfl]
  exact hk

/-- The exponent is the maximum selected free-head size in the same original
record. Ambient size is used only in its signature-range base. -/
theorem addressed_headSize (depth : ℕ) (hdepth : depth < (src).input.r) :
    (src).headSize depth ≤ (resources).headSize :=
  ProducedQueryResources.selected_length_le front k B C degree qi exponent guard first tail node
    ⟨depth,hdepth⟩

variable (model : Circuit.Model) (padding : Fin 8 → ℕ)
  (model_eq : model = LeafParametersProgram.Execute.guardedModel (front.input k) padding)
variable (positiveT : 0 < (model).val 33) (positiveD : 0 < (model).val 34)
  (modulus : SubexpPreparedQuartic.Modulus 3 ((model).val 33))
  (cache : RingProgram.ScalarCache 3 ((model).val 33))
  (half : RingProgram.ScalarCode 3 ((model).val 33)) (output : LeafRingSetupProgram.Data)
  (produced : LeafRingSetupProgram.Produced model positiveD modulus cache half output)
  (fieldSize : (Native.queryInputsAddressed front k guard first tail node).Q < 3^((model).val 34))
  (valid : front.Valid)
  (positiveJ : 0 < (model).val 42)
  (clauses : List (List (SAT.Literal
    (Fin (Native.queryInputsAddressed front k guard first tail node).n))))
  (encoded : front.clauses = HashInputProgram.Expansion.encodedClauses clauses)

local notation "spec" => QueryReadyConstruction.sourceSpec src model positiveT positiveD
  modulus cache half output produced fieldSize front valid positiveJ clauses encoded

include model_eq valid in
/-- The real guarded parameter bank and authentic factor factory identify
the order in the pair iterator with the order of this original resource record. -/
theorem addressed_order :
    model.val 42 = CostAssembly.jetOrder k (ProducedQueryResources.ambient front) resources := by
  have hm : (front.input k).clauses ≠ 0 := Nat.ne_of_gt guard.2.2.1
  have hQ : (LeafParametersProgram.produce (front.input k)).Q ≠ 0 := by
    have := guard.2.2.2.2.2.2.1
    omega
  exact (congrArg (fun m : Circuit.Model => m.val 42) model_eq).trans
    (((LeafParametersProgram.Execute.guardedModel_public (front.input k) padding 11).trans
    (LeafParametersProgram.Layout.model_jet (front.input k) padding hm hQ)).trans
    (QueryEnvelopeBudgets.produced_order_eq front k B C degree qi exponent guard first tail valid))

include model_eq ready bounded hc positiveT positiveD produced fieldSize valid positiveJ encoded in
/-- The complete measured pair cost for the actual addressed source and
actual produced ring. Every local dimension is read from its bounded scalar
bank, and both exponential factors use the same selected-rank/head record. -/
theorem addressed_pair_cost (A : ℕ) (hbound : bound ≤ A)
    (hbank : ∀ j, (model).val j ≤ A) :
    DifferencePairsProgram.cost
      (QueryPairEvaluation.callbackBudget src spec
        ((src).input.n-(HighMarkedFrontend.highSet front).card)
        (QueryHeadBudgets.compact A) (QueryHeadBudgets.source A)
        (QueryHeadBudgets.arithmetic A) (QueryHeadBudgets.transient A) (resources).headSize)
      ((src).input.n-(HighMarkedFrontend.highSet front).card) (spec).J ≤
      pairCoefficient A*CostAssembly.assembledWork k (ProducedQueryResources.ambient front) resources^2+10 := by
  exact pair_cost_le_assembled src spec k
    ((src).input.n-(HighMarkedFrontend.highSet front).card) (ProducedQueryResources.ambient front)
    A (resources).headSize resources (Nat.sub_le ..) le_rfl hbound
    (hbank 34) (hbank 33) (hbank 33) (hbank 42) rfl rfl rfl
    (addressed_order front k B C degree qi exponent guard first tail model padding model_eq valid)
    (ProducedQueryResources.make_bits_pos ..) (ProducedQueryResources.make_heads_pos ..)
    (addressed_inventory front k B C degree qi exponent guard first tail node physical ready bound bounded
      ra rd rc words hc) le_rfl

include ready bounded hc positiveT positiveD produced fieldSize valid positiveJ encoded in
/-- The same actual addressed source and produced ring have polynomial
all-prefix pair space; the exponential traversal time is never used here. -/
theorem addressed_pair_space (A : ℕ) (hbound : bound ≤ A)
    (hbank : ∀ j, model.val j ≤ A) :
    max (QueryPairEvaluation.callbackSpace src spec
      ((src).input.n-(HighMarkedFrontend.highSet front).card)
      (QueryHeadBudgets.compact A) (QueryHeadBudgets.transient A))
      (896*QueryHeadBudgets.compact A+13) ≤ pairSpaceEnvelope A :=
  pair_space_le src spec _ A (Nat.sub_le ..) hbound
    (hbank 34) (hbank 33) (hbank 33) (hbank 42) rfl rfl rfl

end Addressed

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical boundaries of the fixed conditioned query. The node invariant
retains the actual prepared words and the exact length of the emitted stream;
it contains no execution or evaluator fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open SubexpSetupStorage

section ActualNode
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource LeafHeadSetupProgram
open QueryNodeEvaluation

variable (query : LeafQueryFrontend.Query) (k RB RC RD RI RE : ℕ)
  (hg : Guard (query.input k)) (hv : query.Valid)
  (first : MulticolorTypes.Word (Query.packingProblem query k hg).r
    (Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (Query.packingProblem query k hg).r
    (Query.packingProblem query k hg).Q))
  (node : Fin (Query.packingProblem query k hg).Q)
  (m : Circuit.Model) (padding : Fin 8 → ℕ)
  (hm : m=Execute.guardedModel (query.input k) padding)
  (ht : 0 < m.val 33) (hd : 0 < m.val 34)
  (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
  (cache : RingProgram.ScalarCache 3 (m.val 33))
  (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
  (base out : State 40 768) (ho : Query.ArithmeticOutput base out m hd M cache half e)
  (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3 ^ (m.val 34))
  (hQ : m.val 21=(Native.queryInputsAddressed query k hg first tail node).Q)
  (hR : (base.stacks 740).length=(Native.queryInputsAddressed query k hg first tail node).R)
  (hJ : 0 < m.val 42)
  (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
  (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
local notation "H" => HighMarkedFrontend.highSet query
local notation "resources" => ProducedQueryResources.ofPacking query k RB RC RD RI RE hg first tail
local notation "work" => CostAssembly.assembledWork k (ProducedQueryResources.ambient query) resources
local notation "bits" => RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (node.val+1))

include hm hQ hR in
/-- One actual node executes its preparation, complete pair/tuple traversal
and coefficient readout. Every numerical and semantic source premise is
constructed from the same physical input and actual produced ring. -/
theorem node_run_oai (high : H → Bool) (A : ℕ) (a : State 40 896)
    (remaining : List (List Bool))
    (hbank : NativeLayoutLoad.SourceBank native a)
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
    (hcache : ∀ i∈cacheInputPorts,(a.stacks i).length≤A)
    (hvalues : ∀ i,m.val i≤A)
    (hsources : Query.Sources query (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a))
    (h700 : (a.stacks 700).length≤A) (h701 : (a.stacks 701).length≤A)
    (h708 : (a.stacks 708).length≤A)
    (hcursor : a.stacks 301=Encoding.encodeList id (bits::remaining))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hframe : ∀ i∈QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (h704 : a.stacks 704=List.replicate query.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex query))
    (h706 : a.stacks 706=[query.mark.isSome])
    (h702 : a.stacks 702=List.ofFn
      (fun v : Fin (BinaryArithmetic.toNat query.ambient) => decide (v ∈ H)))
    (h703 : a.stacks 703=List.ofFn
      (fun v : Fin (BinaryArithmetic.toNat query.ambient) =>
        if h : v ∈ H then high ⟨v, h⟩ else false))
    (ha : WordBound (QueryHeadBudgets.compact A) a)
    (hout : (a.stacks 863).length+(m.val 42)*((m.val 34)*baseWidth 3 (m.val 33))≤QueryHeadBudgets.compact A) :
    ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
    ∃ steps z, ∃ codes : List (DensePolynomialProgram.Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
      let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
        hfield query hv (m.val 42) hJ source hsource
      Eval QueryStreamProgram.nodeBody steps a z ∧ codes.length=m.val 42 ∧
      codes.map factor.p.ops.decode=List.ofFn
        (Truncated.ofPolynomial (m.val 42) ((NodeConcrete.specTarget factor H high).comp
          (Polynomial.X+Polynomial.C (factor.p.ops.decode factor.theta)))).coeff ∧
      z.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
      z.stacks 301=Encoding.encodeList id remaining ∧
      z.stacks 307=List.replicate (node.val+1) true ∧
      z.regs 37= !remaining.isEmpty ∧ z.regs 38=true ∧ z.stacks 89=[] ∧
      (∀ i∈framePorts,i≠307 → i≠863 → z.stacks i=a.stacks i) ∧
      WordBound (QueryHeadBudgets.compact A) z ∧
      steps≤nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work ∧
      QueryExecution.PrefixBound QueryStreamProgram.nodeBody (steps+1) a
        (nodeSpace (native).n (m.val 33) (m.val 34) (m.val 42) A) := by
  let F := QueryHeadBudgets.compact A
  let physical := QuerySourceSnapshot.snapshot (sourceSnapshot a bits remaining)
  have ready : Native.Ready native physical := QuerySourceSnapshot.snapshot_ready
    (sourceSnapshot_ready native a bits remaining hbank)
  have bounded : WordBound A physical := QuerySourceSnapshot.snapshot_bound _ A
    (sourceSnapshot_bank_bound native a bits remaining A hbank hparked)
  have hcap : SignatureHeadLoader.bootstrapOutputBound native≤F :=
    QueryNodeSourceBounds.bootstrap_capacity_of_ready native physical A ready bounded
  obtain ⟨ra,rd,rc,words,hc,np,b,hp,hpt,hb,hcommon,hzero,_hpair,h832,h833,h834,h835,
      h301,_h307,h863,hbf,_hready,_hsnap,hmast,haddress,_htrace,_hpref⟩ :=
    prepare_native_run native m ht hd M cache half e base out ho hfield hQ hR query hv hJ
      source hsource H high F a hbank remaining hcursor hmask hframe hdegree
      hsources.formula hsources.rows h704 h705 h706 hsources.modulus hsources.width
      h702 h703 ha hcap
  let src := nodeSource query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc
  let factor := QueryReadyConstruction.sourceSpec src m ht hd M cache half e ho.produced
    hfield query hv hJ source hsource
  have common : QueryReadyConstruction.CommonReady factor node H high A b :=
    prepared_common_cache_bound hcommon hbf hbank.ambient hcache
  have caps := QueryNodeSourceBounds.headBounds query k hg first tail node a bits remaining A
    hbank hparked ra rd rc words hc m ht hd M cache half e ho.produced hfield hv hJ
    source hsource hvalues hsources h700 h701 h708
  have cap := QueryNodeSourceBounds.retainedCap query k hg first tail node a bits remaining A
    hbank hparked ra rd rc words hc
  have hheads : ∀ depth<(native).r,src.headSize depth≤(resources).headSize := by
    intro depth hdepth
    exact StreamedQueryMeasuredCost.addressed_headSize query k RB RC RD RI RE hg first tail node
      physical ready A bounded ra rd rc words hc depth hdepth
  have hnodeCap := QueryNodeSourceBounds.node_capacity query k hg first tail node a bits remaining A
    hbank hparked ra rd rc words hc m ht hd M cache half e ho.produced hfield hv hJ
    source hsource hvalues
  have hnext : node.val+1≤F := by
    have hn : node.val<(native).Q := node.isLt
    have hq : (native).Q≤F := hnodeCap.2
    omega
  have hcurrentMask : b.stacks 338=HighIncidenceProgram.descendingHighMask H :=
    (hbf 338 (by decide)).trans hmask
  have hremaining : (b.stacks 863).length+(m.val 42)*((m.val 34)*baseWidth 3 (m.val 33))≤F := by
    rw [h863]
    exact hout
  obtain ⟨steps,z,codes,he,hlen,hvalue,happend,h301',h307',hguard,hpeek,hscratch,
      hfinalFrame,hfinal,hcost,_ht,hs⟩ :=
    nodeSource_run query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc
      m ht hd M cache half e ho.produced hfield hv hJ source hsource high F
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A) (QueryHeadBudgets.transient A)
      A (resources).headSize caps cap hheads b np hp ha hb common hzero hmast hbf
      hcurrentMask haddress h832 h833 h834 h835 h301 hremaining hnext
  have pairCost := StreamedQueryMeasuredCost.addressed_pair_cost query k RB RC RD RI RE hg
    first tail node physical ready A bounded ra rd rc words hc m padding hm ht hd M cache half e
    ho.produced hfield hv hJ source hsource A (Nat.le_refl A) hvalues
  have pairSpace := StreamedQueryMeasuredCost.addressed_pair_space query k hg first tail node
    physical ready A bounded ra rd rc words hc m ht hd M cache half e ho.produced hfield hv hJ
    source hsource A (Nat.le_refl A) hvalues
  change DifferencePairsProgram.cost
    (QueryPairEvaluation.callbackBudget src factor ((native).n-(H).card) F
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) (resources).headSize)
    ((native).n-(H).card) factor.J ≤
      StreamedQueryMeasuredCost.pairCoefficient A*work^2+10 at pairCost
  refine ⟨words,hc,steps,z,codes,he,hlen,hvalue,happend,h301',h307',hguard,hpeek,hscratch,
    hfinalFrame,hfinal,?_,?_⟩
  · change steps≤prepareBudget A+StreamedQueryMeasuredCost.pairCoefficient A*work^2+10+
      finishBudget (native).n (m.val 33) (m.val 34) (m.val 42) A
    change np≤prepareBudget A at hpt
    change steps≤np+DifferencePairsProgram.cost
      (QueryPairEvaluation.callbackBudget src factor ((native).n-(H).card) F
        (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
        (QueryHeadBudgets.transient A) (resources).headSize)
      ((native).n-(H).card) factor.J+
      finishBudget (native).n (m.val 33) (m.val 34) (m.val 42) A at hcost
    omega
  · apply hs.mono
    exact max_le_max pairSpace (by
      change 896*F+np+finishBudget (native).n (m.val 33) (m.val 34) (m.val 42) A+1≤_
      change np≤prepareBudget A at hpt
      omega)


end ActualNode

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.node_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.node_run_oai
