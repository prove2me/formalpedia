-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.ldDnoteq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:44:31.693822+00:00
-- url     : https://prove2.me/submissions/84fd16b1-36cd-46f9-842d-05cb3d81178c

-- Generated proof for MIPStarRE.LDT.Pasting.ldDnoteq.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_PMF_totalVariationDistance_uniformOfFintype_uniformOfFinset_eq

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Basic/Distribution.lean. -/
/-!
# Distribution infrastructure for the low individual degree test

Shared distribution definitions: finite-support weighted distributions,
a probability predicate, push-forward distributions, weighted-sum linear maps,
averaging, uniform distribution, and outcome summation.

Note: this module contributes declarations to the comparator statement closure
of `mainFormal`, which must elaborate in the same environment as the
Mathlib-only `Challenge.lean`.  Keep the full `import Mathlib`; do not narrow
it.  See `docs/comparator.md`, "Environment alignment".
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT



namespace Distribution















end Distribution



namespace Distribution.IsProbability









end Distribution.IsProbability

namespace Distribution











end Distribution



namespace Distribution









end Distribution



namespace Distribution





end Distribution



















namespace Distribution













end Distribution















/-- On a finite ambient type, the local total-variation distance may be summed
over all points rather than over the union of the stored supports. -/
theorem totalVariationDistance_eq_univ_sum {α : Type*} [Fintype α] [DecidableEq α]
    (μ ν : Distribution α) :
    totalVariationDistance μ ν =
      (1 / 2) * ∑ a : α, |μ.weight a - ν.weight a| := by
  unfold totalVariationDistance
  congr 1
  exact Finset.sum_subset (Finset.subset_univ (μ.support ∪ ν.support)) (fun a _ ha => by
    have hμ : a ∉ μ.support := fun h => ha (Finset.mem_union_left ν.support h)
    have hν : a ∉ ν.support := fun h => ha (Finset.mem_union_right μ.support h)
    rw [μ.outsideSupport a hμ, ν.outsideSupport a hν, sub_self, abs_zero])

/-- For probability distributions on a finite ambient type, the local
total-variation distance is the half `L^1` distance between the associated
Mathlib probability mass functions. -/
theorem totalVariationDistance_eq_toPMF_sum {α : Type*} [Fintype α] [DecidableEq α]
    (μ ν : Distribution α) (hμ : μ.IsProbability) (hν : ν.IsProbability) :
    totalVariationDistance μ ν =
      (1 / 2) * ∑ a : α, |(μ.toPMF hμ a).toReal - (ν.toPMF hν a).toReal| := by
  rw [totalVariationDistance_eq_univ_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Distribution.toPMF_apply_toReal, Distribution.toPMF_apply_toReal]

end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Pasting/Defs/Tuples.lean. -/
/-!
# Section 12 — Definitions: tuples and operators

Tuple distributions, type abbreviations, and basic operator helpers.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







/-- The number of injective `k`-tuples is the falling factorial `q(q-1) ... (q-k+1)`. -/
theorem distinctTupleSupport_card (params : Parameters) (k : ℕ) :
    (distinctTupleSupport params k).card = params.q.descFactorial k := by
  classical
  rw [← Fintype.card_coe]
  let e : { xs : PointTuple params k // Function.Injective xs } ≃ (Fin k ↪ Fq params) :=
    Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fq params)
  simpa [distinctTupleSupport, Finset.mem_filter] using
    (Fintype.card_congr e).trans Fintype.card_embedding_eq

/-- If `k ≤ q`, there exists an injective `k`-tuple. -/
theorem distinctTupleSupport_nonempty_of_le
    (params : Parameters) (k : ℕ) (hk : k ≤ params.q) :
    (distinctTupleSupport params k).Nonempty := by
  classical
  refine ⟨fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩, ?_⟩
  refine Finset.mem_filter.mpr ?_
  constructor
  · simp
  · intro i j hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)

/-- If `q < k`, no injective `k`-tuple of field elements exists. -/
theorem distinctTupleSupport_eq_empty_of_lt
    (params : Parameters) (k : ℕ) (hk : params.q < k) :
    distinctTupleSupport params k = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [distinctTupleSupport_card]
  exact Nat.descFactorial_eq_zero_iff_lt.mpr hk























































end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Basic/DistributionUniform.lean. -/
/-!
# Uniform subset estimates

This file contains estimates for the total variation distance between the
uniform distribution on a finite type and the uniform distribution on a
nonempty finite subset, together with averaging bounds for `[0,1]`-valued
functions.  The uniform-subset total-variation identity is proved by transport
through Mathlib probability mass functions.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

/-- Total variation between the uniform distribution on a finite ambient type and
the uniform distribution on a nonempty finite subset.

This is the elementary finite identity
`TV(uniform α, uniform s) = 1 - |s| / |α|`.  The proof transports the project
`Distribution` statement to Mathlib's uniform probability mass functions. -/
theorem totalVariationDistance_uniformDistribution_uniformOnFinset_eq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty) :
    totalVariationDistance (uniformDistribution α) (Distribution.uniformOnFinset s) =
      1 - (s.card : Error) / (Fintype.card α : Error) := by
  rw [totalVariationDistance_eq_toPMF_sum]
  change PMF.totalVariationDistance
      ((uniformDistribution α).toPMF (uniformDistribution_isProbability α))
      ((Distribution.uniformOnFinset s).toPMF
        (Distribution.uniformOnFinset_isProbability s hs)) =
    1 - (s.card : Error) / (Fintype.card α : Error)
  rw [uniformDistribution_toPMF, Distribution.uniformOnFinset_toPMF]
  exact PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq s hs



end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Section 12 pasting: distinct tuple distribution bound

The total variation distance between the uniform distribution on all point tuples
and the distribution restricted to distinct tuples.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) (k : ℕ) :
    _root_.LIDT.MIPStarRE.LDT.totalVariationDistance (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k))
        (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k)
      ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := by
  classical
  let support : Finset (_root_.LIDT.MIPStarRE.LDT.PointTuple params k) :=
    _root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleSupport params k
  have hsupport_card : support.card = params.q.descFactorial k := by
    simpa [support] using _root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleSupport_card params k
  have hq_ne : (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hq)
  by_cases hk : k ≤ params.q
  · have hsupport_nonempty : support.Nonempty := by
      simpa [support] using _root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleSupport_nonempty_of_le params k hk
    have htv_eq :
        _root_.LIDT.MIPStarRE.LDT.totalVariationDistance (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k)
          = 1 - (support.card : _root_.LIDT.MIPStarRE.LDT.Error) / ((params.q : _root_.LIDT.MIPStarRE.LDT.Error) ^ k) := by
      have htv :=
        _root_.LIDT.MIPStarRE.LDT.totalVariationDistance_uniformDistribution_uniformOnFinset_eq
          (s := support) hsupport_nonempty
      simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution, support, _root_.LIDT.MIPStarRE.LDT.PointTuple, Fintype.card_fun,
        Fintype.card_fin] using htv
    have hratio_prod :
        (support.card : _root_.LIDT.MIPStarRE.LDT.Error) / ((params.q : _root_.LIDT.MIPStarRE.LDT.Error) ^ k)
          = ∏ i ∈ Finset.range k, (((params.q - i : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / params.q) := by
      rw [hsupport_card, Nat.descFactorial_eq_prod_range]
      rw [show ((∏ i ∈ Finset.range k, (params.q - i) : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error)
          = ∏ i ∈ Finset.range k, ((params.q - i : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) by
            rw [Finset.prod_natCast]]
      simp_rw [div_eq_mul_inv]
      rw [Finset.prod_mul_distrib]
      simp
    have hfactor :
        ∀ i ∈ Finset.range k,
          (((params.q - i : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / params.q) = 1 - (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q := by
      intro i hi
      have hi_le : i ≤ params.q := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hk
      rw [Nat.cast_sub hi_le]
      field_simp [hq_ne]
    have hfactor_nonneg :
        ∀ i ∈ Finset.range k, 0 ≤ 1 - (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q := by
      intro i hi
      have hi_le : (i : _root_.LIDT.MIPStarRE.LDT.Error) ≤ params.q := by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hk
      have hq_pos : 0 < (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := by positivity
      have hdiv_le_one : (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q ≤ 1 := by
        have hfrac_le : (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q ≤ (params.q : _root_.LIDT.MIPStarRE.LDT.Error) / params.q := by
          exact div_le_div_of_nonneg_right hi_le (by positivity)
        have hqq : (params.q : _root_.LIDT.MIPStarRE.LDT.Error) / params.q = 1 := by
          field_simp [hq_ne]
        rw [hqq] at hfrac_le
        exact hfrac_le
      nlinarith
    have hfactor_le_one :
        ∀ i ∈ Finset.range k, 1 - (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q ≤ 1 := by
      intro i hi
      exact sub_le_self _ (by positivity)
    have hprefix_le_one :
        ∀ i ∈ Finset.range k,
          ∏ j ∈ Finset.range k with j < i, (1 - (j : _root_.LIDT.MIPStarRE.LDT.Error) / params.q) ≤ 1 := by
      intro i hi
      calc
        ∏ j ∈ Finset.range k with j < i, (1 - (j : _root_.LIDT.MIPStarRE.LDT.Error) / params.q)
          ≤ ∏ j ∈ Finset.range k with j < i, (1 : _root_.LIDT.MIPStarRE.LDT.Error) := by
              exact Finset.prod_le_prod
                (fun j hj => hfactor_nonneg j (Finset.mem_filter.mp hj).1)
                (fun j hj => hfactor_le_one j (Finset.mem_filter.mp hj).1)
        _ = 1 := by simp
    have hsum_le :
        ∑ i ∈ Finset.range k,
          ((i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q)
            * ∏ j ∈ Finset.range k with j < i, (1 - (j : _root_.LIDT.MIPStarRE.LDT.Error) / params.q)
          ≤ ∑ i ∈ Finset.range k, (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi_nonneg : 0 ≤ (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q := by positivity
      have hprefix_nonneg :
          0 ≤ ∏ j ∈ Finset.range k with j < i, (1 - (j : _root_.LIDT.MIPStarRE.LDT.Error) / params.q) := by
        exact Finset.prod_nonneg fun j hj => hfactor_nonneg j (Finset.mem_filter.mp hj).1
      calc
        ((i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q)
            * ∏ j ∈ Finset.range k with j < i, (1 - (j : _root_.LIDT.MIPStarRE.LDT.Error) / params.q)
          ≤ ((i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q) * 1 := by
              exact mul_le_mul_of_nonneg_left (hprefix_le_one i hi) hi_nonneg
        _ = (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q := by ring
    have hcollision_le :
        1 - ∏ i ∈ Finset.range k, (1 - (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q)
          ≤ ∑ i ∈ Finset.range k, (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q := by
      have hprod_expand :=
        (Finset.prod_one_sub_ordered (s := Finset.range k)
          (f := fun i => (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q))
      rw [hprod_expand]
      nlinarith
    have hsum_id :
        ∑ i ∈ Finset.range k, (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q
          = (((k * (k - 1) / 2 : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / params.q) := by
      calc
        ∑ i ∈ Finset.range k, (i : _root_.LIDT.MIPStarRE.LDT.Error) / params.q
          = (∑ i ∈ Finset.range k, (i : _root_.LIDT.MIPStarRE.LDT.Error)) / params.q := by
              simp [div_eq_mul_inv, Finset.sum_mul]
        _ = (((k * (k - 1) / 2 : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / params.q) := by
              rw [← Nat.cast_sum]
              simp [Finset.sum_range_id]
    have hsum_sq :
        (((k * (k - 1) / 2 : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / params.q)
          ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / params.q := by
      have hnat : k * (k - 1) / 2 ≤ k * k := by
        refine le_trans (Nat.div_le_self _ _) ?_
        exact Nat.mul_le_mul_left k (Nat.sub_le _ _)
      have hcast : (((k * (k - 1) / 2 : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error)) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) * k := by
        exact_mod_cast hnat
      simpa [pow_two] using div_le_div_of_nonneg_right hcast (by positivity)
    rw [htv_eq]
    rw [hratio_prod]
    rw [Finset.prod_congr rfl hfactor]
    exact le_trans hcollision_le (by simpa [hsum_id] using hsum_sq)
  · have hkq : params.q < k := lt_of_not_ge hk
    have hsupport_empty : support = ∅ := by
      simpa [support] using _root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleSupport_eq_empty_of_lt params k hkq
    have htv_eq_half :
        _root_.LIDT.MIPStarRE.LDT.totalVariationDistance (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.PointTuple params k))
            (_root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution params k)
          = 1 / 2 := by
      rw [_root_.LIDT.MIPStarRE.LDT.totalVariationDistance]
      simp [_root_.LIDT.MIPStarRE.LDT.uniformDistribution, _root_.LIDT.MIPStarRE.LDT.Pasting.distinctTupleDistribution, support, hsupport_empty]
    have hbound_ge_one : 1 ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := by
      have hk_pos_nat : 0 < k := lt_trans params.hq hkq
      have hk_ge_q : (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤ k := by exact_mod_cast hkq.le
      have hk_sq_ge_q : (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ) := by
        have hk_sq_ge_k : (k : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ) := by
          have hk_one : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ k := by exact_mod_cast hk_pos_nat
          nlinarith
        exact le_trans hk_ge_q hk_sq_ge_k
      calc
        1 = (params.q : _root_.LIDT.MIPStarRE.LDT.Error) / params.q := by
              field_simp [hq_ne]
        _ ≤ ((k : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)) / params.q := by
              exact div_le_div_of_nonneg_right hk_sq_ge_q (by positivity)
    rw [htv_eq_half]
    nlinarith [hbound_ge_one]
