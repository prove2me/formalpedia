-- Prove2me | solution 2 for OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:23:54.70729+00:00
-- url     : https://prove2.me/submissions/3c7745a3-8145-4fe1-9311-c569890b0b31

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/Main.lean:L46-L67
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_MetricEntropyDuality_exists_entropy_duality_counterexample_with_covers) verbatim and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
import Definitions.Def_OAI_Analysis_MetricEntropy_ProfileMixtures
import Definitions.Def_OAI_Analysis_MetricEntropy_LabelEncoding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionCode
import Definitions.Def_OAI_Analysis_MetricEntropy_WeightRounding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionDecoder
import Definitions.Def_OAI_Analysis_MetricEntropy_GroupedWeights
import Definitions.Def_OAI_Analysis_MetricEntropy_SignedCompression
import Theorems.Thm_OAI_MetricEntropyDuality_exists_entropy_pair_with_budget

-- ---- from OAI.Analysis.MetricEntropy.Parameters ----
namespace OAI

/-!
# Parameters fixed before the prime is chosen

These are the literal accuracy, pivot-slot, direction-count and encoding-cost
parameters of the construction. The radius and rank are genuinely available
for every proposed comparison constant. Their existence does not depend on
the eventual field size.
-/

noncomputable section

namespace MetricEntropyDuality

theorem compressionRadius_pos (a : ℝ) : 0 < compressionRadius a :=
  Nat.succ_pos _

/-- The rank can be chosen after the compression parameters and before the prime. -/
theorem exists_rank (b θ : ℝ) {h : ℕ} (hh : 0 < h) :
    ∃ r : ℕ, 0 < r ∧
      8 * b * (h : ℝ) ^ 2 * (pivotSlots θ : ℝ) < (r : ℝ) + h - 1 := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max 0 (8 * b * (h : ℝ) ^ 2 * (pivotSlots θ : ℝ)))
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hrbound := lt_of_le_of_lt (le_max_right _ _) hr
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Nat.succ_le_of_lt hh)
  refine ⟨r, Nat.cast_pos.mp hr0, ?_⟩
  linarith

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.Main ----
namespace OAI

/-!
# Counterexamples to metric-entropy duality

The construction supplies actual finite-dimensional bodies and
their least covering numbers from only the numerical parameters. The public
statements retain arbitrary ambient translation centers and the literal polar.
-/

noncomputable section

namespace MetricEntropyDuality

open Filter Topology
open scoped Pointwise

private theorem entropyBudget_lt_of_rank {a b : ℝ} {r : ℕ}
    (hb : 1 ≤ b)
    (hrank : 8 * b * (compressionRadius a : ℝ) ^ 2 *
      (pivotSlots (accuracy a) : ℝ) <
        (r : ℝ) + (compressionRadius a : ℝ) - 1) :
    entropyBudget a r (8 * b) < 1 / (2 * b) := by
  have hb0 : 0 < b := by linarith only [hb]
  have hden : 0 < (r : ℝ) + (compressionRadius a : ℝ) - 1 :=
    lt_of_le_of_lt (by positivity) hrank
  have hfirst : 2 * (compressionRadius a : ℝ) ^ 2 *
      (pivotSlots (accuracy a) : ℝ) /
        ((r : ℝ) + (compressionRadius a : ℝ) - 1) < 1 / (4 * b) := by
    apply (div_lt_div_iff₀ hden (by positivity)).mpr
    nlinarith only [hrank]
  calc
    entropyBudget a r (8 * b) < 1 / (4 * b) + 2 / (8 * b) :=
      add_lt_add_of_lt_of_le hfirst (le_refl _)
    _ = 1 / (2 * b) := by field_simp [ne_of_gt hb0]; ring

/-- The strict counterexample together with actual finite-cover witnesses on
both sides. Thus no empty-infimum convention is used for these numbers. -/
theorem exists_entropy_duality_counterexample_with_covers
    (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ n : ℕ, 0 < n ∧ ∃ K : Set (RealSpace (Fin n)),
      IsSymmetricConvexBody K ∧
      Coverable K (cube (Fin n)) ∧
      Coverable (polar (cube (Fin n))) (a⁻¹ • polar K) ∧
      b * Real.log (coveringNumber (polar (cube (Fin n))) (a⁻¹ • polar K) : ℝ) <
        Real.log (coveringNumber K (cube (Fin n)) : ℝ) := by
  obtain ⟨r, hr, hrank⟩ := exists_rank b (accuracy a) (compressionRadius_pos a)
  have hb0 : 0 < b := by linarith only [hb]
  let P : EntropyPair a r (8 * b) := Classical.choice
    (exists_entropy_pair_with_budget a ha r (Nat.succ_le_of_lt hr)
      (8 * b) (by positivity))
  refine ⟨P.dimension, P.dimension_pos, P.body, P.body_isSymmetricConvexBody,
    P.primal_coverable, P.dual_coverable, ?_⟩
  have hratio : entropyRatio a P.body < 1 / (2 * b) :=
    P.ratio_lt.trans (entropyBudget_lt_of_rank hb hrank)
  have hcross := (div_lt_div_iff₀ P.primal_log_pos
    (by positivity : 0 < 2 * b)).mp hratio
  nlinarith only [hcross, P.primal_log_pos]

end MetricEntropyDuality

end

end OAI

-- ---- mission target ----
open OAI OAI.MetricEntropyDuality
universe u
open Filter Topology
open scoped BigOperators Pointwise
open scoped Pointwise

namespace OAI
namespace MetricEntropyDuality
theorem _root_.solution
    (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ n : ℕ, 0 < n ∧ ∃ K : Set (RealSpace (Fin n)),
      IsSymmetricConvexBody K ∧
      Coverable K (cube (Fin n)) ∧
      Coverable (polar (cube (Fin n))) (a⁻¹ • polar K) ∧
      b * Real.log (coveringNumber (polar (cube (Fin n))) (a⁻¹ • polar K) : ℝ) <
        Real.log (coveringNumber K (cube (Fin n)) : ℝ) := by
  first
    | exact OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers a b ha hb
    | exact OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers
    | (apply OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers <;> assumption)
    | (intros; apply OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers <;> assumption)
end MetricEntropyDuality
end OAI
