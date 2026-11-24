-- Prove2me | solution 1 for GlobalTheory.basisVal_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:14.825766+00:00
-- url     : https://prove2.me/submissions/a2f93819-884b-4344-bb31-d730333dc26f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_le_basisVal
import Theorems.Thm_GlobalTheory_basisVal_add_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open Module
variable {R Γ₀ ι κ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation R Γ₀) {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
  {O : Type*} [CommRing O] [Algebra O R] [Module O M] [IsScalarTower O R M]
namespace GlobalTheory
theorem _root_.solution (hO : v.Integers O) {x : M} :
    basisVal v b x ≤ 1 ↔ x ∈ Submodule.span O (Set.range b) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := hO.exists_of_le_one ((le_basisVal v b x i).trans h)
    simp_rw [← ha, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · induction h using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; simp
    | zero => simp
    | add y z _ _ hy hz => exact (basisVal_add_le v b y z).trans (max_le hy hz)
    | smul a y _ hy =>
      rw [← algebraMap_smul R a y, basisVal_smul]
      exact mul_le_one' (hO.map_le_one a) hy
end GlobalTheory
