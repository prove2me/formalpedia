-- Prove2me | solution 1 for GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:48:46.843698+00:00
-- url     : https://prove2.me/submissions/69644af3-8de8-4692-b407-fc640049ef13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_exists_complete_isAlgClosed_isometry
import Theorems.Thm_GlobalTheory_exists_absoluteValue_of_isDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution (V : Type*) (K : Type u)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {a : V} (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ (C : Type u) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C)
      (_ : IsAlgClosed C) (_ : Algebra K C),
      (∀ x : K, ‖algebraMap K C x‖ ≤ 1 ↔ x ∈ (algebraMap V K).range) ∧
        ‖algebraMap K C (algebraMap V K a)‖ = r := by
  obtain ⟨w, hw, hw1, hwa⟩ := exists_absoluteValue_of_isDiscreteValuationRing V K ha0 ha hr0 hr1
  letI : NontriviallyNormedField (WithAbs w) :=
    { (inferInstance : NormedField (WithAbs w)) with
      non_trivial := ⟨(WithAbs.toAbs w (algebraMap V K a))⁻¹, by
        rw [norm_inv]
        change 1 < (w (algebraMap V K a))⁻¹
        rw [hwa]
        exact (one_lt_inv₀ hr0).2 hr1⟩ }
  haveI : IsUltrametricDist (WithAbs w) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => hw x.ofAbs y.ofAbs
  obtain ⟨C, _, _, _, _, i, hi⟩ := exists_complete_isAlgClosed_isometry (WithAbs w)
  letI : Algebra K C := (i.comp (WithAbs.equiv w).symm.toRingHom).toAlgebra
  have hn : ∀ x : K, ‖algebraMap K C x‖ = w x := fun x => hi _
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun x => by rw [hn, hw1], by rw [hn, hwa]⟩
end GlobalTheory
