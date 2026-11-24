-- Prove2me | solution 1 for GlobalTheory.UnRep.ReflStep.exists_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:58:58.943948+00:00
-- url     : https://prove2.me/submissions/e26592f8-d737-4c8a-92a9-0ae9d0bc7abc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEq
import Theorems.Thm_GlobalTheory_UnRep_ReflStep_herm_sub_smul_left
import Theorems.Thm_GlobalTheory_UnRep_ReflStep_herm_sub_smul_right
import Theorems.Thm_GlobalTheory_UnRep_ReflStep_herm_conj
import Theorems.Thm_GlobalTheory_UnRep_ReflStep_refl_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.ReflStep
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.UnRep.ReflStep
theorem _root_.solution (h : IsHermForm c G) (x z : Fin n → E) (hz : hermE c G z z = hermE c G x x) (e : E)
    (he : c e = e) (he2 : e * e = 1) (hy : hermE c G (z - e • x) (z - e • x) ≠ 0) :
    ∃ u : E, u * c u = 1 ∧ refl c G (z - e • x) u *ᵥ z = e • x := by
  obtain ⟨a, ha⟩ : ∃ a, a = hermE c G z (z - e • x) := ⟨_, rfl⟩
  have hyy : hermE c G (z - e • x) (z - e • x) = a + c a := by
    rw [ha, herm_conj c G h, herm_sub_smul_left c G z x (z - e • x), herm_sub_smul_left c G z x z,
      herm_sub_smul_right c G z x x, he, hz]
    linear_combination (hermE c G x x) * he2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hy (by simpa using hyy)
  have hca : c a ≠ 0 := by simpa using ha0
  refine ⟨-c a / a, ?_, ?_⟩
  · rw [map_div₀, map_neg, h.1]
    field_simp
  · rw [refl_mulVec, ← ha]
    have : (-c a / a - 1) * a / hermE c G (z - e • x) (z - e • x) = -1 := by
      rw [div_eq_iff hy, hyy]
      field_simp
      ring
    rw [this]
    simp
end GlobalTheory.UnRep.ReflStep
