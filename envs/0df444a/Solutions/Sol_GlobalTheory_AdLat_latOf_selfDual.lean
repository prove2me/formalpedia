-- Prove2me | solution 1 for GlobalTheory.AdLat.latOf_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:14.400784+00:00
-- url     : https://prove2.me/submissions/09d8b0ad-2ea0-45de-8b67-ec894e458724

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicHermitianFormGaloisMemOfMemCompletion
import Theorems.Thm_GlobalTheory_AdLat_hermA_fv_fv
import Theorems.Thm_GlobalTheory_AdLat_adelicHermitianFormGalois_mem_of_mem_completion
import Theorems.Thm_GlobalTheory_AdLat_adele_one_integral
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletion_fractionalIdeal_iff
import Theorems.Thm_GlobalTheory_T_adelicCompletion_selfDual_of_selfDual_lattice
import Theorems.Thm_GlobalTheory_T_exists_lattice_rationalVectorsInAdelicTranslate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
namespace GlobalTheory.AdLat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E) (g : GL (Fin n) (RA F E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) → G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) → (∀ x y, hermA c G ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ x) ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ y) = hermA c G x y) → ∀ v : Fin n → E, (∀ y ∈ latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L := by
  intro F E _ _ _ _ _ n L c G J g hfg hspan hc hG hdet hJ hL hg v
  have hd := GlobalTheory.T.adelicCompletion_selfDual_of_selfDual_lattice F E n L c G J hfg hspan hc hG hdet hJ hL
  obtain ⟨Λ, hΛ, -, -, hhat⟩ := GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate F E n L g hfg hspan
  constructor
  · intro hv
    have hz : (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ
        (((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ fv F v) = fv F v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨_, (hd _).1 fun y hy => ?_, hz⟩
    rw [← hg, hz]
    refine adelicHermitianFormGalois_mem_of_mem_completion c G (S := (Λ : Set (Fin n → E))) (fun y' hy' => ?_) ?_
    · rw [hermA_fv_fv]
      exact one_tmul_mem_adelicCompletionOfElementSet F (hv y' (hΛ ▸ hy'))
    · have : (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ fv F y ∈
          (hat F (Λ : Set (Fin n → E)) : Set (Fin n → RA F E)) := by
        rw [hhat]
        exact ⟨fv F y, AddSubgroup.subset_closure ⟨1, adele_one_integral F, y, hy, rfl⟩, rfl⟩
      exact this
  · rintro ⟨z, hz, hzv⟩ y ⟨w, hw, hwy⟩
    rw [← one_tmul_mem_adelicCompletion_fractionalIdeal_iff F, ← hermA_fv_fv, ← hzv, ← hwy, hg]
    exact adelicHermitianFormGalois_mem_of_mem_completion c G ((hd z).2 hz) hw
end GlobalTheory.AdLat
