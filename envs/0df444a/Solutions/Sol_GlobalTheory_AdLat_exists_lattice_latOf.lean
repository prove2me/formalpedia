-- Prove2me | solution 1 for GlobalTheory.AdLat.exists_lattice_latOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:03.667108+00:00
-- url     : https://prove2.me/submissions/752b6a74-ec60-4a93-a808-1cbd61a225a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Theorems.Thm_GlobalTheory_AdLat_Translate_fv_nsmul
import Theorems.Thm_GlobalTheory_AdLat_Translate_fv_mem_hat
import Theorems.Thm_GlobalTheory_AdLat_Translate_mem_pre
import Theorems.Thm_GlobalTheory_AdLat_Translate_mulVec_mem_hat
import Theorems.Thm_GlobalTheory_AdLat_Translate_exists_bound
import Theorems.Thm_GlobalTheory_AdLat_Translate_nsmul_mem_hat
import Theorems.Thm_GlobalTheory_AdLat_Translate_nsmul_cancel
import Theorems.Thm_GlobalTheory_AdLat_hat_rational_points_and_approx
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory.AdLat.Translate
namespace GlobalTheory.AdLat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∃ Λ : Submodule (𝓞 E) (Fin n → E), (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L ∧ Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧ (hat F (Λ : Set (Fin n → E)) : Set (Fin n → RA F E)) = (g : Matrix (Fin n) (Fin n) (RA F E)).mulVec '' (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L g hL hspan
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hL hspan
  set G : Matrix (Fin n) (Fin n) (RA F E) := (g : Matrix (Fin n) (Fin n) (RA F E)) with hG
  set H : Matrix (Fin n) (Fin n) (RA F E) := ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E))
    with hH
  have hGH : ∀ z, G.mulVec (H.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hG, hH, Units.mul_inv, Matrix.one_mulVec]
  have hHG : ∀ z, H.mulVec (G.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hG, hH, Units.inv_mul, Matrix.one_mulVec]
  have him : ∀ z, z ∈ G.mulVec '' (hat F (L : Set (Fin n → E)) : Set (Fin n → RA F E)) ↔
      H.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩; rw [hHG]; exact hu
    · intro h; exact ⟨_, h, hGH z⟩
  obtain ⟨d, hd, hdG⟩ := exists_bound G hL h4
  obtain ⟨e, he, heH⟩ := exists_bound H hL h4
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have he' : (e : E) ≠ 0 := by exact_mod_cast he.ne'
  have hlow : ∀ x ∈ L, e • x ∈ pre H L := by
    intro x hx
    rw [mem_pre, fv_nsmul, Matrix.mulVec_smul]
    exact heH _ (fv_mem_hat hx)
  have hup : ∀ x ∈ pre H L, d • x ∈ L := by
    intro x hx
    rw [← h1, fv_nsmul, ← hGH (fv F x)]
    exact hdG _ hx
  refine ⟨pre H L, ?_, ?_, ?_, ?_⟩
  · ext v
    exact (him _).symm
  · have hinj : Function.Injective (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) := by
      intro x y hxy
      simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
      rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at hxy
      exact smul_right_injective _ hd' hxy
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have hle : (pre H L).map (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) ≤ L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hup x hx
    have : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian _ hL
    exact (isNoetherian_submodule.1 this) _ hle
  · rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro x hx
    have hx' : x = (e : E)⁻¹ • (e • x) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ he', one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hlow x hx))
  · ext z
    rw [him]
    constructor
    · intro hz
      exact mulVec_mem_hat subset_rfl hz
    · intro hz
      have hdz : d • z ∈ hat F (L : Set (Fin n → E)) := by
        rw [← hGH z]; exact hdG _ hz
      obtain ⟨x, -, w, hw, hxw⟩ := h2 (d * e) (Nat.mul_pos hd he) _ hdz
      have hx' : x = d • ((d : E)⁻¹ • x) := by
        rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hd', one_smul]
      have hz' : z = fv F ((d : E)⁻¹ • x) + e • w := by
        apply nsmul_cancel hd
        rw [smul_add, ← fv_nsmul, ← hx', smul_smul, hxw]
      have hy : (d : E)⁻¹ • x ∈ pre H L := by
        rw [mem_pre, eq_sub_of_add_eq hz'.symm, Matrix.mulVec_sub, Matrix.mulVec_smul]
        exact sub_mem hz (heH _ hw)
      rw [hz']
      exact add_mem (fv_mem_hat hy) (nsmul_mem_hat hlow hw)
end GlobalTheory.AdLat
