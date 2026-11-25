-- Prove2me | solution 1 for GlobalTheory.NonzeroDeterminantIntegrality.integral_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:08:07.825945+00:00
-- url     : https://prove2.me/submissions/a51e1695-d7ab-47c8-ba87-28600b342f19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralCoefficients
import Theorems.Thm_GlobalTheory_NonzeroDeterminantIntegrality_exists_det_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonzeroDeterminantIntegrality
open Matrix
namespace GlobalTheory.NonzeroDeterminantIntegrality
theorem _root_.solution : ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁]
    (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a : W, i₁ a ≠ 0 → IsUnit a) →
    ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W),
    (∀ c : Λ → K₁, (∀ i : I, ∑ l : Λ, c l * i₁ (u i l) = 0) → c = 0) →
    ∀ (w : I → W) (z : Λ → K₀), (∀ i : I, i₀ (w i) = ∑ l : Λ, z l * i₀ (u i l)) →
    ∃ z₀ : Λ → W, (∀ l : Λ, i₀ (z₀ l) = z l) ∧ ∀ i : I, w i = ∑ l : Λ, z₀ l * u i l := by
  intro W _ _ K₀ K₁ _ _ i₀ i₁ hinj hunit I Λ _ u hu w z hz
  classical
  obtain ⟨f, hf⟩ := exists_det_ne_zero (fun i l => i₁ (u i l)) hu
  let M : Matrix Λ Λ W := Matrix.of fun a l => u (f a) l
  have hdet : IsUnit M.det := by
    apply hunit
    rw [RingHom.map_det]
    exact hf
  let z₀ : Λ → W := M⁻¹ *ᵥ (fun a => w (f a))
  have hM : M *ᵥ z₀ = fun a => w (f a) := by
    simp only [z₀]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hdet₀ : IsUnit (i₀.mapMatrix M).det := by
    rw [← RingHom.map_det]
    exact hdet.map i₀
  have key : (fun l => i₀ (z₀ l)) = z := by
    apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hdet₀)
    funext a
    have h1 := congrArg i₀ (congrFun hM a)
    rw [hz] at h1
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h1 ⊢
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨z₀, fun l => congrFun key l, fun i => hinj ?_⟩
  rw [hz, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← congrFun key l]
end GlobalTheory.NonzeroDeterminantIntegrality
