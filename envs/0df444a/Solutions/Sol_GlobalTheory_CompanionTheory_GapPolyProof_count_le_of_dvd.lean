-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapPolyProof.count_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:32:59.385736+00:00
-- url     : https://prove2.me/submissions/34c7eade-5d83-4327-a151-2547b4257cef

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountLeOfDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapPolyProof
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
namespace GlobalTheory.CompanionTheory.GapPolyProof
theorem _root_.solution (S : Multiset ℂ) (q c d z : ℂ) (hq : q ≠ 0) (hc : c ≠ 0) (f : ℂ[X])
    (hf : (X - C z) ^ (S.count z) ∣ f)
    (hrel : C d * (X * f) = C c * (((S.map (fun t => X - C t)).prod).comp (C q * X) - (S.map (fun t => X - C t)).prod)) :
    S.count z ≤ S.count (q * z) := by
  set G := (S.map (fun t => X - C t)).prod with hGdef
  have hGroots : G.roots = S := roots_multiset_prod_X_sub_C S
  have hG0 : G ≠ 0 := (monic_multiset_prod_of_monic _ _ (fun t _ => monic_X_sub_C t)).ne_zero
  have hcount : ∀ w, S.count w = rootMultiplicity w G := fun w => by rw [← count_roots, hGroots]
  have h1 : (X - C z) ^ (S.count z) ∣ G := by
    rw [hcount]; exact pow_rootMultiplicity_dvd _ _
  have h2 : (X - C z) ^ (S.count z) ∣ C c * G.comp (C q * X) := by
    have : C c * G.comp (C q * X) = C d * (X * f) + C c * G := by rw [hrel]; ring
    rw [this]
    exact dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_left hf _) _) (Dvd.dvd.mul_left h1 _)
  have h3 : (X - C z) ^ (S.count z) ∣ G.comp (C q * X) :=
    ((isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)).dvd_mul_left).1 h2
  obtain ⟨H, hH⟩ := h3
  have h4 : G = (C q⁻¹ * (X - C (q * z))) ^ (S.count z) * H.comp (C q⁻¹ * X) := by
    have e1 : (G.comp (C q * X)).comp (C q⁻¹ * X) = G := by
      rw [comp_assoc]
      have : (C q * X : ℂ[X]).comp (C q⁻¹ * X) = X := by
        simp only [mul_comp, C_comp, X_comp]
        rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hq, C_1, one_mul]
      rw [this, comp_X]
    have e2 : (X - C z : ℂ[X]).comp (C q⁻¹ * X) = C q⁻¹ * (X - C (q * z)) := by
      simp only [sub_comp, X_comp, C_comp, mul_sub, ← C_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul]
    rw [← e1, hH, mul_comp, pow_comp, e2]
  have h5 : (X - C (q * z)) ^ (S.count z) ∣ G := by
    rw [h4, mul_pow, mul_assoc]
    refine ((isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hq))).pow _).dvd_mul_left.2 ?_
    exact Dvd.intro _ rfl
  rw [hcount (q * z)]
  exact (le_rootMultiplicity_iff hG0).2 h5
end GlobalTheory.CompanionTheory.GapPolyProof
