-- Prove2me | solution 1 for GlobalTheory.gram_det_cauchy_schwarz_of_det_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:03.649621+00:00
-- url     : https://prove2.me/submissions/8c772d2f-3f8b-4529-801e-dea58bdb445f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetCauchySchwarzOfDetMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0)) → (∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq n] (A B : Matrix m n ℂ), ‖(Aᴴ * B).det‖ ^ 2 ≤ (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ∧ ((Aᴴ * B).det ≠ 0 → (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ≤ ‖(Aᴴ * B).det‖ ^ 2 → ∃ C : Matrix n n ℂ, B = A * C)) := by
  intro H m n _ _ _ A B
  classical
  have hA : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  have hB : (Bᴴ * B).PosSemidef := posSemidef_conjTranspose_mul_self B
  have hA0 : 0 ≤ (Aᴴ * A).det.re := (H n _ _ hA hA).1
  have hB0 : 0 ≤ (Bᴴ * B).det.re := (H n _ _ hB hB).1
  by_cases hG : (Aᴴ * A).det = 0
  · obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hG
    have hAv : A *ᵥ v = 0 := (conjTranspose_mul_self_mulVec_eq_zero A v).mp hv0
    have h1 : (Bᴴ * A).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, by rw [← mulVec_mulVec, hAv, mulVec_zero]⟩
    have h2 : (Aᴴ * B).det = 0 := by
      have : Aᴴ * B = (Bᴴ * A)ᴴ := by simp
      rw [this, det_conjTranspose, h1, star_zero]
    refine ⟨?_, fun h => (h h2).elim⟩
    rw [h2]
    simpa using mul_nonneg hA0 hB0
  · have hreal : (Aᴴ * A).det = ((Aᴴ * A).det.re : ℂ) := by
      have : star (Aᴴ * A).det = (Aᴴ * A).det := by
        rw [← det_conjTranspose, hA.1.eq]
      exact (Complex.conj_eq_iff_re.mp this).symm
    set g : ℝ := (Aᴴ * A).det.re with hg
    have hg0 : g ≠ 0 := fun h => hG (by rw [hreal, h]; simp)
    have hgpos : 0 < g := lt_of_le_of_ne hA0 hg0.symm
    obtain ⟨C, hC⟩ : ∃ C : Matrix n n ℂ, (Aᴴ * A) * C = Aᴴ * B :=
      ⟨(Aᴴ * A)⁻¹ * (Aᴴ * B), mul_nonsing_inv_cancel_left _ _ (Ne.isUnit hG)⟩
    have horth : (A * C)ᴴ * (B - A * C) = 0 := by
      rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_sub, ← Matrix.mul_assoc Aᴴ A C, hC,
        sub_self, Matrix.mul_zero]
    have horth' : (B - A * C)ᴴ * (A * C) = 0 := by
      have := congrArg conjTranspose horth
      rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
    have hsum : Bᴴ * B = (A * C)ᴴ * (A * C) + (B - A * C)ᴴ * (B - A * C) := by
      have hBe : B = A * C + (B - A * C) := by abel
      generalize B - A * C = D at *
      generalize A * C = E at *
      rw [hBe, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, horth, horth']
      simp
    have hP : ((A * C)ᴴ * (A * C)).det = ((g * ‖C.det‖ ^ 2 : ℝ) : ℂ) := by
      have : (A * C)ᴴ * (A * C) = Cᴴ * (Aᴴ * A) * C := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [this, det_mul, det_mul, det_conjTranspose, hreal]
      push_cast
      rw [← Complex.conj_mul' C.det]
      simp only [RCLike.star_def]
      ring
    have hAB : (Aᴴ * B).det = g * C.det := by rw [← hC, det_mul, hreal]
    have hN : ‖(Aᴴ * B).det‖ ^ 2 = g * (g * ‖C.det‖ ^ 2) := by
      rw [hAB, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA0]
      ring
    obtain ⟨-, h2, h3⟩ := H n _ _ (posSemidef_conjTranspose_mul_self (A * C))
      (posSemidef_conjTranspose_mul_self (B - A * C))
    rw [← hsum, hP, Complex.ofReal_re] at h2 h3
    rw [hN]
    refine ⟨mul_le_mul_of_nonneg_left h2 hA0, fun hne hle => ⟨C, ?_⟩⟩
    have hc : C.det ≠ 0 := fun h => hne (by rw [hAB, h, mul_zero])
    have hQ := h3 (by
      have : g * ‖C.det‖ ^ 2 ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))
      exact_mod_cast this) (le_of_mul_le_mul_left hle hgpos)
    exact sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp hQ)
end GlobalTheory
