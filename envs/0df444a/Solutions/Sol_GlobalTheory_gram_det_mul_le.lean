-- Prove2me | solution 1 for GlobalTheory.gram_det_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:08:08.628216+00:00
-- url     : https://prove2.me/submissions/568ff19e-aa08-4f67-a6d7-00fd9f88371a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsScalarSubPosSemidef
import Theorems.Thm_GlobalTheory_exists_scalar_sub_posSemidef
import Theorems.Thm_GlobalTheory_gram_det_eq_zero_of_lt_card

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
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0)) → (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) := by
  intro H r a
  obtain ⟨c, hc1, hc⟩ := exists_scalar_sub_posSemidef (aᴴ * a) (Matrix.isHermitian_conjTranspose_mul_self a)
  refine ⟨c ^ r, one_le_pow₀ hc1, ?_⟩
  intro ι _ _ M
  by_cases hι : r < Fintype.card ι
  · rw [gram_det_eq_zero_of_lt_card (a * M) hι, gram_det_eq_zero_of_lt_card M hι]
    simp
  · push Not at hι
    have hP : (Mᴴ * (aᴴ * a) * M).PosSemidef :=
      (Matrix.posSemidef_conjTranspose_mul_self a).conjTranspose_mul_mul_same M
    have hQ : (Mᴴ * ((c : ℂ) • 1 - aᴴ * a) * M).PosSemidef := hc.conjTranspose_mul_mul_same M
    obtain ⟨-, hle, -⟩ := H ι _ _ hP hQ
    have hM0 : 0 ≤ (Mᴴ * M).det.re :=
      (H ι _ _ (Matrix.posSemidef_conjTranspose_mul_self M) (Matrix.posSemidef_conjTranspose_mul_self M)).1
    have e1 : (a * M)ᴴ * (a * M) = Mᴴ * (aᴴ * a) * M := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have e2 : Mᴴ * (aᴴ * a) * M + Mᴴ * ((c : ℂ) • 1 - aᴴ * a) * M = (c : ℂ) • (Mᴴ * M) := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [e1]
    refine hle.trans ?_
    rw [e2, Matrix.det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 hι) hM0
end GlobalTheory
