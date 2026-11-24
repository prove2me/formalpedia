-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_scalar_mul_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:34.047929+00:00
-- url     : https://prove2.me/submissions/8d99107b-bc25-4086-8a30-1699e34a5e00

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryFramesPreserveNormSqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnitFrame
namespace GlobalTheory.CompanionTheory.UnitFrame
theorem _root_.solution {m : ℕ} (J : Matrix (Fin m) (Fin m) ℂ) (fr : GL (Fin m) ℂ)
    (ζ : ℂ) (s : ℤˣ)
    (h : ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1) (v : Fin m → ℂ) :
    ((∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 : ℝ) : ℂ) =
      (((s : ℤ) : ℂ) * star ζ) * (star v ⬝ᵥ (J.map star *ᵥ v)) := by
  obtain ⟨w, hw, hv⟩ : ∃ w, (fr⁻¹).1 *ᵥ v = w ∧ v = fr.1 *ᵥ w :=
    ⟨_, rfl, by rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]⟩
  rw [hw]
  subst hv
  have hc : ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hB : star ζ • (fr.1ᵀ * J * fr.1.map star).map star =
      ((s : ℤ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    have h1 := congrArg star (congrFun (congrFun h i) j)
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul'] at h1 ⊢
    rw [h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hX : (fr.1ᵀ * J * fr.1.map star).map star = fr.1ᴴ * J.map star * fr.1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      star_sum, star_mul', star_star]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← hX, mul_assoc,
    ← smul_eq_mul (star ζ), ← dotProduct_smul, ← smul_mulVec, hB, smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul, ← mul_assoc, hc, one_mul]
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
end GlobalTheory.CompanionTheory.UnitFrame
