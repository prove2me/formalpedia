-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.lintegral_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:55:22.350252+00:00
-- url     : https://prove2.me/submissions/1b15f3a0-1b60-4124-83eb-1e59c7bb6be4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
import Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_linear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn
namespace GlobalTheory.GLFirstColumn
theorem _root_.solution {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0)
    (F : (Fin k → Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c = ENNReal.ofReal ((‖A.det‖ ^ 2) ^ k) *
      ∫⁻ z : Fin k → Fin n → ℂ, F (fun a b => (Matrix.of z * A) a b) := by
  let L : (Fin k → Fin n → ℂ) →ₗ[ℂ] (Fin k → Fin n → ℂ) :=
    LinearMap.pi fun i => (Matrix.toLin' Aᵀ).comp (LinearMap.proj i)
  have hL : LinearMap.det L = A.det ^ k := by
    rw [LinearMap.det_pi]; simp [LinearMap.det_toLin']
  have h2 : ∀ z : Fin k → Fin n → ℂ, L z = fun a b => (Matrix.of z * A) a b := by
    intro z; ext a b
    simp [L, Matrix.toLin'_apply, mulVec_transpose, vecMul, dotProduct, Matrix.mul_apply]
  rw [lintegral_linear L (hL ▸ pow_ne_zero _ hA) F hF, hL, norm_pow, ← pow_mul, ← pow_mul, mul_comm k]
  simp only [h2]
end GlobalTheory.GLFirstColumn
