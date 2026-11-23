-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.lintegral_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:23.451799+00:00
-- url     : https://prove2.me/submissions/571995e1-6caa-47a5-9a9a-330efb6cf011

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
    (F : (Fin n → Fin k → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c = ENNReal.ofReal ((‖A.det‖ ^ 2) ^ k) *
      ∫⁻ z : Fin n → Fin k → ℂ, F (fun a b => (A * Matrix.of z) a b) := by
  let P : (Fin k → Fin n → ℂ) →ₗ[ℂ] (Fin k → Fin n → ℂ) :=
    LinearMap.pi fun c => (Matrix.toLin' A).comp (LinearMap.proj c)
  let e : (Fin k → Fin n → ℂ) ≃ₗ[ℂ] (Fin n → Fin k → ℂ) :=
    { toFun := fun x a b => x b a
      invFun := fun x a b => x b a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let L : (Fin n → Fin k → ℂ) →ₗ[ℂ] (Fin n → Fin k → ℂ) :=
    (e : _ →ₗ[ℂ] _) ∘ₗ P ∘ₗ (e.symm : _ →ₗ[ℂ] _)
  have hL : LinearMap.det L = A.det ^ k := by
    rw [LinearMap.det_conj, LinearMap.det_pi]
    simp
  have h2 : ∀ z : Fin n → Fin k → ℂ, L z = fun a b => (A * Matrix.of z) a b := fun z => rfl
  rw [lintegral_linear L (hL ▸ pow_ne_zero _ hA) F hF, hL, norm_pow, ← pow_mul, ← pow_mul, mul_comm k]
  simp only [h2]
end GlobalTheory.GLFirstColumn
