-- Prove2me | solution 1 for GlobalTheory.T.cauchy_slice_eq_removable_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:36:09.816239+00:00
-- url     : https://prove2.me/submissions/874ec8be-7417-4823-ac70-6aa25b5a1b3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CauchySliceEqRemovableExtension
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CauchySliceEqRemovableExtensionStatement
import Theorems.Thm_GlobalTheory_cauchy_slice_removable_extension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r M : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.ball z₀ (2 * r) ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z ∈ Metric.ball z₀ (2 * r), z k ≠ 0 → ‖f z‖ ≤ M) → ∀ z ∈ Metric.ball z₀ r, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) = (if z k = 0 then limUnder (nhdsWithin (0 : ℂ) {0}ᶜ) (fun t => f (Function.update z k t)) else f z) := by
  first | exact @GlobalTheory.cauchy_slice_removable_extension | exact GlobalTheory.cauchy_slice_removable_extension | (intros; apply GlobalTheory.cauchy_slice_removable_extension <;> assumption)
end _root_.GlobalTheory.T
