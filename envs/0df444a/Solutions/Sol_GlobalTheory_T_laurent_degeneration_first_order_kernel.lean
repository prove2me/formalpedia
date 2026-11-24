-- Prove2me | solution 1 for GlobalTheory.T.laurent_degeneration_first_order_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:06.941027+00:00
-- url     : https://prove2.me/submissions/6c9dda1e-f054-4491-aa88-2105e0a130dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentDegenerationFirstOrderKernel
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentDegenerationFirstOrderKernelStatement
import Theorems.Thm_GlobalTheory_laurent_degeneration


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k], ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ : K), ∀ (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U] (t u : V →ₗ[k] U), e ≤ 1 → (∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → ∀ y : Fin (e + 1) → Fin a → K, (∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧ (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') → ¬ LinearIndependent K y := by
  first | exact @GlobalTheory.laurent_degeneration | exact GlobalTheory.laurent_degeneration | (intros; apply GlobalTheory.laurent_degeneration <;> assumption)
end _root_.GlobalTheory.T
