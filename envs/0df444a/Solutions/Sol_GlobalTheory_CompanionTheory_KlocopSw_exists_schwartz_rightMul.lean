-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:42:12.859185+00:00
-- url     : https://prove2.me/submissions/fa10af31-afdd-4818-a17f-fc0d1aad15f7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzLinearChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix SchwartzMap
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KlocopSw
namespace GlobalTheory.CompanionTheory.KlocopSw
theorem _root_.solution : ∀ (m n : ℕ) (c : ℂ) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det →
    ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ⇑ψ = fun u => c * φ (Matrix.of u * a) := by
  intro m n c a ha φ
  refine ⟨c • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((rightMulEquiv m n a ha).restrictScalars ℝ) φ, ?_⟩
  funext u
  rfl
end GlobalTheory.CompanionTheory.KlocopSw
