-- Prove2me | solution 1 for GlobalTheory.T.schwartz_linear_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:26:52.543885+00:00
-- url     : https://prove2.me/submissions/74b298a0-ea67-4cd1-aed0-7bb7df2bd232

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzLinearChange
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzLinearChangeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_KlocopSw_exists_schwartz_rightMul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix SchwartzMap
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (m n : ℕ) (c : ℂ) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => c * φ (Matrix.of u * a) := by
  first | exact @GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul | exact GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul | (intros; apply GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul <;> assumption)
end _root_.GlobalTheory.T
