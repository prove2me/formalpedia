-- Prove2me | solution 1 for GlobalTheory.T.GL_inv_mul_congr_one_mod_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:15:40.170518+00:00
-- url     : https://prove2.me/submissions/9f1f68c9-8747-4762-8133-fcac2fb608ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GLInvMulCongrOneModUniformizer
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GLInvMulCongrOneModUniformizerStatement
import Theorems.Thm_GlobalTheory_GL_inv_mul_congr_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {N : ℕ} (π : K), π ≠ 0 → Valued.v π < 1 →
  ∀ (a a₁ : GL (Fin N) K), (∀ i j, Valued.v (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    (∀ i j, Valued.v (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    ∀ i j, Valued.v (π⁻¹ * (((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1 := by
  first | exact @GlobalTheory.GL_inv_mul_congr_one | exact GlobalTheory.GL_inv_mul_congr_one | (intros; apply GlobalTheory.GL_inv_mul_congr_one <;> assumption)
end _root_.GlobalTheory.T
