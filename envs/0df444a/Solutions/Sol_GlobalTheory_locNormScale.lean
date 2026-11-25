-- Prove2me | solution 1 for GlobalTheory.locNormScale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:16:54.175033+00:00
-- url     : https://prove2.me/submissions/841b8e15-5b02-4bd4-8c73-af2a7b806a61

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AlgebraicTheory_StatementNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LocalNormalizationIntegralScalar
import Theorems.Thm_GlobalTheory_tensorFourthPower_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Formalism.L2.AlgTh
namespace GlobalTheory
theorem _root_.solution : LocNormScale := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι c hc hLN
  obtain ⟨g₁, ε, hiso, hp, hidx, hε, heq⟩ := hLN
  refine ⟨g₁, c ^ 4 * ε, hiso, hp, hidx, ?_, ?_⟩
  · rw [map_mul, map_pow, norm_mul, norm_pow]
    have h0 : 0 ≤ ‖ι c‖ := norm_nonneg _
    have h4 : ‖ι c‖ ^ 4 ≤ 1 := pow_le_one₀ h0 hc
    calc ‖ι c‖ ^ 4 * ‖ι ε‖ ≤ 1 * 1 := mul_le_mul h4 hε (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [tensorFourthPower_smul, heq, smul_smul]
end GlobalTheory
