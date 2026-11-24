-- Prove2me | solution 1 for GlobalTheory.SummCount.pow_mul_inv_rpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:43.025362+00:00
-- url     : https://prove2.me/submissions/3906434f-803b-44a9-a045-05119374f444

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SummableRpowOfFibreCardLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummCount
namespace GlobalTheory.SummCount
theorem _root_.solution {b t : ℝ} (hb : 0 < b) (n m : ℕ) :
    b ^ (n * m) * ((b ^ m)⁻¹) ^ t = (b ^ ((n : ℝ) - t)) ^ m := by
  have hx : 0 < b ^ m := pow_pos hb m
  rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, pow_mul', ← Real.rpow_natCast (b ^ m) n,
    ← Real.rpow_add hx, ← Real.rpow_natCast b m, ← Real.rpow_mul hb.le,
    ← Real.rpow_mul_natCast hb.le]
  congr 1
  ring
end GlobalTheory.SummCount
