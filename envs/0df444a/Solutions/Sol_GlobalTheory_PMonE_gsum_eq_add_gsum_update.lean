-- Prove2me | solution 1 for GlobalTheory.PMonE.gsum_eq_add_gsum_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:17:33.992222+00:00
-- url     : https://prove2.me/submissions/8332c51d-2206-48f1-b444-c9a972f4bfa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE Finset
open GlobalTheory GlobalTheory.PMonE
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
    (q D : ℕ) (U : ℕ → Matrix m m F) (y : m → F) :
    gsum q D U y = y + gsum q D (fun n => if n = 0 then U 0 - 1 else U n) y := by
  unfold gsum
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp [Matrix.sub_mulVec]
  abel
end GlobalTheory.PMonE
