-- Prove2me | solution 1 for GlobalTheory.BK.ringAct_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:50.423538+00:00
-- url     : https://prove2.me/submissions/012d2d9c-5395-4e74-ba94-866cc4882d10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {K : Type} [NormedField K] (l : ℕ) {e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero a] [TameDescentExponentData K l e a]
variable {l}
namespace GlobalTheory.BK
theorem _root_.solution (g : TameGal K l e a) : ringAct g (fun _ => X ^ e) = fun _ => X ^ e := by
  ext1 τ
  rw [ringAct_apply, map_pow, rescale_X, mul_pow, ← map_pow, g.root_pow, map_one, one_mul]
end GlobalTheory.BK
