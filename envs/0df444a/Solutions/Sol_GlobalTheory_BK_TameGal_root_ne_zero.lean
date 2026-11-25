-- Prove2me | solution 1 for GlobalTheory.BK.TameGal.root_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:59.107859+00:00
-- url     : https://prove2.me/submissions/bb1bfad8-48c6-4f63-ad0b-40606b16b82f

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
open GlobalTheory.BK.TameGal
variable {l}
namespace GlobalTheory.BK.TameGal
theorem _root_.solution (g : TameGal K l e a) (τ : ZMod a) : root g τ ≠ 0 := Units.ne_zero _
end GlobalTheory.BK.TameGal
