-- Prove2me | solution 1 for GlobalTheory.BK.Descent.act_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:30:11.308125+00:00
-- url     : https://prove2.me/submissions/22c91b75-b928-4566-af3a-de050d03a525

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Theorems.Thm_GlobalTheory_BK_Descent_red_act
import Theorems.Thm_GlobalTheory_BK_PhiMod_map_xi


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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P) (g : TameGal K l e a)
namespace GlobalTheory.BK.Descent
theorem _root_.solution (d : P.D) : Δ.act g (P.xi d) = P.xi (Δ.actD g d) := by
  rw [PhiMod.map_xi (Δ.act_phi g), red_act, PhiMod.red_xi]
end GlobalTheory.BK.Descent
