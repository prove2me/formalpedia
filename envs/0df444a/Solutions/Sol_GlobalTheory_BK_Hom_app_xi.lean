-- Prove2me | solution 1 for GlobalTheory.BK.Hom.app_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:25:17.409848+00:00
-- url     : https://prove2.me/submissions/51f1d6e6-c503-4320-90a3-4128290f8e6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_map_xi
import Theorems.Thm_GlobalTheory_BK_Hom_app_phi
import Theorems.Thm_GlobalTheory_BK_Hom_red_app


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
  [Fact l.Prime]
open GlobalTheory.BK.Hom
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)
namespace GlobalTheory.BK.Hom
theorem _root_.solution (d : P.D) : F.app (P.xi d) = Q.xi (F.onD d) := by
  rw [PhiMod.map_xi F.app_phi, red_app, PhiMod.red_xi]
end GlobalTheory.BK.Hom
