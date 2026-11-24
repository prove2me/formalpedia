-- Prove2me | solution 1 for GlobalTheory.BK.Hom.app_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:21.918011+00:00
-- url     : https://prove2.me/submissions/e1e0086d-d8c8-49c0-a8f1-8c83021285e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_map_zeta
import Theorems.Thm_GlobalTheory_BK_Hom_app_mem_uPow
import Theorems.Thm_GlobalTheory_BK_Hom_app_conn
import Theorems.Thm_GlobalTheory_BK_Hom_app_phi


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
theorem _root_.solution (y : Vec K a ι) : F.app (P.zeta y) = Q.zeta (F.app y) :=
  PhiMod.map_zeta (F.app.restrictScalars K) (fun _ => F.app_mem_uPow) F.app_phi F.app_conn y
end GlobalTheory.BK.Hom
