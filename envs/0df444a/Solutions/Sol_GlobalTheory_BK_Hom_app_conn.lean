-- Prove2me | solution 1 for GlobalTheory.BK.Hom.app_conn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:01.465219+00:00
-- url     : https://prove2.me/submissions/e40f0dfa-3ab8-4003-90cc-cb102171f13b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_map_conn
import Theorems.Thm_GlobalTheory_BK_Hom_app_smul_tot
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
theorem _root_.solution (v : Vec K a ι) : F.app (P.conn v) = Q.conn (F.app v) :=
  PhiMod.map_conn F.app.toAddMonoidHom id (fun _ => rfl) F.app_smul_tot F.app_phi v
end GlobalTheory.BK.Hom
