-- Prove2me | solution 1 for GlobalTheory.BK.Descent.act_conn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:32:34.625074+00:00
-- url     : https://prove2.me/submissions/6acf700e-4779-44a2-b3ed-62b5e6bb7175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Theorems.Thm_GlobalTheory_BK_ringAct_NTot
import Theorems.Thm_GlobalTheory_BK_PhiMod_map_conn


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
theorem _root_.solution (v : Vec K a ι) : Δ.act g (P.conn v) = P.conn (Δ.act g v) :=
  PhiMod.map_conn (Δ.act g).toAddMonoidHom (ringAct g) (ringAct_NTot g) (Δ.act_smul_tot g)
    (Δ.act_phi g) v
end GlobalTheory.BK.Descent
