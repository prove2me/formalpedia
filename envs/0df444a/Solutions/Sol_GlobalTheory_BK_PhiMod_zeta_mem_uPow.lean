-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.zeta_mem_uPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:12:38.2068+00:00
-- url     : https://prove2.me/submissions/25e0267c-1e27-4f5b-aaf0-6226aac68d58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_geom_mem
import Theorems.Thm_GlobalTheory_BK_PhiMod_raises_lphi
import Theorems.Thm_GlobalTheory_BK_PhiMod_lphi_conn_mem

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
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (y : Vec K a ι) : P.zeta y ∈ uPow K a ι 1 :=
  neg_mem (geom_mem P.raises_lphi (P.lphi_conn_mem y))
end GlobalTheory.BK.PhiMod
