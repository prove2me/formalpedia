-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.zeta_phi_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:49:02.234805+00:00
-- url     : https://prove2.me/submissions/f6229aa4-4c69-4a93-90c9-7cce9952a10e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_mem_uPow
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_phi
import Theorems.Thm_GlobalTheory_BK_PhiMod_lphi_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_zeta_unique

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
theorem _root_.solution (m : Vec K a ι) : P.zeta (P.phi m - m) = P.conn (P.phi m) :=
  (P.zeta_unique (P.conn_mem_uPow _) (by
    rw [map_sub P.conn, sub_sub_cancel, lphi_apply, conn_phi])).symm
end GlobalTheory.BK.PhiMod
