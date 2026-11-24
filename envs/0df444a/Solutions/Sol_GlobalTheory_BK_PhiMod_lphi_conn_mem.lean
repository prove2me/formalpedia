-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.lphi_conn_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:57:32.990543+00:00
-- url     : https://prove2.me/submissions/c2eafdcc-96a6-4506-938f-f7b7601ecfb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_uPow_anti
import Theorems.Thm_GlobalTheory_BK_PhiMod_conn_mem_uPow
import Theorems.Thm_GlobalTheory_BK_PhiMod_raises_lphi

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
theorem _root_.solution (y : Vec K a ι) : P.lphi (P.conn y) ∈ uPow K a ι 1 :=
  uPow_anti one_le_two (P.raises_lphi 0 _ (P.conn_mem_uPow y))
end GlobalTheory.BK.PhiMod
