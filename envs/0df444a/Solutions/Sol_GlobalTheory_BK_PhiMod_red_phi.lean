-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.red_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:52:42.94341+00:00
-- url     : https://prove2.me/submissions/2ac778d0-b70c-4885-b584-f571d7d4d6dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_PhiMod_phiD_apply
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_apply

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
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
open GlobalTheory.BK.PhiMod
variable {O K l e a ι} (P : PhiMod O K l e a ι)
variable [Fact l.Prime]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (v : Vec K a ι) : red (P.phi v) = P.phiD (red v) := by
  ext1 τ
  rw [red_apply, phi_apply, powerSeriesVecReduceModU_mulVec, phiD_apply]
  congr 1
  ext i
  simp
end GlobalTheory.BK.PhiMod
