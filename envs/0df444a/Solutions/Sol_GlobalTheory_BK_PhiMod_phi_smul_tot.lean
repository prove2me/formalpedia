-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.phi_smul_tot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:02:01.608601+00:00
-- url     : https://prove2.me/submissions/8fba4c8c-51c8-4327-a059-199426d65029

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
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
theorem _root_.solution (f : ZMod a → K⟦X⟧) (v : Vec K a ι) :
    P.phi (f • v) = frobTot K a l f • P.phi v := by
  ext1 τ
  rw [Pi.smul_apply', phi_apply, phi_apply, ← Matrix.mulVec_smul]
  congr 1
  ext1 i
  simp
end GlobalTheory.BK.PhiMod
