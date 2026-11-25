-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.phi_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:26:39.079954+00:00
-- url     : https://prove2.me/submissions/5fb2107e-32b7-462c-957d-e0744b12d114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_apply
import Theorems.Thm_GlobalTheory_BK_frob_injective


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
theorem _root_.solution : Function.Injective P.phi := fun v w h => by
  ext1 τ
  ext1 i
  have := congrArg (fun x => (P.mxInv (τ + 1) *ᵥ x (τ + 1)) i) h
  simp only [phi_apply, Matrix.mulVec_mulVec, mxInv_mul_mx, Matrix.one_mulVec, add_sub_cancel_right,
    frobV_apply] at this
  exact frob_injective l this
end GlobalTheory.BK.PhiMod
