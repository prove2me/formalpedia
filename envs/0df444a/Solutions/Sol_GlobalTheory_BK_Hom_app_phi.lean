-- Prove2me | solution 1 for GlobalTheory.BK.Hom.app_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:55:21.982842+00:00
-- url     : https://prove2.me/submissions/bd07031d-5eb4-4f8b-b852-cbb82c7a75ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_PhiMod_phi_apply
import Theorems.Thm_GlobalTheory_BK_Hom_app_apply

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
variable {O K l e a ι} [Fact l.Prime] {κ μ : Type} [Fintype κ] [DecidableEq κ] [Fintype μ]
  [DecidableEq μ]
open GlobalTheory.BK.Hom
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
namespace GlobalTheory.BK.Hom
theorem _root_.solution (F : Hom P Q) (v : Vec K a ι) : F.app (P.phi v) = Q.phi (F.app v) := by
  ext1 τ
  rw [app_apply, P.phi_apply, Q.phi_apply, app_apply, Matrix.mulVec_mulVec, F.comm,
    ← Matrix.mulVec_mulVec]
  congr 1
  ext1 i
  exact (RingHom.map_mulVec (frob K l).toRingHom _ _ i).symm
end GlobalTheory.BK.Hom
