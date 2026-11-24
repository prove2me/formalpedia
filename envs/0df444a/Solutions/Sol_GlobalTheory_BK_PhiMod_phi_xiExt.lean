-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.phi_xiExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:25:00.478736+00:00
-- url     : https://prove2.me/submissions/1589ee7a-94ea-4352-9231-83fe6ab093b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_mx_mul_xiMat
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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (w : Vec K a ι) :
    P.phi (P.xiExt w) = P.xiExt fun τ => (P.mx0 τ).map C *ᵥ frobV l (w (τ - 1)) := by
  ext1 τ
  rw [phi_apply, xiExt_apply, xiExt_apply, Matrix.mulVec_mulVec, ← mx_mul_xiMat,
    ← Matrix.mulVec_mulVec]
  congr 1
  ext1 i
  exact RingHom.map_mulVec (frob K l).toRingHom _ _ i
end GlobalTheory.BK.PhiMod
