-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.plusProj_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:46:33.013884+00:00
-- url     : https://prove2.me/submissions/ecebd22a-b62c-4e8a-ad07-bd7883808ef0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_Hom_app_apply
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))
variable [NormedAlgebra ℚ_[l] K] [NeZero e]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    (P.plusProj hy).app (join v f) = fun τ _ => f τ := by
  ext1 τ
  rw [Hom.app_apply, plusProj]
  ext1 i
  simp [join]
end GlobalTheory.BK.PhiMod
