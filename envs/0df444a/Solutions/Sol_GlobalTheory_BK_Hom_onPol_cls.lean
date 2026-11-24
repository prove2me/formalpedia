-- Prove2me | solution 1 for GlobalTheory.BK.Hom.onPol_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:23.768696+00:00
-- url     : https://prove2.me/submissions/a3979856-6e89-412e-bd46-f536aa5b6697

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul

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
open GlobalTheory.BK.Hom
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)
namespace GlobalTheory.BK.Hom
theorem _root_.solution (v : Vec K a ι) : F.onPol (P.cls v) = Q.cls (F.app v) := rfl
end GlobalTheory.BK.Hom
