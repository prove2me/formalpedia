-- Prove2me | solution 1 for GlobalTheory.BK.Descent.actPol_Mon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:52.30409+00:00
-- url     : https://prove2.me/submissions/7f14b092-d552-49f6-bb19-6997f4b49a9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_Descent_act_EN
import Theorems.Thm_GlobalTheory_BK_Descent_act_E_smul
import Theorems.Thm_GlobalTheory_BK_Descent_act_zeta
import Theorems.Thm_GlobalTheory_BK_PhiMod_Mon_apply


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
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P)
namespace GlobalTheory.BK.Descent
theorem _root_.solution (g : TameGal K l e a) (y : Vec K a ι) :
    Δ.actPol g (P.Mon y) = P.Mon (Δ.act g y) := by
  rw [PhiMod.Mon_apply, actPol_cls, map_sub, act_EN, act_E_smul, act_zeta, PhiMod.Mon_apply]
end GlobalTheory.BK.Descent
