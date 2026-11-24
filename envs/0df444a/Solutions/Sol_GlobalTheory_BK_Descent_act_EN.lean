-- Prove2me | solution 1 for GlobalTheory.BK.Descent.act_EN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:08.622494+00:00
-- url     : https://prove2.me/submissions/6648b7d7-bcf2-4c89-be94-89b9e19f24af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_Descent_act_E_smul
import Theorems.Thm_GlobalTheory_BK_Descent_act_conn
import Theorems.Thm_GlobalTheory_BK_PhiMod_EN_apply


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
omit [NeZero e]
namespace GlobalTheory.BK.Descent
theorem _root_.solution (g : TameGal K l e a) (v : Vec K a ι) : Δ.act g (P.EN v) = P.EN (Δ.act g v) := by
  rw [PhiMod.EN_apply, act_E_smul, act_conn, PhiMod.EN_apply]
end GlobalTheory.BK.Descent
