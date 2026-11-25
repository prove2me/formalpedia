-- Prove2me | solution 1 for GlobalTheory.BK.Descent.tameDescent_extended_action_extraVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:01.287585+00:00
-- url     : https://prove2.me/submissions/65cf0c2f-fe8a-41c3-a79f-809f3fba603c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_Descent_plus_act_join


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
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
variable (Δ : Descent P) {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) (hinv : y ∈ Δ.inv)
namespace GlobalTheory.BK.Descent
theorem _root_.solution (g : TameGal K l e a) : (Δ.plus hy hinv).act g xVec = xVec := by
  rw [xVec, plus_act_join, map_zero, map_one]
end GlobalTheory.BK.Descent
