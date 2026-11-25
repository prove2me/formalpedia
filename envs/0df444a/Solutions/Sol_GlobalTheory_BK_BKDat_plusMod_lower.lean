-- Prove2me | solution 1 for GlobalTheory.BK.BKDat.plusMod_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:32:41.102325+00:00
-- url     : https://prove2.me/submissions/677eb592-190a-41de-b808-5125993f8bc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_PhiMod_plus_lower


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
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
open GlobalTheory.BK.BKDat
variable (D : BKDat O K l e a ι η H)
variable {D} {y : Vec K a ι}
omit [NeZero e]
namespace GlobalTheory.BK.BKDat
theorem _root_.solution (hy : y ∈ D.Y) :
    ∀ v ∈ (plusMod hy).M, E K l e ^ (H + η) • v ∈ (plusMod hy).L :=
  D.plus_lower _ (fun v hv => by
    rw [pow_add, mul_smul]
    exact D.lower _ (D.M.smul_mem (EIn l e (A O K) ^ η) hv)) (by
    rw [pow_add, mul_smul]
    exact D.lower _ hy.1)
end GlobalTheory.BK.BKDat
