-- Prove2me | solution 1 for GlobalTheory.BK.BKDat.hatTot_conn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:25:17.88249+00:00
-- url     : https://prove2.me/submissions/d72598f6-12db-407d-8fc4-7e852c79aed9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_BKDat_conn_bas_mem
import Theorems.Thm_GlobalTheory_BK_PhiMod_hatTot_conn


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
namespace GlobalTheory.BK.BKDat
theorem _root_.solution [CompleteSpace K] {v : Vec K a ι} (hv : v ∈ D.Mext (RpiE O K l e)) :
    D.hatTot (D.conn v) = D.connHat (D.hatTot v) := D.toPhiMod.hatTot_conn D.conn_bas_mem hv
end GlobalTheory.BK.BKDat
