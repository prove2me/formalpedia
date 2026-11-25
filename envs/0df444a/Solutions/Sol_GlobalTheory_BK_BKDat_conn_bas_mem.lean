-- Prove2me | solution 1 for GlobalTheory.BK.BKDat.conn_bas_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:44:46.845147+00:00
-- url     : https://prove2.me/submissions/4ca83c6d-513b-4f64-ac2f-26764e6d9971

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_PhiMod_bas_mem_M
import Theorems.Thm_GlobalTheory_BK_PhiMod_mem_Mext_invE_of_mem_divE


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
omit [NeZero e]
namespace GlobalTheory.BK.BKDat
theorem _root_.solution (i : ι) : D.conn (bas i) ∈ D.Mext (RpiE O K l e) :=
  D.mem_Mext_invE_of_mem_divE (n := 1) (by rw [pow_one]; exact D.EN_mem _ (D.bas_mem_M i))
end GlobalTheory.BK.BKDat
