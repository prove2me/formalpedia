-- Prove2me | solution 1 for GlobalTheory.BK.BKDat.Mon_add_phi_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:28:48.96089+00:00
-- url     : https://prove2.me/submissions/89bc6789-99c1-4b02-8043-ddf413666712

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_PhiMod_Mon_phi_sub
import Theorems.Thm_GlobalTheory_BK_PhiMod_cls_eq_zero_iff


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
theorem _root_.solution (y : Vec K a ι) {m : Vec K a ι} (hm : m ∈ D.Man) :
    D.Mon (y + (D.phi m - m)) = D.Mon y := by
  rw [map_add, PhiMod.Mon_phi_sub, D.cls_eq_zero_iff.2 (D.EN_mem_Man hm), neg_zero, add_zero]
end GlobalTheory.BK.BKDat
