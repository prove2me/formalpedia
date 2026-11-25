-- Prove2me | solution 1 for GlobalTheory.BK.Descent.map_Y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:33:09.678547+00:00
-- url     : https://prove2.me/submissions/057db65b-61b5-4d60-9e02-f73215de1f1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_Descent_avg_mem_inv
import Theorems.Thm_GlobalTheory_BK_Descent_map_avg
import Theorems.Thm_GlobalTheory_BK_Descent_avg_mem
import Theorems.Thm_GlobalTheory_BK_Descent_cls_mem_Z
import Theorems.Thm_GlobalTheory_BK_Descent_mem_Z


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
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P)
namespace GlobalTheory.BK.Descent
theorem _root_.solution (η : ℕ) : (Δ.Y η).map (P.cls.restrictScalars O) = Δ.Z η := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact Δ.cls_mem_Z hy
  · obtain ⟨⟨y, hy, rfl⟩, h⟩ := Δ.mem_Z.1 hw
    exact ⟨Δ.avg y, ⟨Δ.avg_mem _ fun g => Δ.act_mem_EM g hy, Δ.avg_mem_inv y⟩, Δ.map_avg P.cls h⟩
end GlobalTheory.BK.Descent
