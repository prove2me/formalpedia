-- Prove2me | solution 1 for GlobalTheory.BK.Descent.avg_of_mem_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:31:37.98036+00:00
-- url     : https://prove2.me/submissions/572f4430-f830-48fe-a4fc-ed73e2df2e5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_Descent_map_avg

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
theorem _root_.solution {v : Vec K a ι} (hv : v ∈ Δ.inv) : Δ.avg v = v := Δ.map_avg LinearMap.id hv
end GlobalTheory.BK.Descent
