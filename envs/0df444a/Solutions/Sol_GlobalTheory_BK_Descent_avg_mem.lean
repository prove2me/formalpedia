-- Prove2me | solution 1 for GlobalTheory.BK.Descent.avg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:00:11.527458+00:00
-- url     : https://prove2.me/submissions/241b7bca-4558-4096-9e4d-a59cb1296eaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_Descent_norm_card

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
theorem _root_.solution (W : Submodule O (Vec K a ι)) {v : Vec K a ι} (h : ∀ g, Δ.act g v ∈ W) :
    Δ.avg v ∈ W := by
  obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) ((Nat.card (TameGal K l e a) : K)⁻¹)).2
    (by rw [norm_inv, norm_card, inv_one])
  rw [avg, LinearMap.smul_apply, LinearMap.sum_apply, ← hc, algebraMap_smul]
  exact W.smul_mem c (W.sum_mem fun g _ => h g)
end GlobalTheory.BK.Descent
