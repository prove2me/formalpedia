-- Prove2me | solution 1 for GlobalTheory.BK.mem_Lcomp_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:24.010354+00:00
-- url     : https://prove2.me/submissions/ae38edb7-32f3-4b32-8b6c-af443be8c633

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_mx_rankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.hat_coe
attribute [local simp] GlobalTheory.BK.coe_Eunit

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
variable {O K l e a}
namespace GlobalTheory.BK
theorem _root_.solution {j : ZMod a → ℤ} {τ : ZMod a} {n : ℕ} (h : j τ = n)
    {v : Unit → K⟦X⟧} :
    v ∈ (rankOne O K l e j).Lcomp τ ↔ ∃ m ∈ A O K, v () = E K l e ^ n * m := by
  rw [PhiMod.mem_extc]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m (), hm (), by simp [Matrix.mulVec, dotProduct, mx_rankOne h]⟩
  · rintro ⟨m, hm, hv⟩
    exact ⟨fun _ => m, fun _ => hm, funext fun _ => by
      simp [Matrix.mulVec, dotProduct, mx_rankOne h, hv]⟩
end GlobalTheory.BK
