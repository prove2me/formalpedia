-- Prove2me | solution 1 for GlobalTheory.BK.one_notMem_Lcomp_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:52.348197+00:00
-- url     : https://prove2.me/submissions/ee281c39-dabc-4bda-b9bc-d0b220579e7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_mem_Lcomp_rankOne
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
theorem _root_.solution (τ : ZMod a) :
    (fun _ => 1) ∉ (rankOne O K l e fun _ : ZMod a => 1).Lcomp τ := by
  rw [mem_Lcomp_rankOne (n := 1) rfl]
  rintro ⟨m, hm, h⟩
  have h1 := congrArg (fun f => ‖constantCoeff f‖) h
  simp only [map_one, norm_one, pow_one, map_mul, constantCoeff_E, norm_mul] at h1
  have h2 := hm 0
  rw [coeff_zero_eq_constantCoeff] at h2
  have := norm_l_lt_one (K := K) l
  nlinarith [norm_nonneg (l : K)]
end GlobalTheory.BK
