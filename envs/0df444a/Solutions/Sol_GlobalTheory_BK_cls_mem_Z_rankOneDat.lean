-- Prove2me | solution 1 for GlobalTheory.BK.cls_mem_Z_rankOneDat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:48:09.357852+00:00
-- url     : https://prove2.me/submissions/97bf37fe-cd7b-4a5c-ba18-0ff548839c19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_Descent_cls_mem_Z
import Theorems.Thm_GlobalTheory_BK_E_pow_mul_Ezpow_neg
import Theorems.Thm_GlobalTheory_BK_Ezpow_add
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_PhiMod_cls_eq_zero_iff
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_map_Ezpow
import Theorems.Thm_GlobalTheory_BK_mem_tot
import Theorems.Thm_GlobalTheory_BK_ringAct_E
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
variable [CompleteSpace K] {j : ℤ} (h₁ : -(η : ℤ) ≤ j) (h₂ : j ≤ H)
namespace GlobalTheory.BK
theorem _root_.solution (hη : 1 ≤ η) :
    (rankOneDat O K l e a η H j h₁ h₂ 1).cls (Ezpow K l e (-1) • bas ()) ∈
        (rankOneDat O K l e a η H j h₁ h₂ 1).Z ∧
      (rankOneDat O K l e a η H j h₁ h₂ 1).cls (Ezpow K l e (-1) • bas ()) ≠ 0 := by
  refine ⟨Descent.cls_mem_Z _ ⟨mem_tot.2 fun τ i => ?_, fun g => ?_⟩, fun h => ?_⟩
  · have := Ezpow_mem_A (O := O) (K := K) (l := l) (e := e) (i := η + -1) (by omega)
    rw [Ezpow_add, Ezpow_natCast] at this
    simpa [bas] using this
  · ext τ i : 2
    refine (rankOneDesc_act j 1 g _ τ).trans ?_
    simpa [bas] using map_Ezpow l e _ (congrFun (ringAct_E g) τ) (-1)
  · have h1 := mem_tot.1 ((PhiMod.cls_eq_zero_iff _).1 h) 0 ()
    have h2 : E K l e * Ezpow K l e (-1) = 1 := by simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
    have h3 := eq_zero_of_E_mul (O := O) (g := Ezpow K l e (-1)) l e (by simpa [bas] using h1)
      fun n => by rw [h2, coeff_one, if_neg (by have := NeZero.pos e; omega)]
    exact Units.ne_zero _ h3
end GlobalTheory.BK
