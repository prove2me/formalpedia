-- Prove2me | solution 1 for GlobalTheory.BK.Ezpow_mem_invL_A_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:38.546831+00:00
-- url     : https://prove2.me/submissions/f2bbeea6-adbf-4e58-b946-6e24fd463851

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_E_pow_mul_Ezpow_neg
import Theorems.Thm_GlobalTheory_BK_Ezpow_add
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_Rot_invL
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
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
omit [NeZero a] [TameDescentExponentData K l e a]
namespace GlobalTheory.BK
theorem _root_.solution {i : ℤ} : Ezpow K l e i ∈ invL l (A O K) ↔ 0 ≤ i := by
  refine ⟨fun h => not_lt.1 fun hi => ?_, fun h => le_away (A O K) _ (Ezpow_mem_A h)⟩
  have h0 : Ezpow K l e (-1 - i) ∈ invL l (A O K) := le_away _ _ (Ezpow_mem_A (by omega))
  have h1 := mul_mem h0 h
  rw [← Ezpow_add, sub_add_cancel] at h1
  have h2 : E K l e * Ezpow K l e (-1) = 1 := by simpa using E_pow_mul_Ezpow_neg (K := K) l e 1
  have h3 : Ezpow K l e (-1) = 0 := eq_zero_of_E_mul l e (invL_A_le_Rpi l e h1) fun n => by
    rw [h2, coeff_one, if_neg (by have := NeZero.pos e; omega)]
  exact Units.ne_zero _ h3
end GlobalTheory.BK
