-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.LocIn.inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:48.907338+00:00
-- url     : https://prove2.me/submissions/fd76e00a-b728-4c02-9939-5e0019b4b3e9

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Theorems.Thm_GlobalTheory_CMVal_Euler_iota_mul
import Theorems.Thm_GlobalTheory_CMVal_Euler_iota_add
import Theorems.Thm_GlobalTheory_CMVal_Euler_iota_one
import Theorems.Thm_GlobalTheory_CMVal_Euler_mul_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_add_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_one_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_inv_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_val_iota_le_one
import Theorems.Thm_GlobalTheory_CMVal_Euler_val_iota_le_of_mem
import Theorems.Thm_GlobalTheory_CMVal_Euler_locIn_zero_iff
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
namespace LocIn
theorem _root_.solution {n : ℕ} {v : HeightOneSpectrum (OF E)} {y : (Af E)ˣ} (h : LocIn n v y)
    (hu : ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) : LocIn n v (y⁻¹ : (Af E)ˣ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact locIn_zero_iff.2 fun P hP => by rw [inv_coord, map_inv₀, hu P hP, inv_one]
  obtain ⟨a, ha⟩ := h
  by_cases hav : a ∈ v.asIdeal
  · refine ⟨0, fun P hP => absurd (hu P hP) (ne_of_lt ?_)⟩
    have h1 := val_iota_le_of_mem hP 1 (a := a) (by simpa using hav)
    have h2 := (ha P hP).trans (WithZero.exp_le_exp.2 (show -(n : ℤ) ≤ -((1 : ℕ) : ℤ) by omega))
    have := Valuation.map_add_le _ h2 h1
    rw [sub_add_cancel] at this
    refine this.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hco : IsCoprime (Ideal.span {a}) (v.asIdeal ^ n) := by
    refine IsCoprime.pow_right ?_
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
    exact v.isMaximal.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hav (h.ge (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))))
  obtain ⟨s, hs, t, ht, hst⟩ := Ideal.isCoprime_iff_exists.1 hco
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hs
  refine ⟨b, fun P hP => ?_⟩
  have h0 : (y : Af E) P ≠ 0 := (coord P y).ne_zero
  have h1 : iota b P * iota a P + iota t P = 1 := by
    rw [← mul_coord, ← add_coord, ← iota_mul, ← iota_add, hst, iota_one, one_coord]
  have : ((y⁻¹ : (Af E)ˣ) : Af E) P - iota b P =
      ((y : Af E) P)⁻¹ * (iota t P - iota b P * ((y : Af E) P - iota a P)) := by
    rw [inv_coord]; field_simp; linear_combination -h1
  rw [this, map_mul, map_inv₀, hu P hP, inv_one, one_mul]
  refine Valuation.map_sub_le _ (val_iota_le_of_mem hP n ht) ?_
  rw [map_mul]; exact (mul_le_mul' (val_iota_le_one P b) (ha P hP)).trans_eq (one_mul _)
end LocIn
end GlobalTheory.CMVal.Euler
