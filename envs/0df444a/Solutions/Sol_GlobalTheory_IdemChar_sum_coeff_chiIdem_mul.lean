-- Prove2me | solution 1 for GlobalTheory.IdemChar.sum_coeff_chiIdem_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:05.803325+00:00
-- url     : https://prove2.me/submissions/0eb66299-b12a-4260-a1d6-e996d3c1074c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumCoeffChiIdemMul
import Theorems.Thm_Formalism_L2_DIV_coeff_chiIdem
import Theorems.Thm_Formalism_L2_DIV_conv_char


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.DIV
open GlobalTheory GlobalTheory.IdemChar
open Classical
namespace GlobalTheory.IdemChar
theorem _root_.solution {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
    {φ χ : G → K} (hφ : IsAbsIrrChar φ) (hχ : IsAbsIrrChar χ) :
    ∑ g : G, (chiIdem φ).coeff g * χ g = if φ = χ then χ 1 else 0 := by
  have hG : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

  have hc := conv_char hχ hφ 1
  have hre : ∑ s : G, χ s⁻¹ * φ (s * 1) = ∑ g : G, φ g⁻¹ * χ g :=
    Fintype.sum_equiv (Equiv.inv G) _ _ (fun s => by simp [mul_comm])
  rw [hre] at hc
  have hsum : ∑ g : G, (chiIdem φ).coeff g * χ g
      = ((∑ g : G, φ g⁻¹ * χ g) * φ 1) / (Fintype.card G : K) := by
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [coeff_chiIdem]
    ring
  rw [hsum, hc]
  by_cases h : φ = χ
  · subst h
    rw [if_pos rfl, if_pos rfl, mul_div_cancel_left₀ _ hG]
  · have h' : ¬ χ = φ := fun e => h e.symm
    rw [if_neg h', if_neg h, zero_div]
end GlobalTheory.IdemChar
