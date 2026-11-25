-- Prove2me | solution 1 for GlobalTheory.Nef.RatDilation.natDegree_eq_zero_of_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:52.082836+00:00
-- url     : https://prove2.me/submissions/799ea03f-afdd-4ec8-809b-f56f527ee0f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeEqZeroOfSqDvd
import Theorems.Thm_GlobalTheory_Nef_RatDilation_natDegree_comp_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open Polynomial
open GlobalTheory.Nef.RatDilation
namespace GlobalTheory.Nef.RatDilation
theorem _root_.solution {F : Type} [Field F] [CharZero F] (f g : F[X]) (hf : f ≠ 0)
    (hc : IsCoprime f g) (h : f.comp (C (2:F) * X) * g ^ 2 = g.comp (C (2:F) * X) * f ^ 2) :
    f.natDegree = 0 := by
  have hd : f ^ 2 ∣ f.comp (C (2:F) * X) := by
    have : f ^ 2 ∣ f.comp (C (2:F) * X) * g ^ 2 := h ▸ dvd_mul_left _ _
    exact (hc.pow).dvd_of_dvd_mul_right this
  have hne : f.comp (C (2:F) * X) ≠ 0 := by
    intro h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨_, h0⟩
    · exact hf h0
    · have := congrArg natDegree h0
      rw [natDegree_C_mul_X _ two_ne_zero, natDegree_C] at this
      exact one_ne_zero this
  have := natDegree_le_of_dvd hd hne
  rw [natDegree_comp_two, natDegree_pow] at this
  omega
end GlobalTheory.Nef.RatDilation
