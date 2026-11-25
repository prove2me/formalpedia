-- Prove2me | solution 1 for GlobalTheory.BadShare.SqCount.sq_mul_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:59:40.910447+00:00
-- url     : https://prove2.me/submissions/8f3a13d7-6962-4c6e-8059-9ffa73f5f721

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.SqCount
namespace GlobalTheory.BadShare.SqCount
theorem _root_.solution {k : Type} [Field k] {a b c d : k[X]} (ha : a.Monic) (hc : c.Monic)
    (hb : Squarefree b) (hd : Squarefree d) (h : a ^ 2 * b = c ^ 2 * d) : a = c ∧ b = d := by
  obtain ⟨a1, c1, e, hco, rfl, rfl⟩ : ∃ a1 c1 e : k[X], IsCoprime a1 c1 ∧ a = e * a1 ∧ c = e * c1 := by
    obtain ⟨a1, c1, h1, h2, h3⟩ := extract_gcd a c
    exact ⟨a1, c1, GCDMonoid.gcd a c, (gcd_isUnit_iff _ _).1 h3, h1, h2⟩
  have he : e ≠ 0 := left_ne_zero_of_mul ha.ne_zero
  have h' : a1 ^ 2 * b = c1 ^ 2 * d := by
    apply mul_left_cancel₀ (pow_ne_zero 2 he)
    linear_combination h
  have u1 : IsUnit a1 := by
    apply hd
    rw [← sq]
    exact (hco.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left ⟨b, h'.symm⟩
  have u2 : IsUnit c1 := by
    apply hb
    rw [← sq]
    exact (hco.symm.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left ⟨d, h'⟩
  have hac : e * a1 = e * c1 :=
    eq_of_monic_of_associated ha hc ((associated_mul_unit_left e a1 u1).trans (associated_mul_unit_left e c1 u2).symm)
  refine ⟨hac, ?_⟩
  rw [hac] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 hc.ne_zero) h
end GlobalTheory.BadShare.SqCount
