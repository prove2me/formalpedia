-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.fischer_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:56:53.440767+00:00
-- url     : https://prove2.me/submissions/c8e99554-25a1-4285-a91e-937debebeff8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mfact_add_single
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_add_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_add_right
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_monomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_left
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_right

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {σ : Type*}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (a : σ) (f g : MvPolynomial σ ℂ) :
    fischer (X a * f) g = fischer f (pderiv a g) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, fischer_add_left, fischer_add_left, hp, hq]
  | monomial s c =>
    induction g using MvPolynomial.induction_on' with
    | add p q hp hq => rw [fischer_add_right, map_add, fischer_add_right, hp, hq]
    | monomial t d =>
      rw [X, monomial_mul, one_mul, pderiv_monomial, fischer_monomial, fischer_monomial]
      by_cases ht : t a = 0
      · have hne : Finsupp.single a 1 + s ≠ t := by
          intro h
          have := congrArg (fun m => m a) h
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
          omega
        rw [if_neg hne]
        split_ifs <;> simp [ht]
      · have hle : Finsupp.single a 1 ≤ t := by
          intro v
          by_cases hv : v = a
          · subst hv; simp only [Finsupp.single_eq_same]; omega
          · rw [Finsupp.single_apply, if_neg (Ne.symm hv)]; exact Nat.zero_le _
        have hiff : Finsupp.single a 1 + s = t ↔ s = t - Finsupp.single a 1 := by
          constructor
          · rintro rfl; simp
          · rintro rfl; rw [add_comm]; exact tsub_add_cancel_of_le hle
        by_cases h : s = t - Finsupp.single a 1
        · have h' := hiff.2 h
          rw [if_pos h', if_pos h]
          have hsa : (s a + 1 : ℕ) = t a := by
            rw [← h']; simp [add_comm]
          rw [add_comm (Finsupp.single a 1) s, mfact_add_single, ← hsa]
          push_cast
          ring
        · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
end GroundTheory.Automorphic.HarishChandra
