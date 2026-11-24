-- Prove2me | solution 1 for GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:48.785802+00:00
-- url     : https://prove2.me/submissions/9ce6dce3-5a33-4b0c-9958-c4e0fa833d0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialIdealEqBotOfPderivStableNoConstants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial Finsupp
namespace GlobalTheory
theorem _root_.solution :
    ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) R)),
  (∀ P ∈ I, ∀ i, MvPolynomial.pderiv i P ∈ I) → (∀ a : R, MvPolynomial.C a ∈ I → a = 0) → I = ⊥ := by
  intro R _ _ _ r I hI hC
  have key : ∀ n : ℕ, ∀ P ∈ I, P.totalDegree = n → P = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro P hP h
    by_contra hne
    by_cases hn : n = 0
    · subst hn
      rw [totalDegree_eq_zero_iff_eq_C] at h
      apply hne
      rw [h] at hP ⊢
      rw [hC _ hP, C_0]
    · obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hne)
        (fun s => s.sum fun _ e => e)
      have hdeg : (m.sum fun _ e => e) = n := by rw [← h, totalDegree, hmd]
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have hm0 : m = 0 := Finsupp.ext hcon
        subst hm0
        simp at hdeg
        omega
      have hQ : pderiv i P ∈ I := hI P hP i
      have hQne : pderiv i P ≠ 0 := by
        intro h0
        have hc := coeff_pderiv (i := i) P (m - single i 1)
        rw [h0, coeff_zero, sub_add_single_one_cancel hi] at hc
        have hcm : coeff m P ≠ 0 := MvPolynomial.mem_support_iff.mp hm
        have hk : (((m - single i 1 : Fin r →₀ ℕ) i : ℕ) : R) + 1 ≠ 0 :=
          Nat.cast_add_one_ne_zero _
        exact (mul_ne_zero hcm hk) hc.symm
      have hlt : (pderiv i P).totalDegree < n := by
        have hle : (pderiv i P).totalDegree ≤ n - 1 := by
          apply Finset.sup_le
          intro s hs
          have hs' := MvPolynomial.mem_support_iff.mp hs
          rw [coeff_pderiv] at hs'
          have hsupp : s + single i 1 ∈ P.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hs')
          have hd := le_totalDegree hsupp
          rw [Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_single_index rfl, h] at hd
          omega
        omega
      exact hQne (ih _ hlt _ hQ rfl)
  rw [eq_bot_iff]
  intro P hP
  rw [Ideal.mem_bot]
  exact key _ P hP rfl
end GlobalTheory
