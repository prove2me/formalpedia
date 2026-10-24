-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurveIdealContact_finset_product_of_pairwise_eq_or_comaximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:21:29.119123+00:00
-- url     : https://prove2.me/submissions/4bdc09a2-4f40-4998-b478-4dbd7591e3bb

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib

section

open OAI.PiExponent.FormalInterpolation

namespace PiL30

variable {E : Type} [Field E] [Algebra Complex E] {d : ℕ}

lemma val_C (nu : PolynomialCurvePlace E) (a : ℂ) : 0 ≤ nu.1 (algebraMap ℂ E a) := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [nu.2.1 a ha]

lemma val_nonneg (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) (f : MvPolynomial (Fin d) ℂ) :
    0 ≤ nu.1 (MvPolynomial.aeval x f) := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C]; exact val_C nu a
  | add p q hp hq =>
    rw [map_add]
    exact le_trans (le_min hp hq) (AddValuation.map_add _ _ _)
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.aeval_X, AddValuation.map_mul]
    exact add_nonneg hp (hchart i)

/-- value as a natural number when nonzero -/
lemma val_eq (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) (f : MvPolynomial (Fin d) ℂ)
    (hf : MvPolynomial.aeval x f ≠ 0) :
    ∃ n : ℕ, nu.1 (MvPolynomial.aeval x f) = ((n : ℤ) : WithTop ℤ) := by
  have h0 := val_nonneg nu x hchart f
  have htop : nu.1 (MvPolynomial.aeval x f) ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 htop
  have hk0 : 0 ≤ k := by rw [← hk] at h0; exact_mod_cast h0
  exact ⟨k.toNat, by rw [← hk, Int.toNat_of_nonneg hk0]⟩

def Dead (x : Fin d → E) (I : Ideal (MvPolynomial (Fin d) Complex)) : Prop :=
  ∀ f ∈ I, MvPolynomial.aeval x f = 0

lemma contact_chart (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) (I : Ideal (MvPolynomial (Fin d) Complex)) :
    polynomialCurveIdealContact nu x I = sInf {k : Nat | ∃ f : MvPolynomial (Fin d) Complex,
      f ∈ I ∧ nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)} := by
  classical
  unfold polynomialCurveIdealContact
  rw [if_pos hchart]

lemma contact_nochart (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hchart : ¬ ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) (I : Ideal (MvPolynomial (Fin d) Complex)) :
    polynomialCurveIdealContact nu x I = 0 := by
  classical
  unfold polynomialCurveIdealContact
  rw [if_neg hchart]

lemma lb (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) (I : Ideal (MvPolynomial (Fin d) Complex))
    (f : MvPolynomial (Fin d) ℂ) (hf : f ∈ I) :
    (((polynomialCurveIdealContact nu x I : ℕ) : ℤ) : WithTop ℤ) ≤ nu.1 (MvPolynomial.aeval x f) := by
  by_cases h0 : MvPolynomial.aeval x f = 0
  · rw [h0, AddValuation.map_zero]; exact le_top
  · obtain ⟨n, hn⟩ := val_eq nu x hchart f h0
    rw [hn]
    have : polynomialCurveIdealContact nu x I ≤ n := by
      rw [contact_chart nu x hchart]
      exact Nat.sInf_le ⟨f, hf, hn⟩
    exact_mod_cast this

lemma attained (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) (I : Ideal (MvPolynomial (Fin d) Complex))
    (hI : ¬ Dead x I) :
    ∃ f ∈ I, nu.1 (MvPolynomial.aeval x f) = (((polynomialCurveIdealContact nu x I : ℕ) : ℤ) : WithTop ℤ) := by
  unfold Dead at hI; push_neg at hI
  obtain ⟨f, hf, hne⟩ := hI
  obtain ⟨n, hn⟩ := val_eq nu x hchart f hne
  rw [contact_chart nu x hchart]
  have hmem := Nat.sInf_mem (s := {k : Nat | ∃ f : MvPolynomial (Fin d) Complex,
      f ∈ I ∧ nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)}) ⟨n, f, hf, hn⟩
  obtain ⟨g, hg, hgv⟩ := hmem
  exact ⟨g, hg, hgv⟩

lemma dead_contact (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Ideal (MvPolynomial (Fin d) Complex)) (hI : Dead x I) :
    polynomialCurveIdealContact nu x I = 0 := by
  by_cases hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)
  · rw [contact_chart nu x hchart]
    convert Nat.sInf_empty
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro f hf hv
    rw [hI f hf, AddValuation.map_zero] at hv
    exact WithTop.top_ne_coe hv
  · exact contact_nochart nu x hchart I

lemma comax_contact (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I J : Ideal (MvPolynomial (Fin d) Complex)) (hI : Dead x I) (hIJ : I ⊔ J = ⊤) :
    polynomialCurveIdealContact nu x J = 0 := by
  by_cases hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)
  · have h1 : (1 : MvPolynomial (Fin d) ℂ) ∈ I ⊔ J := hIJ ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    have hb1 : MvPolynomial.aeval x b = 1 := by
      have := congrArg (MvPolynomial.aeval x) hab
      rw [map_add, hI a ha, zero_add, map_one] at this
      exact this
    have := lb nu x hchart J b hb
    rw [hb1, AddValuation.map_one] at this
    exact_mod_cast le_antisymm (by exact_mod_cast this) (Nat.zero_le _)
  · exact contact_nochart nu x hchart J

lemma mul_contact (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (I J : Ideal (MvPolynomial (Fin d) Complex)) (hI : ¬ Dead x I) (hJ : ¬ Dead x J) :
    polynomialCurveIdealContact nu x (I * J) =
      polynomialCurveIdealContact nu x I + polynomialCurveIdealContact nu x J := by
  obtain ⟨f, hf, hfv⟩ := attained nu x hchart I hI
  obtain ⟨g, hg, hgv⟩ := attained nu x hchart J hJ
  set cI := polynomialCurveIdealContact nu x I
  set cJ := polynomialCurveIdealContact nu x J
  have hfg : nu.1 (MvPolynomial.aeval x (f * g)) = (((cI + cJ : ℕ) : ℤ) : WithTop ℤ) := by
    rw [map_mul, AddValuation.map_mul, hfv, hgv]; push_cast; rfl
  have hlow : ∀ h ∈ I * J, (((cI + cJ : ℕ) : ℤ) : WithTop ℤ) ≤ nu.1 (MvPolynomial.aeval x h) := by
    intro h hh
    refine Submodule.mul_induction_on hh ?_ ?_
    · intro a ha b hb
      rw [map_mul, AddValuation.map_mul]
      have := add_le_add (lb nu x hchart I a ha) (lb nu x hchart J b hb)
      refine le_trans (le_of_eq ?_) this
      push_cast; rfl
    · intro a b ha hb
      rw [map_add]
      exact le_trans (le_min ha hb) (AddValuation.map_add _ _ _)
  rw [contact_chart nu x hchart]
  apply le_antisymm
  · exact Nat.sInf_le ⟨f * g, Ideal.mul_mem_mul hf hg, hfg⟩
  · obtain ⟨h, hh, hk⟩ := Nat.sInf_mem (s := {k : Nat | ∃ f : MvPolynomial (Fin d) Complex,
      f ∈ I * J ∧ nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)})
      ⟨cI + cJ, f * g, Ideal.mul_mem_mul hf hg, hfg⟩
    have := hlow h hh
    rw [hk] at this
    exact_mod_cast this

lemma not_dead_mul (x : Fin d → E) (I J : Ideal (MvPolynomial (Fin d) Complex))
    (hI : ¬ Dead x I) (hJ : ¬ Dead x J) : ¬ Dead x (I * J) := by
  unfold Dead at *; push_neg at *
  obtain ⟨f, hf, hf0⟩ := hI
  obtain ⟨g, hg, hg0⟩ := hJ
  exact ⟨f * g, Ideal.mul_mem_mul hf hg, by rw [map_mul]; exact mul_ne_zero hf0 hg0⟩

lemma not_dead_top (x : Fin d → E) : ¬ Dead x (⊤ : Ideal (MvPolynomial (Fin d) Complex)) := by
  intro h
  have := h 1 Submodule.mem_top
  simp at this

lemma prod_alive (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) {K : ℕ}
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex)) (S : Finset (Fin K))
    (hS : ∀ j ∈ S, ¬ Dead x (I j)) :
    ¬ Dead x (∏ j ∈ S, I j) ∧ polynomialCurveIdealContact nu x (∏ j ∈ S, I j) =
      ∑ j ∈ S, polynomialCurveIdealContact nu x (I j) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, Ideal.one_eq_top]
    refine ⟨not_dead_top x, ?_⟩
    rw [contact_chart nu x hchart]
    apply Nat.eq_zero_of_le_zero
    apply Nat.sInf_le
    exact ⟨1, Submodule.mem_top, by simp⟩
  | insert a S ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
    have hA := hS a (Finset.mem_insert_self a S)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨not_dead_mul x _ _ hA h1, by rw [mul_contact nu x hchart _ _ hA h1, h2]⟩

theorem main {d K : Nat} (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (S : Finset (Fin K))
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex))
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      I i = I j ∨ I i ⊔ I j = ⊤) :
    polynomialCurveIdealContact nu x (∏ j ∈ S, I j) =
      ∑ j ∈ S, polynomialCurveIdealContact nu x (I j) := by
  classical
  by_cases hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)
  · by_cases hdead : ∃ k ∈ S, Dead x (I k)
    · obtain ⟨k, hk, hkd⟩ := hdead
      have hall : ∀ j ∈ S, polynomialCurveIdealContact nu x (I j) = 0 := by
        intro j hj
        by_cases hjk : k = j
        · subst hjk; exact dead_contact nu x _ hkd
        · rcases hpair k hk j hj hjk with h | h
          · rw [← h]; exact dead_contact nu x _ hkd
          · exact comax_contact nu x _ _ hkd h
      rw [Finset.sum_eq_zero hall]
      apply dead_contact
      intro f hf
      apply hkd
      exact Ideal.prod_le_inf.trans (Finset.inf_le hk) hf
    · push_neg at hdead
      exact (prod_alive nu x hchart I S hdead).2
  · rw [contact_nochart nu x hchart]
    symm
    exact Finset.sum_eq_zero fun j _ => contact_nochart nu x hchart _

end PiL30

end

open OAI OAI.PiExponent OAI.PiExponent.FormalInterpolation

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d K : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (S : Finset (Fin K))
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex))
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      I i = I j ∨ I i ⊔ I j = ⊤) :
    polynomialCurveIdealContact nu x (∏ j ∈ S, I j) =
      ∑ j ∈ S, polynomialCurveIdealContact nu x (I j) := by
  apply PiL30.main <;> assumption
