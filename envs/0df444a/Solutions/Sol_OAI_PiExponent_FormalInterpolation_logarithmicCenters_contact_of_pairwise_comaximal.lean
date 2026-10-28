-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCenters_contact_of_pairwise_comaximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:26:51.766744+00:00
-- url     : https://prove2.me/submissions/57e4c7ee-cc6c-4aba-9f21-5176fabf3e04

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

namespace S38CC

variable {E : Type} [Field E] [Algebra Complex E]

lemma nonneg_aeval {d : Nat} (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hx : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) (f : MvPolynomial (Fin d) Complex) :
    (0 : WithTop Int) ≤ nu.1 (MvPolynomial.aeval x f) := by
  induction f using MvPolynomial.induction_on with
  | C b =>
    rw [MvPolynomial.aeval_C]
    by_cases hb : b = 0
    · subst hb; simp
    · rw [nu.2.1 b hb]
  | add p q hp hq =>
    rw [map_add]; exact AddValuation.map_le_add _ hp hq
  | mul_X p i hp =>
    rw [map_mul, AddValuation.map_mul, MvPolynomial.aeval_X]
    exact add_nonneg hp (hx i)

lemma val_prod {ι : Type} (nu : PolynomialCurvePlace E) (s : Finset ι) (g : ι → E) :
    nu.1 (∏ j ∈ s, g j) = ∑ j ∈ s, nu.1 (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddValuation.map_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

lemma contact_eq {d : Nat} (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hx : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) (I : Ideal (MvPolynomial (Fin d) Complex)) :
    polynomialCurveIdealContact nu x I = sInf {k : Nat | ∃ f : MvPolynomial (Fin d) Complex,
      f ∈ I ∧ nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)} := by
  unfold polynomialCurveIdealContact
  rw [if_pos hx]

lemma contact_le {d : Nat} (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hx : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) (I : Ideal (MvPolynomial (Fin d) Complex))
    (f : MvPolynomial (Fin d) Complex) (hf : f ∈ I) :
    (((polynomialCurveIdealContact nu x I : Nat) : Int) : WithTop Int) ≤
      nu.1 (MvPolynomial.aeval x f) := by
  have h0 := nonneg_aeval nu x hx f
  generalize hv : nu.1 (MvPolynomial.aeval x f) = v at h0
  induction v using WithTop.recTopCoe with
  | top => exact le_top
  | coe z =>
    have hz : 0 ≤ z := by exact_mod_cast h0
    lift z to Nat using hz
    rw [contact_eq nu x hx]
    have : sInf {k : Nat | ∃ f : MvPolynomial (Fin d) Complex,
      f ∈ I ∧ nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)} ≤ z :=
      Nat.sInf_le ⟨f, hf, hv⟩
    exact_mod_cast this

end S38CC

open S38CC in
theorem solution
    {K d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex))
    (hcop : ∀ j k : Fin K, j ≠ k → IsCoprime (I j) (I k))
    (hcontact : 0 < (polynomialCurveIdealContact nu x (∏ j, I j) : Real)) :
    ∃ j : Fin K,
      0 < (polynomialCurveIdealContact nu x (I j) : Real) ∧
      (polynomialCurveIdealContact nu x (I j) : Real) =
        (polynomialCurveIdealContact nu x (∏ j, I j) : Real) := by
  classical
  have hx : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i) := by
    by_contra h
    have : polynomialCurveIdealContact nu x (∏ j, I j) = 0 := by
      unfold polynomialCurveIdealContact; rw [if_neg h]
    rw [this] at hcontact; simp at hcontact
  set S : Ideal (MvPolynomial (Fin d) Complex) → Set Nat := fun J =>
    {k : Nat | ∃ f : MvPolynomial (Fin d) Complex,
      f ∈ J ∧ nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)} with hS
  have hcP : 0 < polynomialCurveIdealContact nu x (∏ j, I j) := by exact_mod_cast hcontact
  have hne : (S (∏ j, I j)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [contact_eq nu x hx] at hcP
    have : sInf (S (∏ j, I j)) = 0 := by rw [h]; exact Nat.sInf_empty
    simp only [hS] at this; omega
  have hle : ∀ j, (∏ j, I j) ≤ I j := fun j =>
    (Ideal.prod_le_inf).trans (Finset.inf_le (Finset.mem_univ j))
  have hneJ : ∀ j, (S (I j)).Nonempty := by
    intro j
    obtain ⟨k, f, hf, hv⟩ := hne
    exact ⟨k, f, hle j hf, hv⟩
  -- minimizers
  have hmin : ∀ j, ∃ f ∈ I j, nu.1 (MvPolynomial.aeval x f) =
      (((polynomialCurveIdealContact nu x (I j) : Nat) : Int) : WithTop Int) := by
    intro j
    rw [contact_eq nu x hx]
    exact Nat.sInf_mem (hneJ j)
  choose f hfI hfv using hmin
  set c : Fin K → Nat := fun j => polynomialCurveIdealContact nu x (I j) with hc
  -- at most one positive
  have huniq : ∀ j k, j ≠ k → 0 < c j → c k = 0 := by
    intro j k hjk hj
    by_contra hk
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      ((Ideal.isCoprime_iff_sup_eq.mp (hcop j k hjk)).symm ▸ Submodule.mem_top :
        (1 : MvPolynomial (Fin d) Complex) ∈ I j ⊔ I k)
    have h1 : ((1 : Int) : WithTop Int) ≤ nu.1 (MvPolynomial.aeval x a) :=
      le_trans (by exact_mod_cast hj) (contact_le nu x hx (I j) a ha)
    have h2 : ((1 : Int) : WithTop Int) ≤ nu.1 (MvPolynomial.aeval x b) :=
      le_trans (by exact_mod_cast (Nat.pos_of_ne_zero hk)) (contact_le nu x hx (I k) b hb)
    have h3 := AddValuation.map_le_add nu.1 h1 h2
    rw [← map_add, hab, map_one, AddValuation.map_one] at h3
    exact absurd h3 (by decide)
  -- upper bound on product contact
  have hprod_mem : (∏ j, f j) ∈ ∏ j, I j := Ideal.prod_mem_prod (fun j _ => hfI j)
  have hup : polynomialCurveIdealContact nu x (∏ j, I j) ≤ ∑ j, c j := by
    rw [contact_eq nu x hx]
    apply Nat.sInf_le
    refine ⟨∏ j, f j, hprod_mem, ?_⟩
    rw [map_prod, val_prod, Finset.sum_congr rfl (fun j _ => hfv j)]
    push_cast; rfl
  obtain ⟨j0, hj0⟩ : ∃ j0, 0 < c j0 := by
    by_contra h; push_neg at h
    have : ∑ j, c j = 0 := Finset.sum_eq_zero (fun j _ => by have := h j; omega)
    omega
  have hsum : ∑ j, c j = c j0 :=
    Finset.sum_eq_single j0 (fun k _ hk => huniq j0 k (Ne.symm hk) hj0) (by simp)
  have hlow : c j0 ≤ polynomialCurveIdealContact nu x (∏ j, I j) := by
    simp only [hc]
    rw [contact_eq nu x hx, contact_eq nu x hx]
    apply csInf_le_csInf (OrderBot.bddBelow _) hne
    rintro k ⟨g, hg, hv⟩
    exact ⟨g, hle j0 hg, hv⟩
  refine ⟨j0, by exact_mod_cast hj0, ?_⟩
  have : c j0 = polynomialCurveIdealContact nu x (∏ j, I j) := by omega
  exact_mod_cast this
