-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.comaximal_contacts_exclusive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:30:52.398549+00:00
-- url     : https://prove2.me/submissions/3d33bc8e-d52c-4c0c-b0b9-b2227ce2cb9a

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
    (hbranch : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hcop : ∀ j k : Fin K, j ≠ k → IsCoprime (I j) (I k)) :
    ∀ j k : Fin K, j ≠ k →
      ¬ (0 < polynomialCurveIdealContact nu x (I j) ∧
         0 < polynomialCurveIdealContact nu x (I k)) := by
  rintro j k hjk ⟨hj, hk⟩
  have hx := hbranch
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
    ((Ideal.isCoprime_iff_sup_eq.mp (hcop j k hjk)).symm ▸ Submodule.mem_top :
      (1 : MvPolynomial (Fin d) Complex) ∈ I j ⊔ I k)
  have h1 : ((1 : Int) : WithTop Int) ≤ nu.1 (MvPolynomial.aeval x a) :=
    le_trans (by exact_mod_cast hj) (contact_le nu x hx (I j) a ha)
  have h2 : ((1 : Int) : WithTop Int) ≤ nu.1 (MvPolynomial.aeval x b) :=
    le_trans (by exact_mod_cast hk) (contact_le nu x hx (I k) b hb)
  have h3 := AddValuation.map_le_add nu.1 h1 h2
  rw [← map_add, hab, map_one, AddValuation.map_one] at h3
  exact absurd h3 (by decide)
