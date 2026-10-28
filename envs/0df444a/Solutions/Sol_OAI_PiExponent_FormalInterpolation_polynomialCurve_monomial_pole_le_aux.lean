-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurve_monomial_pole_le_aux
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:31:57.353197+00:00
-- url     : https://prove2.me/submissions/0d916376-cef8-4a46-8b11-932449714ba3

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.Algebra.BigOperators.WithTop

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

namespace S38PL

variable {E : Type} [Field E] [Algebra Complex E]

lemma le_val_sum {ι : Type} (nu : PolynomialCurvePlace E) (s : Finset ι) (t : ι → E)
    (g : WithTop Int) (h : ∀ a ∈ s, g ≤ nu.1 (t a)) : g ≤ nu.1 (∑ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddValuation.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact AddValuation.map_le_add _ (h a (Finset.mem_insert_self a s))
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

lemma val_prod {ι : Type} (nu : PolynomialCurvePlace E) (s : Finset ι) (g : ι → E) :
    nu.1 (∏ j ∈ s, g j) = ∑ j ∈ s, nu.1 (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddValuation.map_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

lemma pow_bound (nu : PolynomialCurvePlace E) (y : E) (n : Nat) :
    (((n : Int) * polynomialCurveOrder nu y : Int) : WithTop Int) ≤ nu.1 (y ^ n) := by
  rw [AddValuation.map_pow]
  unfold polynomialCurveOrder
  generalize nu.1 y = v
  induction v using WithTop.recTopCoe with
  | top =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
      rw [succ_nsmul, WithTop.add_top]; exact le_top
  | coe z =>
    rw [WithTop.untop₀_coe, ← WithTop.coe_nsmul]
    exact_mod_cast le_of_eq (by simp [nsmul_eq_mul])

end S38PL

open S38PL in
theorem plMain
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E)
    (x : Fin d → E) (w : Fin d → Rat)
    (hw : ∀ i, 0 < (w i : Real))
    (N : Nat) (P : MvPolynomial (Fin d) Complex)
    (hP : fibreContactSupportBound w N P) :
    max 0 (-(polynomialCurveOrder nu (MvPolynomial.aeval x P) : Real)) ≤
      (N : Real) * polynomialCurvePole nu x w := by
  classical
  set pole := polynomialCurvePole nu x w with hpole
  have hpole0 : 0 ≤ pole := by
    have := Finset.le_sup' (fun i : Option (Fin d) => i.elim 0 (fun j =>
      -(polynomialCurveOrder nu (x j) : Real) / (w j : Real))) (Finset.mem_univ none)
    rw [hpole, polynomialCurvePole]; exact this
  have hpi : ∀ i, -(polynomialCurveOrder nu (x i) : Real) ≤ (w i : Real) * pole := by
    intro i
    have := Finset.le_sup' (fun i : Option (Fin d) => i.elim 0 (fun j =>
      -(polynomialCurveOrder nu (x j) : Real) / (w j : Real))) (Finset.mem_univ (some i))
    have h2 : -(polynomialCurveOrder nu (x i) : Real) / (w i : Real) ≤ pole := by
      rw [hpole, polynomialCurvePole]; exact this
    rw [div_le_iff₀ (hw i)] at h2; linarith
  -- integer lower bound per monomial
  set s : (Fin d →₀ Nat) → Int := fun a => ∑ i, (a i : Int) * polynomialCurveOrder nu (x i)
    with hs
  have hsR : ∀ a ∈ P.support, -((s a : Int) : Real) ≤ (N : Real) * pole := by
    intro a ha
    have hb := hP a ha
    simp only [hs]; push_cast
    rw [← Finset.sum_neg_distrib]
    calc ∑ i, -((a i : Real) * (polynomialCurveOrder nu (x i) : Real))
        ≤ ∑ i, (a i : Real) * ((w i : Real) * pole) := by
          apply Finset.sum_le_sum; intro i _
          have := hpi i
          have ha0 : (0 : Real) ≤ a i := Nat.cast_nonneg _
          nlinarith
      _ = (∑ i, (a i : Real) * (w i : Real)) * pole := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ (N : Real) * pole := mul_le_mul_of_nonneg_right hb hpole0
  by_cases hP0 : P.support = ∅
  · have : P = 0 := MvPolynomial.support_eq_empty.mp hP0
    subst this
    simp [polynomialCurveOrder, AddValuation.map_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hpole0
  have hne : P.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
  set m : Int := P.support.inf' hne s with hm
  have hval : ((m : Int) : WithTop Int) ≤ nu.1 (MvPolynomial.aeval x P) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    apply le_val_sum
    intro a ha
    rw [AddValuation.map_mul, nu.2.1 _ (MvPolynomial.mem_support_iff.mp ha), zero_add,
      val_prod]
    have h1 : ((m : Int) : WithTop Int) ≤ ((s a : Int) : WithTop Int) :=
      WithTop.coe_le_coe.mpr (Finset.inf'_le _ ha)
    refine h1.trans ?_
    simp only [hs]; rw [WithTop.coe_sum]
    exact Finset.sum_le_sum (fun i _ => pow_bound nu (x i) (a i))
  have hm' : -((m : Int) : Real) ≤ (N : Real) * pole := by
    obtain ⟨a, ha, hma⟩ := Finset.exists_mem_eq_inf' hne s
    rw [hm, hma]; exact hsR a ha
  apply max_le (mul_nonneg (Nat.cast_nonneg _) hpole0)
  unfold polynomialCurveOrder
  generalize hv : nu.1 (MvPolynomial.aeval x P) = v at hval
  induction v using WithTop.recTopCoe with
  | top => simp; exact mul_nonneg (Nat.cast_nonneg _) hpole0
  | coe z =>
    rw [WithTop.untop₀_coe]
    have : m ≤ z := WithTop.coe_le_coe.mp hval
    have : (m : Real) ≤ z := by exact_mod_cast this
    linarith

theorem solution
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E) (w : Fin d → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (N : Nat)
    (a : Fin d →₀ Nat)
    (hdeg : (∑ i : Fin d, (a i : Real) * (w i : Real)) ≤ (N : Real)) :
    max 0 (-(polynomialCurveOrder nu
      (MvPolynomial.aeval x (MvPolynomial.monomial a (1 : Complex))) : Real)) ≤
      (N : Real) * polynomialCurvePole nu x w := by
  apply plMain nu x w hw N
  intro b hb
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hb
  subst hb; exact hdeg
