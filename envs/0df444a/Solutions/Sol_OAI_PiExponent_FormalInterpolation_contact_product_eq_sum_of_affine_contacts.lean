-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.contact_product_eq_sum_of_affine_contacts
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:36:15.074972+00:00
-- url     : https://prove2.me/submissions/5e8721b0-a54c-4af6-8fb7-bfbc321e5b2e

import Mathlib
import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

namespace S38DS

abbrev LS := HahnSeries ℤ ℂ

noncomputable def place : PolynomialCurvePlace LS :=
  ⟨HahnSeries.addVal ℤ ℂ, by
    intro b hb
    have hC : (algebraMap ℂ LS b) = HahnSeries.C b := by
      rw [HahnSeries.algebraMap_apply']; simp
    rw [hC, HahnSeries.addVal_apply_of_ne (HahnSeries.C_ne_zero hb), HahnSeries.order_C]
    rfl,
   by
    intro k
    refine ⟨HahnSeries.single k 1, ?_⟩
    rw [HahnSeries.addVal_apply, HahnSeries.orderTop_single one_ne_zero]⟩

noncomputable def T : LS := HahnSeries.single 1 1

lemma val_T : place.1 T = ((1 : Int) : WithTop Int) := by
  show HahnSeries.addVal ℤ ℂ (HahnSeries.single 1 1) = _
  rw [HahnSeries.addVal_apply, HahnSeries.orderTop_single one_ne_zero]

lemma nonneg_aeval (x : Fin 1 → LS)
    (hx : ∀ i, (0 : WithTop Int) ≤ place.1 (x i)) (f : MvPolynomial (Fin 1) Complex) :
    (0 : WithTop Int) ≤ place.1 (MvPolynomial.aeval x f) := by
  induction f using MvPolynomial.induction_on with
  | C b =>
    rw [MvPolynomial.aeval_C]
    by_cases hb : b = 0
    · subst hb; simp
    · rw [place.2.1 b hb]
  | add p q hp hq =>
    rw [map_add]; exact AddValuation.map_le_add _ hp hq
  | mul_X p i hp =>
    rw [map_mul, AddValuation.map_mul, MvPolynomial.aeval_X]
    exact add_nonneg hp (hx i)

end S38DS

open S38DS in
theorem solution : ¬ (∀ {K d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Fin K → Ideal (MvPolynomial (Fin d) Complex))
    (hbranch : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)),
    polynomialCurveIdealContact nu x (∏ j, I j) =
      ∑ j, polynomialCurveIdealContact nu x (I j)) := by
  intro H
  let x : Fin 1 → LS := fun _ => T
  have hx : ∀ i, (0 : WithTop Int) ≤ place.1 (x i) := by
    intro i; show (0 : WithTop Int) ≤ place.1 T; rw [val_T]; exact_mod_cast zero_le_one
  let I : Fin 2 → Ideal (MvPolynomial (Fin 1) Complex) :=
    ![⊥, Ideal.span {MvPolynomial.X 0}]
  have h := H place x I hx
  have hprod : (∏ j, I j) = ⊥ := by
    rw [Fin.prod_univ_two]; simp [I]
  have hcont : ∀ J : Ideal (MvPolynomial (Fin 1) Complex),
      polynomialCurveIdealContact place x J = sInf {k : Nat | ∃ f : MvPolynomial (Fin 1) Complex,
        f ∈ J ∧ place.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)} := by
    intro J; unfold polynomialCurveIdealContact; rw [if_pos hx]
  have h0 : polynomialCurveIdealContact place x ⊥ = 0 := by
    rw [hcont]
    have : {k : Nat | ∃ f : MvPolynomial (Fin 1) Complex,
        f ∈ (⊥ : Ideal _) ∧ place.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)} = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro f hf
      rw [Ideal.mem_bot.mp hf, map_zero, AddValuation.map_zero]
      exact WithTop.top_ne_coe
    rw [this, Nat.sInf_empty]
  have h1 : polynomialCurveIdealContact place x (Ideal.span {MvPolynomial.X 0}) ≠ 0 := by
    rw [hcont]
    intro hz
    have hne : {k : Nat | ∃ f : MvPolynomial (Fin 1) Complex,
        f ∈ Ideal.span {MvPolynomial.X 0} ∧
          place.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)}.Nonempty := by
      refine ⟨1, MvPolynomial.X 0, Ideal.subset_span rfl, ?_⟩
      rw [MvPolynomial.aeval_X]; exact val_T
    have hm := Nat.sInf_mem hne
    rw [hz] at hm
    obtain ⟨f, hf, hv⟩ := hm
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, AddValuation.map_mul, MvPolynomial.aeval_X] at hv
    have hg := nonneg_aeval x hx g
    have : place.1 (x 0) = ((1 : Int) : WithTop Int) := val_T
    rw [this] at hv
    generalize place.1 (MvPolynomial.aeval x g) = v at hv hg
    induction v using WithTop.recTopCoe with
    | top => simp at hv
    | coe z =>
      have hz0 : (0 : Int) ≤ z := by exact_mod_cast hg
      have : z + 1 = 0 := by exact_mod_cast hv
      omega
  rw [hprod, h0, Fin.sum_univ_two] at h
  simp only [I, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
  rw [h0] at h
  exact h1 (by omega)
