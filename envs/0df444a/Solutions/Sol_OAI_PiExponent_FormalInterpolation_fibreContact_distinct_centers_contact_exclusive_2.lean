-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.fibreContact_distinct_centers_contact_exclusive
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-23T23:01:18.012236+00:00
-- url     : https://prove2.me/submissions/d6c11dd6-d5c1-463c-9b06-c394bb3538af

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

noncomputable section

/-- Evaluation of a polynomial at an affine tuple has nonnegative valuation. -/
private theorem counter_aeval_nonneg
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hx : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (f : MvPolynomial (Fin d) Complex) :
    (0 : WithTop Int) ≤ nu.1 (MvPolynomial.aeval x f) := by
  induction f using MvPolynomial.induction_on with
  | C b =>
      simp only [MvPolynomial.aeval_C]
      by_cases hb : b = 0
      · subst b
        simpa only [map_zero, AddValuation.map_zero] using
          (le_top : (0 : WithTop Int) ≤ ⊤)
      · exact le_of_eq (nu.property.1 b hb).symm
  | add p q hp hq =>
      rw [map_add (MvPolynomial.aeval x)]
      exact nu.1.map_le_add hp hq
  | mul_X p i hp =>
      rw [map_mul (MvPolynomial.aeval x), AddValuation.map_mul,
        MvPolynomial.aeval_X]
      exact add_nonneg hp (hx i)

/-- A principal ideal whose generator has order one has positive contact.
The generator also witnesses that the set defining the natural infimum is nonempty. -/
private theorem counter_principal_contact_pos
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hx : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (g : MvPolynomial (Fin d) Complex)
    (hg : nu.1 (MvPolynomial.aeval x g) = (1 : WithTop Int)) :
    0 < polynomialCurveIdealContact nu x (Ideal.span {g}) := by
  classical
  let S : Set Nat := {k | ∃ f : MvPolynomial (Fin d) Complex,
    f ∈ Ideal.span {g} ∧
      nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)}
  have hS : S.Nonempty := by
    refine ⟨1, g, Ideal.mem_span_singleton_self g, ?_⟩
    simpa using hg
  have hpos : ∀ k ∈ S, 0 < k := by
    rintro k ⟨f, hf, hval⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hf
    have hq := counter_aeval_nonneg nu x hx q
    have hlow : (1 : WithTop Int) ≤
        nu.1 (MvPolynomial.aeval x (g * q)) := by
      rw [map_mul (MvPolynomial.aeval x), AddValuation.map_mul, hg]
      simpa only [add_zero] using
        (add_le_add (le_rfl : (1 : WithTop Int) ≤ 1) hq)
    rw [hval] at hlow
    have hk : (1 : Int) ≤ (k : Int) := WithTop.coe_le_coe.mp hlow
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Int.ofNat_le.mp hk)
  unfold polynomialCurveIdealContact
  rw [if_pos hx]
  change 0 < sInf S
  exact hpos _ (Nat.sInf_mem hS)

/-- The order valuation on complex Hahn series is a normalized place. -/
private def counter_place : PolynomialCurvePlace (HahnSeries Int Complex) :=
  ⟨HahnSeries.addVal Int Complex, by
    constructor
    · intro b hb
      simpa only [HahnSeries.addVal_apply, HahnSeries.algebraMap_apply,
        Algebra.algebraMap_self_apply, HahnSeries.C_apply, WithTop.coe_zero] using
          (HahnSeries.orderTop_single (a := (0 : Int)) hb)
    · intro k
      refine ⟨HahnSeries.single k (1 : Complex), ?_⟩
      rw [HahnSeries.addVal_apply, HahnSeries.orderTop_single one_ne_zero]⟩

private theorem counter_single_order (k : Int) :
    counter_place.1 (HahnSeries.single k (1 : Complex)) = (k : WithTop Int) := by
  change HahnSeries.addVal Int Complex _ = _
  rw [HahnSeries.addVal_apply, HahnSeries.orderTop_single one_ne_zero]

private def counter_x : Fin 1 → HahnSeries Int Complex :=
  fun _ => 1 + HahnSeries.single 1 1

private theorem counter_x_affine :
    ∀ i, (0 : WithTop Int) ≤ counter_place.1 (counter_x i) := by
  intro i
  change (0 : WithTop Int) ≤
    counter_place.1 (1 + HahnSeries.single (1 : Int) (1 : Complex))
  apply counter_place.1.map_le_add
  · simpa only [AddValuation.map_one] using (le_rfl : (0 : WithTop Int) ≤ 0)
  · rw [counter_single_order]
    exact WithTop.coe_le_coe.mpr (show (0 : Int) ≤ 1 by decide)

private theorem counter_generator_order :
    counter_place.1 (MvPolynomial.aeval counter_x
      (MvPolynomial.X (0 : Fin 1) - (1 : MvPolynomial (Fin 1) Complex))) = (1 : WithTop Int) := by
  have hev : MvPolynomial.aeval counter_x
      (MvPolynomial.X (0 : Fin 1) - (1 : MvPolynomial (Fin 1) Complex)) =
        HahnSeries.single (1 : Int) (1 : Complex) := by
    rw [map_sub, MvPolynomial.aeval_X, map_one]
    change (1 + HahnSeries.single (1 : Int) (1 : Complex)) - 1 = _
    ring
  rw [hev]
  exact counter_single_order 1

/-- In dimension zero there is only the first logarithmic coordinate. -/
private theorem counter_center_ideal (c : Fin 0 → Complex) :
    logarithmicCenterIdeal c (fun _ => 1) (fun _ => 1) =
      Ideal.span {MvPolynomial.X (0 : Fin 1) - (1 : MvPolynomial (Fin 1) Complex)} := by
  unfold logarithmicCenterIdeal
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [logarithmicCoordinate]
  · intro hp
    simp only [Set.mem_singleton_iff] at hp
    refine ⟨0, ?_⟩
    simpa [logarithmicCoordinate] using hp.symm

theorem solution : ¬ (∀ {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E),
    ∀ j k : Fin K, j ≠ k →
      ¬ (0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c j) (fun _ => e 0) e) ∧
         0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c k) (fun _ => e 0) e))) := by
  intro h
  let c : Fin 2 → Fin 0 → Complex := fun _ i => Fin.elim0 i
  let e : Fin (0 + 1) → Nat := fun _ => 1
  have hc : ∀ i : Fin 0, Function.Injective (fun j : Fin 2 => c j i) := by
    intro i
    exact Fin.elim0 i
  have he : ∀ i : Fin (0 + 1), 0 < e i := by
    intro i
    change 0 < 1
    decide
  have hcontact (a : Fin 0 → Complex) :
      0 < polynomialCurveIdealContact counter_place counter_x
        (logarithmicCenterIdeal a (fun _ => e 0) e) := by
    change 0 < polynomialCurveIdealContact counter_place counter_x
      (logarithmicCenterIdeal a (fun _ => 1) (fun _ => 1))
    rw [counter_center_ideal]
    exact counter_principal_contact_pos counter_place counter_x counter_x_affine
      (MvPolynomial.X (0 : Fin 1) - (1 : MvPolynomial (Fin 1) Complex)) counter_generator_order
  exact h (m := 0) (K := 2) c hc e he (HahnSeries Int Complex)
    counter_place counter_x (0 : Fin 2) (1 : Fin 2) (by decide)
    ⟨hcontact (c 0), hcontact (c 1)⟩
