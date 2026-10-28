-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmic_centers_contact_is_single_center
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-24T08:59:40.220444+00:00
-- url     : https://prove2.me/submissions/fae760da-fb61-4289-9349-c7e93e334333

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.Tactic.NormNum

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

noncomputable section

/-- On the affine chart every evaluated polynomial has nonnegative order. -/
private theorem affine_polynomial_nonneg
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hx : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (f : MvPolynomial (Fin d) Complex) :
    (0 : WithTop Int) ≤ nu.1 (MvPolynomial.aeval x f) := by
  induction f using MvPolynomial.induction_on with
  | C b =>
      rw [MvPolynomial.aeval_C]
      by_cases hb : b = 0
      · simp [hb]
      · simpa only [nu.2.1 b hb] using (le_refl (0 : WithTop Int))
  | add f g hf hg =>
      rw [map_add]
      exact nu.1.map_le_add hf hg
  | mul_X f i hf =>
      rw [map_mul, MvPolynomial.aeval_X, nu.1.map_mul]
      exact add_nonneg hf (hx i)

/-- The finite order of a principal generator is the ideal's contact.
The generator itself proves nonemptiness and attainment of the infimum. -/
private theorem affine_principal_contact
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hx : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (g : MvPolynomial (Fin d) Complex) (n : Nat)
    (hg : nu.1 (MvPolynomial.aeval x g) = ((n : Int) : WithTop Int)) :
    polynomialCurveIdealContact nu x (Ideal.span {g}) = n := by
  classical
  rw [polynomialCurveIdealContact, if_pos hx]
  have hn : n ∈ {k : Nat | ∃ f : MvPolynomial (Fin d) Complex,
      f ∈ Ideal.span {g} ∧
      nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)} :=
    ⟨g, Ideal.mem_span_singleton_self g, hg⟩
  apply le_antisymm (csInf_le (OrderBot.bddBelow _) hn)
  apply le_csInf ⟨n, hn⟩
  rintro k ⟨f, hf, hfk⟩
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  have hq := affine_polynomial_nonneg nu x hx q
  rw [map_mul, nu.1.map_mul, hg] at hfk
  have hle : ((n : Int) : WithTop Int) ≤ ((k : Int) : WithTop Int) := by
    calc
      ((n : Int) : WithTop Int) = 0 + ((n : Int) : WithTop Int) :=
        (zero_add _).symm
      _ ≤ nu.1 (MvPolynomial.aeval x q) + ((n : Int) : WithTop Int) :=
        add_le_add hq (le_refl _)
      _ = ((k : Int) : WithTop Int) := hfk
  exact Int.ofNat_le.mp (WithTop.coe_le_coe.mp hle)

private def counterPlace : PolynomialCurvePlace (HahnSeries Int Complex) := by
  refine ⟨HahnSeries.addVal Int Complex, ?_, ?_⟩
  · intro b hb
    rw [HahnSeries.addVal_apply]
    change (HahnSeries.single (0 : Int) b).orderTop = 0
    simpa using (HahnSeries.orderTop_single (a := (0 : Int)) hb)
  · intro k
    refine ⟨HahnSeries.single k 1, ?_⟩
    rw [HahnSeries.addVal_apply, HahnSeries.orderTop_single one_ne_zero]

private def counterPoint : Fin 1 → HahnSeries Int Complex :=
  fun _ => 1 + HahnSeries.single 1 1

private def counterGenerator : MvPolynomial (Fin 1) Complex :=
  MvPolynomial.X 0 - 1

private theorem counter_uniformizer_order :
    counterPlace.1 (HahnSeries.single 1 1) = ((1 : Int) : WithTop Int) := by
  change HahnSeries.addVal Int Complex (HahnSeries.single 1 1) = _
  rw [HahnSeries.addVal_apply]
  exact HahnSeries.orderTop_single one_ne_zero

private theorem counter_chart :
    ∀ i, (0 : WithTop Int) ≤ counterPlace.1 (counterPoint i) := by
  intro i
  change (0 : WithTop Int) ≤ counterPlace.1 (1 + HahnSeries.single 1 1)
  apply counterPlace.1.map_le_add
  · simp
  · rw [counter_uniformizer_order]
    exact WithTop.coe_le_coe.mpr (by norm_num : (0 : Int) ≤ 1)

private theorem counter_generator_eval :
    MvPolynomial.aeval counterPoint counterGenerator = HahnSeries.single 1 1 := by
  simp [counterGenerator, counterPoint]

private theorem zero_dimensional_center
    (c : Fin 0 → Complex) (T : Fin 0 → Nat) :
    logarithmicCenterIdeal c T (fun _ => 1) = Ideal.span {counterGenerator} := by
  unfold logarithmicCenterIdeal
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [logarithmicCoordinate, counterGenerator]
  · intro hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact ⟨0, by simp [logarithmicCoordinate, counterGenerator]⟩

private theorem counter_single_contact (c : Fin 0 → Complex) :
    polynomialCurveIdealContact counterPlace counterPoint
      (logarithmicCenterIdeal c (fun _ => 1) (fun _ => 1)) = 1 := by
  rw [zero_dimensional_center]
  apply affine_principal_contact counterPlace counterPoint counter_chart counterGenerator 1
  simpa only [counter_generator_eval, Nat.cast_one] using counter_uniformizer_order

private theorem counter_product_contact (c : Fin 2 → Fin 0 → Complex) :
    polynomialCurveIdealContact counterPlace counterPoint
      (logarithmicCentersIdeal c (fun _ => 1) (fun _ => 1)) = 2 := by
  rw [logarithmicCentersIdeal, Fin.prod_univ_two]
  simp only [zero_dimensional_center, Ideal.span_singleton_mul_span_singleton]
  apply affine_principal_contact counterPlace counterPoint counter_chart
    (counterGenerator * counterGenerator) 2
  rw [map_mul, counterPlace.1.map_mul, counter_generator_eval,
    counter_uniformizer_order, ← WithTop.coe_add]
  rfl

/-- The exact target is false: its coordinate separation condition is vacuous
in dimension zero, and two identical centers double the positive contact. -/
theorem solution :
    ¬ (∀ {m K : Nat} (c : Fin K → Fin m → Complex),
      (∀ i : Fin m, Function.Injective (fun j : Fin K => c j i)) →
      ∀ (e : Fin (m + 1) → Nat) (E : Type) [Field E] [Algebra Complex E]
        (nu : PolynomialCurvePlace E) (x : Fin (m + 1) → E),
      0 < (polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real) →
      ∃ j : Fin K,
        0 < (polynomialCurveIdealContact nu x
          (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) ∧
        (polynomialCurveIdealContact nu x
          (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) =
        (polynomialCurveIdealContact nu x
          (logarithmicCentersIdeal c (fun _ => e 0) e) : Real)) := by
  intro h
  let c : Fin 2 → Fin 0 → Complex := fun _ i => Fin.elim0 i
  have hc : ∀ i : Fin 0, Function.Injective (fun j : Fin 2 => c j i) := by
    intro i
    exact Fin.elim0 i
  have hp : 0 < (polynomialCurveIdealContact counterPlace counterPoint
      (logarithmicCentersIdeal c (fun _ => 1) (fun _ => 1)) : Real) := by
    rw [counter_product_contact]
    norm_num
  obtain ⟨j, _, hj⟩ := h c hc (fun _ => 1) (HahnSeries Int Complex)
    counterPlace counterPoint hp
  rw [counter_single_contact, counter_product_contact] at hj
  norm_num at hj
