-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicIdeal_constant_fibre_contact_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T23:09:48.1329+00:00
-- url     : https://prove2.me/submissions/9fdf4534-77d7-4c25-be32-8532653e782b

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_constant_fibre_contact_localization
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_function_divisor_le_weighted_poles

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

private theorem pole_sum_nonneg
    {d : Nat} (E : Type) [Field E] [Algebra Complex E]
    (x : Fin d → E) (w : Fin d → Rat) :
    0 ≤ ∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w := by
  classical
  apply finsum_nonneg
  intro nu
  unfold polynomialCurvePole
  exact Finset.le_sup'_of_le _ (Finset.mem_univ (none : Option (Fin d))) le_rfl

private theorem exists_transcendental_succ
    {m : Nat} (E : Type) [Field E] [Algebra Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1) :
    ∃ k : Fin m, Transcendental Complex (x k.succ) := by
  classical
  by_contra h
  have hall : ∀ i : Fin (m + 1), IsAlgebraic Complex (x i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [hfibre]
      exact isAlgebraic_one
    · by_contra hk
      exact h ⟨k, hk⟩
  have hfield : Algebra.IsAlgebraic Complex E := by
    constructor
    intro y
    have hy : y ∈ IntermediateField.adjoin Complex (Set.range x) := by
      rw [hgen]
      exact IntermediateField.mem_top
    exact IntermediateField.adjoin_induction Complex
      (p := fun y _ => IsAlgebraic Complex y)
      (fun y hy => by
        rcases hy with ⟨i, rfl⟩
        exact hall i)
      (fun b => isAlgebraic_algebraMap b)
      (fun y z _ _ hy hz => hy.add hz)
      (fun y _ hy => hy.inv)
      (fun y z _ _ hy hz => hy.mul hz)
      hy
  letI : Algebra.IsAlgebraic Complex E := hfield
  have hzero : Algebra.trdeg Complex E = 0 := trdeg_eq_zero
  rw [htrdeg] at hzero
  exact one_ne_zero hzero

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat) (he : ∀ i, 0 < e i)
    (w : Fin (m + 1) → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Real) (hrho : 0 ≤ rho)
    (hcoeff : ∀ i : Fin m, (e i.succ : Real) * (w i.succ : Real) ≤ rho)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (hconstant : ∃ i : Fin m, ∃ a : Complex,
      x i.succ = algebraMap Complex E a) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real)) ≤
      rho * (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) := by
  obtain ⟨k, hk⟩ := exists_transcendental_succ E htrdeg x hgen hfibre
  rcases hconstant with ⟨i0, a, ha⟩
  have hp := pole_sum_nonneg E x w
  rcases OAI.PiExponent.FormalInterpolation.constant_fibre_contact_localization
      c hc T e E htrdeg x hgen hfibre i0 a ha k hk with hzero | hmatched
  · rw [hzero]
    exact mul_nonneg hrho hp
  · obtain ⟨j, hj, hcontact⟩ := hmatched
    have hdiv :=
      OAI.PiExponent.FormalInterpolation.function_divisor_le_weighted_poles
        (d := m + 1) E htrdeg x hgen w hw k.succ hk (c j k)
    have he0 : 0 ≤ (e k.succ : Real) := Nat.cast_nonneg _
    calc
      (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x (logarithmicCentersIdeal c T e) : Real))
          ≤ (e k.succ : Real) *
              ∑ᶠ nu : PolynomialCurvePlace E,
                max (polynomialCurveOrder nu
                  (x k.succ - algebraMap Complex E (c j k)) : Real) 0 := hcontact
      _ ≤ (e k.succ : Real) *
              ((w k.succ : Real) *
                ∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) :=
          mul_le_mul_of_nonneg_left hdiv he0
      _ = ((e k.succ : Real) * (w k.succ : Real)) *
            (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) :=
          (mul_assoc _ _ _).symm
      _ ≤ rho * (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) :=
          mul_le_mul_of_nonneg_right (hcoeff k) hp
