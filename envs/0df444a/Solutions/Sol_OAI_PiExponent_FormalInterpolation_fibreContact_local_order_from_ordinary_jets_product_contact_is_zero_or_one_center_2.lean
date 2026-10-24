-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_product_contact_is_zero_or_one_center
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T23:06:52.73635+00:00
-- url     : https://prove2.me/submissions/f2f51053-4898-4198-8d5f-0df8396acc16

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_product_ideal_contact_eq_sum
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_sum_support_at_most_one
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_distinct_centers_contact_exclusive_of_fibre
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (N : Nat) (hN : 0 < N) (f : MvPolynomial (Fin m) Complex)
    (hjet : fibreContactJetVanishing c (fun i => v i.succ)
      ((1 + 2 * (sigma : Real)) * (N : Real)) f)
    (nu : PolynomialCurvePlace E)
    (hne : MvPolynomial.aeval (fun i => x i.succ) f ≠ 0) :
    polynomialCurveIdealContact nu x
      (logarithmicCentersIdeal c (fun _ => e 0) e) = 0 ∨
    ∃ j : Fin K,
      polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) =
      polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) := by
  classical
  have hcontact :=
    OAI.PiExponent.FormalInterpolation.fibreContact_product_ideal_contact_eq_sum
      c e E nu x
  have hexclusive :=
    OAI.PiExponent.FormalInterpolation.fibreContact_distinct_centers_contact_exclusive_of_fibre
      c hc e he E nu x hfibre
  have hsum :=
    OAI.PiExponent.FormalInterpolation.fibreContact_sum_support_at_most_one
      (fun j : Fin K =>
        polynomialCurveIdealContact nu x
          (logarithmicCenterIdeal (c j) (fun _ => e 0) e)) hexclusive
  rcases hsum with hzero | ⟨j, hsingle⟩
  · left
    rw [hcontact]
    exact hzero
  · right
    refine ⟨j, ?_⟩
    rw [hcontact]
    exact hsingle
