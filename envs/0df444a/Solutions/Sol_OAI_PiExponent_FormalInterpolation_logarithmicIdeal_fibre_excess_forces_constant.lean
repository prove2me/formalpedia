-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicIdeal_fibre_excess_forces_constant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:21:28.779931+00:00
-- url     : https://prove2.me/submissions/e0d43863-4e5c-441f-bb3d-f33f26f542ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicIdeal_fibre_nonconstant_contact_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_isAlgebraic_eq_algebraMap_of_isAlgClosed
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hfibreVolume :
      (K : Real) * (1 + 3 * (sigma : Real)) ^ m *
        (∏ i : Fin m, (w i.succ : Real)) /
          (∏ i : Fin m, (v i.succ : Real)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
        (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
        interpolationSeparationConstant m sigma *
          (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin (m + 1) → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (hfibre : x 0 = 1)
    (hexcess :
      (R : Real) * (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) <
        (1 + (sigma : Real)) *
          (∑ᶠ nu : PolynomialCurvePlace E,
            (polynomialCurveIdealContact nu x
              (logarithmicCentersIdeal c (fun _ => e 0) e) : Real))) :
    ∃ i : Fin m, ∃ a : Complex, x i.succ = algebraMap Complex E a := by
  classical
  by_contra h
  push Not at h
  have hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ) := by
    intro i halg
    obtain ⟨a, ha⟩ := isAlgebraic_eq_algebraMap_of_isAlgClosed (x i.succ) halg
    exact h i a ha
  have hbound :=
    logarithmicIdeal_fibre_nonconstant_contact_bound
      c hc w v sigma hm hK hsigma hw hv hfibreVolume hseparated R e hR he hscale
      E htrdeg x hgen hfibre hnonconst
  set contact :=
    (∑ᶠ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real))
  set poles := (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w)
  replace hexcess : (R : Real) * poles < (1 + (sigma : Real)) * contact := by
    simpa [contact, poles] using hexcess
  replace hbound : contact ≤ (R : Real) / (1 + (sigma : Real)) * poles := by
    simpa [contact, poles] using hbound
  have hpos : 0 < (1 + (sigma : Real)) := by linarith
  have hle : (1 + (sigma : Real)) * contact ≤ (R : Real) * poles := by
    have hbound'' : contact ≤ ((R : Real) * poles) / (1 + (sigma : Real)) := by
      convert hbound using 1
      ring
    have := (le_div_iff₀ hpos).mp hbound''
    linarith
  exact not_lt_of_ge hle hexcess
