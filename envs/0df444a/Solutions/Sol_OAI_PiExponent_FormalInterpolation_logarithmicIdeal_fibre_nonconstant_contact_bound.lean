-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicIdeal_fibre_nonconstant_contact_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T09:44:53.660114+00:00
-- url     : https://prove2.me/submissions/88ad75d7-e038-4c9d-95a4-2ceaa5f59daf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_auxiliary_polynomial_exists
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_excess_forces_derivative_vanishing
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_separated_derivative_rigidity
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.Linarith

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
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ)) :
    (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveIdealContact nu x
          (logarithmicCentersIdeal c (fun _ => e 0) e) : Real)) ≤
      (R : Real) / (1 + (sigma : Real)) *
        (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) := by
  classical
  by_contra hbound
  obtain ⟨N1, haux⟩ := fibreContact_auxiliary_polynomial_exists
    m K (fun i => w i.succ) (fun i => v i.succ)
    (fun i => hw i.succ) (fun i => hv i.succ)
    (1 + 3 * (sigma : Real)) (by linarith) hfibreVolume c
  obtain ⟨N2, hrigid⟩ := fibreContact_separated_derivative_rigidity
    w v sigma hm hsigma hw hv hseparated E (fun i => x i.succ)
  let N : Nat := max (max N1 N2) 1
  have hN1 : N1 ≤ N :=
    le_trans (le_max_left N1 N2) (le_max_left (max N1 N2) 1)
  have hN2 : N2 ≤ N :=
    le_trans (le_max_right N1 N2) (le_max_left (max N1 N2) 1)
  have hN : 0 < N :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_right (max N1 N2) 1)
  obtain ⟨F, hF0, hF, hjet⟩ := haux N hN1
  have hwords := fibreContact_excess_forces_derivative_vanishing
    c hc w v sigma hm hK hsigma hw hv R e hR he hscale
    E htrdeg x hgen hfibre hnonconst N hN F hF hjet (lt_of_not_ge hbound)
  obtain ⟨i, a, ha⟩ := hrigid N hN2 hN F hF0 hF hwords
  have halg : IsAlgebraic Complex (x i.succ) := by
    rw [ha]
    exact isAlgebraic_algebraMap a
  exact hnonconst i halg

