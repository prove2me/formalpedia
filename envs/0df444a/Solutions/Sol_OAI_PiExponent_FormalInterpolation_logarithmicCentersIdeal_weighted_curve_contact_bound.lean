-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_weighted_curve_contact_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T22:34:40.211874+00:00
-- url     : https://prove2.me/submissions/8a8cc6cb-333b-4891-a315-ae417e4dd348
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicIdeal_excess_forces_zeroth_one
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicIdeal_fibre_excess_forces_constant
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicIdeal_constant_fibre_contact_le
import Mathlib.Tactic.Linarith

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hnum : LogarithmicInterpolationNumerics m K w v sigma)
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real)) :
    WeightedIdealCurveBound
      (logarithmicCentersIdeal c (fun _ => e 0) e) w (R / (1 + sigma)) := by
  classical
  intro E _ _ _ htrdeg x hgen
  let contactSum : Real :=
    ∑ᶠ nu : PolynomialCurvePlace E,
      (polynomialCurveIdealContact nu x
        (logarithmicCentersIdeal c (fun _ => e 0) e) : Real)
  let poleDegree : Real :=
    ∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w
  have hs : 0 < 1 + (sigma : Real) := by
    linarith [hnum.sigma_pos]
  have hRreal : 0 ≤ (R : Real) := by
    exact_mod_cast (le_of_lt hR)
  have hcoeff : ∀ i : Fin m,
      (e i.succ : Real) * (w i.succ : Real) ≤
        (R : Real) / (1 + (sigma : Real)) := by
    intro i
    apply (le_div_iff₀ hs).mpr
    rw [hscale i.succ]
    have hh := mul_le_mul_of_nonneg_left (le_of_lt (hnum.coordinate_ratio i))
      (Nat.cast_nonneg (e i.succ) : (0 : Real) ≤ (e i.succ : Real))
    nlinarith [hh]
  have hbound : contactSum ≤
      ((R : Real) / (1 + (sigma : Real))) * poleDegree := by
    by_contra hn
    have hn' : ((R : Real) / (1 + (sigma : Real))) * poleDegree <
        contactSum := lt_of_not_ge hn
    have hd : (R : Real) * poleDegree / (1 + (sigma : Real)) <
        contactSum := by
      simpa only [div_mul_eq_mul_div] using hn'
    have hexcess : (R : Real) * poleDegree <
        (1 + (sigma : Real)) * contactSum := by
      have ht := (div_lt_iff₀ hs).mp hd
      simpa only [mul_comm contactSum (1 + (sigma : Real))] using ht
    have hfibre := logarithmicIdeal_excess_forces_zeroth_one
      c hc w v sigma hnum.m_pos hnum.K_pos hnum.sigma_pos
      hnum.degree_pos hnum.jet_pos hnum.volume hnum.separated
      R e hR he hscale E htrdeg x hgen hexcess
    have hconstant := logarithmicIdeal_fibre_excess_forces_constant
      c hc w v sigma hnum.m_pos hnum.K_pos hnum.sigma_pos
      hnum.degree_pos hnum.jet_pos hnum.fibre_volume hnum.separated
      R e hR he hscale E htrdeg x hgen hfibre hexcess
    have hle := logarithmicIdeal_constant_fibre_contact_le
      c hc (fun _ => e 0) e he w hnum.degree_pos
      ((R : Real) / (1 + (sigma : Real)))
      (div_nonneg hRreal (le_of_lt hs)) hcoeff
      E htrdeg x hgen hfibre hconstant
    exact (not_le_of_gt hn') hle
  change contactSum ≤ ((R / (1 + sigma) : Rat) : Real) * poleDegree
  simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_one] using hbound