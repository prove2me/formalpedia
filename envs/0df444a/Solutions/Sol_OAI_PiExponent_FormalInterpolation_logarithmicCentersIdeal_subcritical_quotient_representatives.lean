-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_subcritical_quotient_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T18:19:23.274011+00:00
-- url     : https://prove2.me/submissions/a74227c3-253a-4102-9c30-b62b6e0ed474
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedIdealCurveBound_eventual_quotient_representatives
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_weighted_curve_contact_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_finiteColength
import Mathlib.Tactic.Linarith

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

/-- Conditional reduction to a general curve criterion and the logarithmic
curve-contact inequality. The imported children are open obligations. -/
theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hnum : LogarithmicInterpolationNumerics m K w v sigma)
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real)) :
    ∃ δ : Rat, 0 < δ ∧ δ < R ∧ ∃ n₀ : Nat,
      ∀ n : Nat, n₀ ≤ n → ∀ p : MvPolynomial (Fin (m + 1)) Complex,
        ∃ q : MvPolynomial (Fin (m + 1)) Complex,
          p - q ∈ logarithmicCentersIdeal c (fun _ => e 0) e ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤ (n : Real) * (δ : Real) := by
  have hsigma : (0 : Rat) < sigma := by
    exact_mod_cast hnum.sigma_pos
  have hden : (0 : Rat) < 1 + sigma := by linarith
  have hrho_pos : (0 : Rat) < R / (1 + sigma) := div_pos hR hden
  have hrho_lt : R / (1 + sigma) < R := by
    apply (div_lt_iff₀ hden).2
    nlinarith [mul_pos hR hsigma]
  let δ : Rat := (R / (1 + sigma) + R) / 2
  have hδpos : 0 < δ := by dsimp [δ]; linarith
  have hρδ : R / (1 + sigma) < δ := by dsimp [δ]; linarith
  have hδR : δ < R := by dsimp [δ]; linarith
  have hdist : ∀ j k : Fin K, j ≠ k → c j ≠ c k := by
    intro j k hjk h
    apply hjk
    exact hc ⟨0, hnum.m_pos⟩ (congrFun h ⟨0, hnum.m_pos⟩)
  have hfinite := logarithmicCentersIdeal_finiteColength
    c (fun _ => e 0) e he hdist
  have hcurve := logarithmicCentersIdeal_weighted_curve_contact_bound
    c hc w v sigma hnum R e hR he hscale
  refine ⟨δ, hδpos, hδR, ?_⟩
  exact weightedIdealCurveBound_eventual_quotient_representatives
    (logarithmicCentersIdeal c (fun _ => e 0) e)
    hfinite w hnum.degree_pos (R / (1 + sigma)) hrho_pos.le hcurve δ hρδ