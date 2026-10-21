-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_strict_power_generators
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T12:37:09.149055+00:00
-- url     : https://prove2.me/submissions/3df1d63a-8372-409d-a81e-3136a9f59859
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_subcritical_quotient_representatives
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_quotient_representatives_imply_strict_power_generators

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
    ∃ s : Nat, ∃ D : Rat,
      (D : Real) < (s : Real) * (R : Real) ∧
      logarithmicCentersIdeal c (fun _ => e 0) e ^ s =
        Ideal.span {p : MvPolynomial (Fin (m + 1)) Complex |
          p ∈ logarithmicCentersIdeal c (fun _ => e 0) e ^ s ∧
          ∀ a ∈ p.support, ∑ i, (w i : Real) * (a i : Real) ≤ (D : Real)} := by
  obtain ⟨δ, hδpos, hδR, n₀, hrep⟩ :=
    OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_subcritical_quotient_representatives
      c hc w v sigma hnum R e hR he hscale
  exact OAI.PiExponent.FormalInterpolation.bounded_quotient_representatives_imply_strict_power_generators
    w R (logarithmicCentersIdeal c (fun _ => e 0) e) hR hnum.degree_pos
    δ hδpos hδR n₀ hrep