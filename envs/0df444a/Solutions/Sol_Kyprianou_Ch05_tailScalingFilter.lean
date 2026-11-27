-- Prove2me | solution 1 for Kyprianou.Ch05.tailScalingFilter
-- status  : ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T00:48:23.881337+00:00
-- url     : https://prove2.me/submissions/e4c26380-c8c3-4fe7-97ed-579ec0d67bb5

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Karamata tail scaling at a general positive endpoint filter.
Mirror of WillR's `potentialScalingFilter` proof, with division by
`Phi (1 / x)` in place of multiplication. -/
theorem solution
    (Pi : Measure Real) (Phi L : Real → Real) (alpha : Real)
    (l : Filter Real) (hAlpha1 : alpha < 1)
    (hpos : ∀ᶠ x in l, 0 < x)
    (hL : ∀ x : Real, 0 < x → 0 < L x)
    (hPhi : ∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) * L x)
    (hDens : Tendsto (fun x : Real => (Pi (Set.Ioi x)).toReal /
      (x ^ ((1 - alpha) - 1) * L x / Real.Gamma (1 - alpha))) l (nhds 1))
    (a : Real) (ha : 0 < a)
    (hScale : Tendsto (fun x : Real => a * x) l l)
    (hSlow : Tendsto (fun x : Real => L (a * x) / L x) l (nhds 1)) :
    Tendsto (fun x : Real => (Pi (Set.Ioi (a * x))).toReal / Phi (1 / x)) l
      (nhds (a ^ (-alpha) / Real.Gamma (1 - alpha))) := by
  have h := ((hDens.comp hScale).mul hSlow).mul_const (a ^ (-alpha) / Real.Gamma (1 - alpha))
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hpos] with x hx
  change ((Pi (Set.Ioi (a * x))).toReal /
      ((a * x) ^ ((1 - alpha) - 1) * L (a * x) / Real.Gamma (1 - alpha))) *
    (L (a * x) / L x) * (a ^ (-alpha) / Real.Gamma (1 - alpha)) =
    (Pi (Set.Ioi (a * x))).toReal / Phi (1 / x)
  rw [show (1 - alpha) - 1 = -alpha by ring, hPhi x hx,
    Real.mul_rpow ha.le hx.le, Real.rpow_neg hx.le]
  have hg : 0 < Real.Gamma (1 - alpha) := Real.Gamma_pos_of_pos (by linarith)
  field_simp [ne_of_gt (hL x hx), ne_of_gt (hL (a * x) (mul_pos ha hx)),
    ne_of_gt (Real.rpow_pos_of_pos ha (-alpha)),
    ne_of_gt (Real.rpow_pos_of_pos hx alpha), hg.ne']
