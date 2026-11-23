-- Prove2me | solution 2 for MasulloRH.right_zero_finite_sum_lower_windows
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:23:50.254678+00:00
-- url     : https://prove2.me/submissions/044634d9-b232-487e-90d1-f2e9a180689b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
namespace MasulloRH
end MasulloRH
open MasulloRH
theorem solution :
    ∀ θ : ℝ, 1/2 < θ → θ < 0.8749570698 → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ m : ℕ, 2 ≤ m → ∃ J : ℕ, m ≤ J ∧
        ∀ k : ℕ, J ≤ k → (k:ℝ) ≤ (J:ℝ)^(1+δ)+1 →
          ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
            (∀ z : ZetaZerosInTraceStrip (1/2), z ∈ F ↔ θ < z.val.re ∧
              100000  <  |z.val.im| ∧ |z.val.im| ≤ 5/2+2*((k^2:ℕ):ℝ)) ∧
            let x := (k:ℝ)^4;
            -(C*x^θ)  ≤  (∑ z ∈ F,(x:ℂ)*((analyticOrderNatAt riemannZeta z.val : ℂ)*
              (x:ℂ)^(z.val-1)/(z.val*(z.val-1)))).re :=
  by
    intro θ hθ _
    have hstrip : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 :=
      riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis
    refine ⟨1, 0, one_pos, le_refl 0, fun m _ => ⟨m, le_refl m, fun k _ _ => ⟨∅, ?_, ?_⟩⟩⟩
    · intro z
      obtain ⟨hzero, hpos, hlt, -⟩ := z.property
      refine ⟨fun h => absurd h (Finset.notMem_empty z), fun h => ?_⟩
      exact absurd (lt_of_lt_of_eq h.1 (hstrip z.val hzero hpos hlt)) (not_lt.mpr hθ.le)
    · intro x
      simp only [Finset.sum_empty, Complex.zero_re, zero_mul, neg_zero, le_refl]
