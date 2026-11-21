-- Prove2me | solution 1 for MasulloRH.right_zero_finite_sum_lower_windows
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T03:59:03.567613+00:00
-- url     : https://prove2.me/submissions/fa5a957b-cf36-4b05-a5fb-53a7f85835f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_cofinal_signed_critical_band_certificates
import Theorems.Thm_MasulloRH_critical_zero_band_of_signed_brackets
import Mathlib

open MasulloRH Set Finset ArithmeticFunction MeasureTheory
open Finset ArithmeticFunction MeasureTheory Set

theorem solution :
    ∀ θ : ℝ, 1/2 < θ → θ < 0.8749570698 → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ m : ℕ, 2 ≤ m → ∃ J : ℕ, m ≤ J ∧
        ∀ k : ℕ, J ≤ k → (k:ℝ) ≤ (J:ℝ)^(1+δ)+1 →
          ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
            (∀ z : ZetaZerosInTraceStrip (1/2), z ∈ F ↔ θ < z.val.re ∧
              100000  <  |z.val.im| ∧ |z.val.im| ≤ 5/2+2*((k^2:ℕ):ℝ)) ∧
            let x := (k:ℝ)^4;
            -(C*x^θ)  ≤  (∑ z ∈ F,(x:ℂ)*((analyticOrderNatAt riemannZeta z.val : ℂ)*
              (x:ℂ)^(z.val-1)/(z.val*(z.val-1)))).re  := by
  intro θ hθ _
  refine ⟨1, 0, by norm_num, le_rfl, ?_⟩
  intro m hm
  refine ⟨m, le_rfl, ?_⟩
  intro k hmk hk
  obtain ⟨H, hH, E, B, hE, hB, hD, hED, hcount⟩ :=
    cofinal_signed_critical_band_certificates (3+2*k^2)
  have hband := critical_zero_band_of_signed_brackets 100000 (H:ℝ) E B hE hB hD hED hcount
  refine ⟨∅, ?_, ?_⟩
  · intro z
    simp only [Finset.notMem_empty, false_iff]
    rintro ⟨hzθ, hzlow, hzheight⟩
    have hH' : (3:ℝ)+2*((k^2:ℕ):ℝ) ≤ H := by exact_mod_cast hH
    have hzH : |z.val.im| ≤ (H:ℝ) := by linarith
    have hzline := hband z hzlow hzH
    linarith
  · simp


