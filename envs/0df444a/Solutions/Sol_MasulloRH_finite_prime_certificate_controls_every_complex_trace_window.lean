-- Prove2me | solution 1 for MasulloRH.finite_prime_certificate_controls_every_complex_trace_window
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T03:25:44.250984+00:00
-- url     : https://prove2.me/submissions/5f3ec214-061f-474a-9258-9bcf110b59b4

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_complex_window_trace_error_controlled_by_reference_deficit
import Theorems.Thm_MasulloRH_approximate_prime_certificate_bounds_missing_zero_mass
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Linarith

open MasulloRH ArithmeticFunction Set

theorem solution (N : ℕ) (hN : 2 ≤ N) (ε : ℝ)
    (F : Finset (ZetaZerosInTraceStrip (1 / 2))) (hF : ∀ z ∈ F, z.val.re = 1 / 2)
    (hc : Real.log 2 / 2 + Real.pi / 4 - 37 / 30 +
      (∑ j ∈ Finset.range (N+1), (vonMangoldt j / (j:ℝ) ^ (5/2:ℝ) -
        vonMangoldt j / (j:ℝ) ^ (3:ℝ))) ≤
      (∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val : ℝ) *
        ((z.val.im^2-5) / (2*(z.val.im^2+25/4)*(z.val.im^2+4)))) + ε) :
    let B := ε + ((2/3) * Real.log N + 4/9) * (N:ℝ)^(-(3/2):ℝ)
    ∀ α : ℝ, 0 < α → ∀ s : ℂ, 1 < s.re →
      let E := ‖s-5/2‖ * (1+‖s-5/2‖/(s.re-1)) * (4*B)
      0 ≤ (regularizedTraceRHS (1/2) 3).re - (regularizedTraceRHS α 3).re ∧
      (regularizedTraceRHS (1/2) 3).re - (regularizedTraceRHS α 3).re ≤ 2*B ∧
      ‖regularizedTraceRHS (1/2) s - regularizedTraceRHS α s‖ ≤ E ∧
      ((3/2:ℝ) < s.re → ‖zetaLogDeriv s - regularizedTraceRHS α s‖ ≤ E) := by
  classical
  intro B α hα s hs E
  let Z := ZetaZerosInTraceStrip (1/2)
  let w := zeroDecayWeight (1/2)
  let W := ∑' z : Z, if α ≤ |z.val.re-1/2| then w z else 0
  have hw : Summable w := weighted_zero_summability _ (by norm_num)
  have hwpos (z : Z) : 0 ≤ w z := by dsimp [w,zeroDecayWeight]; positivity
  have hleft : Summable (fun z : Z => if α ≤ |z.val.re-1/2| then w z else 0) := by
    apply (hw.indicator {z | α ≤ |z.val.re-1/2|}).congr
    intro z
    simp [Set.indicator]
  have hright : Summable (fun z : Z => if z ∈ F then 0 else w z) := by
    apply (hw.indicator {z | z ∉ F}).congr
    intro z
    simp [Set.indicator]
  have hle : W ≤ ∑' z : Z, if z ∈ F then 0 else w z := by
    apply hleft.tsum_le_tsum _ hright
    intro z
    by_cases hin : z ∈ F
    · simp [hin, hF z hin, not_le.mpr hα]
    · simp only [hin, if_false]
      split
      · exact le_rfl
      · exact hwpos z
  have hW : W ≤ 4*B := hle.trans (approximate_prime_certificate_bounds_missing_zero_mass N hN ε F hF hc)
  have hW0 : 0 ≤ W := by
    apply tsum_nonneg
    intro z
    split
    · exact hwpos z
    · exact le_rfl
  rcases complex_window_trace_error_controlled_by_reference_deficit α s hs with ⟨hlo,hhi,hcmp⟩
  change W/4 ≤ _ at hlo
  change _ ≤ W/2 at hhi
  have hcpos : 0 ≤ ‖s-5/2‖*(1+‖s-5/2‖/(s.re-1)) :=
    mul_nonneg (norm_nonneg _) (by have := sub_pos.mpr hs; positivity)
  have herr : ‖regularizedTraceRHS (1/2) s - regularizedTraceRHS α s‖ ≤ E :=
    hcmp.trans (mul_le_mul_of_nonneg_left hW hcpos)
  refine ⟨by linarith, by linarith, herr, ?_⟩
  intro hrightHalf
  rw [← regularized_initial_identity_full_strip s hrightHalf]
  exact herr
