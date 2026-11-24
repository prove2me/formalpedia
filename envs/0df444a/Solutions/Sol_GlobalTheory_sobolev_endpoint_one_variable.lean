-- Prove2me | solution 1 for GlobalTheory.sobolev_endpoint_one_variable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:36.016516+00:00
-- url     : https://prove2.me/submissions/c7d6e981-a89b-4635-90ae-71b27b29719d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqIntervalIntegralLeMulIntervalIntegralSq
import Theorems.Thm_GlobalTheory_sq_intervalIntegral_le_mul_intervalIntegral_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ φ' : ℝ → H) (s : ℝ), 0 < s → (∀ t ∈ Set.Icc 0 s, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc 0 s) → ‖φ 0‖ ^ 2 ≤ 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
  intro H _ _ _ φ φ' s hs hd hc
  have hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s := Set.uIcc_of_le hs.le
  have hφc : ContinuousOn φ (Set.Icc 0 s) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hn' : ContinuousOn (fun t => ‖φ' t‖) (Set.Icc 0 s) := hc.norm
  have hn'i : IntervalIntegrable (fun t => ‖φ' t‖) volume 0 s :=
    (hn'.mono hIcc.subset).intervalIntegrable
  have hA : IntervalIntegrable (fun t => ‖φ t‖ ^ 2) volume 0 s :=
    ((hφc.norm.pow 2).mono hIcc.subset).intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ‖φ 0‖ ^ 2 ≤ 2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 := by
    intro t ht
    have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 s := by
      rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
    have hint : IntervalIntegrable φ' volume 0 t := (hc.mono hsub).intervalIntegrable
    have hftc : ∫ y in (0 : ℝ)..t, φ' y = φ t - φ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x (hsub hx)) hint
    have h1 : ‖φ 0‖ ≤ ‖φ t‖ + ‖∫ y in (0 : ℝ)..t, φ' y‖ := by
      rw [hftc]
      have := norm_sub_le (φ t) (φ t - φ 0)
      rwa [sub_sub_cancel] at this
    have h2 : ‖∫ y in (0 : ℝ)..t, φ' y‖ ≤ ∫ y in (0 : ℝ)..t, ‖φ' y‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.1
    have h3 : ∫ y in (0 : ℝ)..t, ‖φ' y‖ ≤ ∫ y in (0 : ℝ)..s, ‖φ' y‖ :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall fun y => norm_nonneg _) hn'i
    have h4 : ‖φ 0‖ ≤ ‖φ t‖ + ∫ y in (0 : ℝ)..s, ‖φ' y‖ := by linarith
    nlinarith [norm_nonneg (φ 0), mul_nonneg (norm_nonneg (φ 0)) (sub_nonneg.2 h4),
      sq_nonneg (‖φ t‖ - ∫ y in (0 : ℝ)..s, ‖φ' y‖),
      sq_nonneg (‖φ t‖ + (∫ y in (0 : ℝ)..s, ‖φ' y‖) - ‖φ 0‖)]
  have hmono : ∫ _ in (0 : ℝ)..s, ‖φ 0‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..s, (2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2) :=
    intervalIntegral.integral_mono_on hs.le intervalIntegrable_const
      ((hA.const_mul 2).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hA.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hmono
  simp only [sub_zero, smul_eq_mul] at hmono
  have hCS : (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 :=
    sq_intervalIntegral_le_mul_intervalIntegral_sq (fun t => ‖φ' t‖) s hs hn'
  have key : ‖φ 0‖ ^ 2 * s ≤
      2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hCS hs.le]
  calc ‖φ 0‖ ^ 2 = ‖φ 0‖ ^ 2 * s / s := by field_simp
    _ ≤ (2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2) / s := by
      gcongr
    _ = 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
      field_simp
end GlobalTheory
