-- Prove2me | solution 1 for GlobalTheory.LogDerivHigher.exists_entire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:17:19.628466+00:00
-- url     : https://prove2.me/submissions/bcdc1ec6-65dd-416b-8fac-4db85f0e1cf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Theorems.Thm_GlobalTheory_LogDerivHigher_growth_triv
import Theorems.Thm_GlobalTheory_norm_LFunction_le_poly_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.LogDerivHigher
namespace GlobalTheory.LogDerivHigher
theorem _root_.solution : ∃ B : ℝ, 0 < B ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z : ℂ, -(7 / 4 : ℝ) ≤ z.re → ‖F z‖ ≤ B * (q : ℝ) ^ 5 * (‖z‖ + 2) ^ 5) ∧
      (∀ z : ℂ, z.re = 2 → ‖LFunction χ z‖ ≤ ‖F z‖) ∧
      (∀ z : ℂ, F z = 0 ↔ (χ ≠ 1 ∨ z ≠ 1) ∧ LFunction χ z = 0) ∧
      (∀ z : ℂ, F z = 0 → analyticOrderNatAt F z = ord χ z) ∧
      ∀ s : ℂ, 1 < s.re → deriv F s / F s =
        deriv (LFunction χ) s / LFunction χ s + (if χ = 1 then 1 else 0) / (s - 1) := by
  obtain ⟨B, hB, G⟩ := growth_triv
  obtain ⟨B', hB', G'⟩ := norm_LFunction_le_poly_left
  refine ⟨B + B', by positivity, fun q _ χ => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  by_cases hχ : χ = 1
  · subst hχ
    have hF : ∀ z, z ≠ 1 → LFunctionTrivChar₁ q z
        = (z - 1) * LFunction (1 : DirichletCharacter ℂ q) z := fun z hz => by
      rw [LFunctionTrivChar₁, Function.update_of_ne hz]
    have hne : ∀ z, LFunctionTrivChar₁ q z = 0 → z ≠ 1 := fun z hz h =>
      LFunctionTrivChar₁_apply_one_ne_zero q (h ▸ hz)
    refine ⟨LFunctionTrivChar₁ q, differentiable_LFunctionTrivChar₁ q, fun z hz => ?_,
      fun z hz => ?_, fun z => ?_, fun z hz => ?_, fun s hs => ?_⟩
    · refine (G q z hz).trans ?_
      gcongr; linarith
    · rw [hF z (by rintro rfl; norm_num at hz), norm_mul]
      refine le_mul_of_one_le_left (norm_nonneg _) ?_
      have := Complex.re_le_norm (z - 1)
      rw [sub_re, hz, one_re] at this
      linarith
    · constructor
      · intro h
        have h1 := hne z h
        rw [hF z h1] at h
        exact ⟨Or.inr h1, (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 h1)⟩
      · rintro ⟨h1, h2⟩
        rw [hF z (h1.resolve_left (by simp)), h2, mul_zero]
    · have h1 := hne z hz
      have hev : LFunctionTrivChar₁ q =ᶠ[𝓝 z]
          (fun z => z - 1) * LFunction (1 : DirichletCharacter ℂ q) := by
        filter_upwards [isOpen_ne.mem_nhds h1] with w hw
        exact hF w hw
      have a1 : AnalyticAt ℂ (fun z : ℂ => z - 1) z := by fun_prop
      have a2 : AnalyticAt ℂ (LFunction (1 : DirichletCharacter ℂ q)) z := by
        refine DifferentiableOn.analyticAt (s := {1}ᶜ) (fun w hw => ?_) (isOpen_ne.mem_nhds h1)
        exact (differentiableAt_LFunction _ w (Or.inl hw)).differentiableWithinAt
      unfold ord analyticOrderNatAt
      rw [analyticOrderAt_congr hev, analyticOrderAt_mul a1 a2,
        a1.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 h1), zero_add]
    · have h1 : s ≠ 1 := by rintro rfl; simp at hs
      have h2 : LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 :=
        LFunction_ne_zero_of_one_le_re _ (Or.inr h1) hs.le
      have h3 := sub_ne_zero.2 h1
      rw [deriv_LFunctionTrivChar₁_apply_of_ne_one q h1, hF s h1, if_pos rfl, LFunctionTrivChar]
      field_simp
  · refine ⟨LFunction χ, differentiable_LFunction hχ, fun z hz => ?_, fun _ _ => le_rfl,
      fun z => by simp [hχ], fun _ _ => rfl, fun s _ => by simp [hχ]⟩
    refine (G' q χ hχ z hz).trans ?_
    have h2 : (1 : ℝ) ≤ ‖z‖ + 2 := by linarith [norm_nonneg z]
    gcongr
    · linarith
    all_goals first | assumption | norm_num
end GlobalTheory.LogDerivHigher
