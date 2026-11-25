-- Prove2me | solution 1 for GlobalTheory.DiffDecay.tame_heisOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:38:46.263986+00:00
-- url     : https://prove2.me/submissions/036deca6-71e5-49b0-85f7-9e1da1c1bbec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSmulSemi
import Theorems.Thm_GlobalTheory_DiffDecay_continuous_smul_semi
import Theorems.Thm_GlobalTheory_DiffDecay_Tame_growth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.DiffDecay
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : Type} [SeminormedAddCommGroup W]
namespace GlobalTheory.DiffDecay
theorem _root_.solution
    (hT : ∀ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p →
      ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (a : V) (f : SchwartzMap V ℂ),
        p (SchwartzMap.compSubConstCLM ℂ (-a) f - f) ≤ ‖a‖ * (1 + ‖a‖) ^ M * q f)
    (hP : ∀ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p →
      ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (L : V →L[ℝ] ℝ) (k : ℝ) (f : SchwartzMap V ℂ),
        p (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ M * q f)
    (L : W → V →L[ℝ] ℝ) (k : W → ℝ) (a : W → V) (c : ℝ) (hc : 1 ≤ c) (hL : ∀ w, ‖L w‖ ≤ c * ‖w‖)
    (hk : ∀ w, |k w| ≤ c * ‖w‖ ^ 2) (ha : ∀ w, ‖a w‖ ≤ ‖w‖) :
    Tame fun w => (heisOp (L w) (k w) (a w)).toLinearMap := by
  intro p hp
  obtain ⟨q₁, M₁, hq₁, hb₁⟩ := hP p hp
  obtain ⟨q₂, M₂, hq₂, hb₂⟩ := hT p hp
  have hTt : Tame fun a : V => (SchwartzMap.compSubConstCLM ℂ (-a) : SchwartzMap V ℂ →L[ℂ] _).toLinearMap := hT
  obtain ⟨q₃, M₃, hq₃, hb₃⟩ := hTt.growth q₁ hq₁
  obtain ⟨q₄, hq₄, e₄⟩ := continuous_smul_semi (c ^ (M₁ + 1)) q₃ hq₃
  refine ⟨q₂ + q₄, M₁ + M₂ + M₃ + 1, (hq₂.add hq₄ : Continuous fun f => q₂ f + q₄ f), fun w f => ?_⟩
  set g := SchwartzMap.compSubConstCLM ℂ (-(a w)) f with hg
  have h1 := map_add_le_add p (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L w y + k w)) g - g) (g - f)
  rw [sub_add_sub_cancel] at h1
  refine le_trans h1 ?_
  have hw := norm_nonneg w
  have h1w : 1 ≤ 1 + ‖w‖ := by linarith
  have hc0 : 0 < c := by linarith
  rw [Seminorm.add_apply, mul_add, add_comm]
  refine add_le_add ((hb₂ _ f).trans ?_) ((hb₁ _ _ g).trans ?_)
  · have := ha w
    calc _ ≤ ‖w‖ * (1 + ‖w‖) ^ M₂ * q₂ f := by gcongr
      _ ≤ _ := by gcongr; omega
  · have h2 : q₁ g ≤ (1 + ‖w‖) ^ M₃ * q₃ f := (hb₃ (a w) f).trans (by have := ha w; gcongr)
    have h3 : ‖L w‖ + |k w| ≤ c * (‖w‖ * (1 + ‖w‖)) := by nlinarith [hL w, hk w]
    have h4 : 1 + ‖L w‖ ≤ c * (1 + ‖w‖) := by nlinarith [hL w]
    rw [e₄, abs_of_nonneg (pow_nonneg hc0.le _)]
    have h5 := apply_nonneg q₃ f
    have h6 := apply_nonneg q₁ g
    calc _ ≤ c * (‖w‖ * (1 + ‖w‖)) * (c * (1 + ‖w‖)) ^ M₁ * ((1 + ‖w‖) ^ M₃ * q₃ f) := by gcongr
      _ = ‖w‖ * (1 + ‖w‖) ^ (M₁ + M₃ + 1) * (c ^ (M₁ + 1) * q₃ f) := by rw [mul_pow c]; ring
      _ ≤ _ := by gcongr; omega
end GlobalTheory.DiffDecay
