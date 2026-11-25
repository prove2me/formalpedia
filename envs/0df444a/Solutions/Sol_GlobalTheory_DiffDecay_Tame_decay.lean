-- Prove2me | solution 1 for GlobalTheory.DiffDecay.Tame.decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:38:34.647001+00:00
-- url     : https://prove2.me/submissions/91e2c45a-fc1a-4cae-baf2-d0d4533941a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSmulSemi
import Theorems.Thm_GlobalTheory_DiffDecay_continuous_smul_semi
import Theorems.Thm_GlobalTheory_DiffDecay_Tame_growth
import Theorems.Thm_GlobalTheory_DiffDecay_Tame_iter

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
variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {W : Type} [SeminormedAddCommGroup W]
namespace GlobalTheory.DiffDecay
namespace Tame
theorem _root_.solution {R : W → E →ₗ[ℂ] E} (h : Tame R) (p : Seminorm ℂ E) (hp : Continuous p) (A C : ℝ) (N : ℕ) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ (s : W) (r : ℝ), 0 ≤ r → ‖s‖ ≤ A * r →
      (0 < r → ∃ u, ‖u‖ * r ≤ C ∧ ∀ f, p (R s (R u f + f)) = 0) → ∀ f, p (R s f) ≤ q f * (1 + r) ^ (-(N : ℝ)) := by
  obtain ⟨q₁, M, hq₁, hb₁⟩ := h.growth p hp
  obtain ⟨q₂, hq₂, hb₂⟩ := h.iter (M + N) q₁ hq₁
  set r₀ := max C 1 with hr₀
  obtain ⟨q₃, hq₃, e₃⟩ := continuous_smul_semi ((1 + |A|) ^ M * (1 + r₀) ^ (M + N)) q₁ hq₁
  obtain ⟨q₄, hq₄, e₄⟩ := continuous_smul_semi ((1 + |A|) ^ M * (2 * r₀) ^ (M + N)) q₂ hq₂
  have hr1 : 1 ≤ r₀ := le_max_right _ _
  refine ⟨q₃ + q₄, (hq₃.add hq₄ : Continuous fun f => q₃ f + q₄ f), fun s r hr hs hu f => ?_⟩
  have hs' : 1 + ‖s‖ ≤ (1 + |A|) * (1 + r) := by
    nlinarith [le_abs_self A, abs_nonneg A, mul_le_mul_of_nonneg_right (le_abs_self A) hr]
  have hpow : (1 + ‖s‖) ^ M ≤ (1 + |A|) ^ M * (1 + r) ^ M := by
    rw [← mul_pow]; gcongr
  rw [Real.rpow_neg (by linarith), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity), Seminorm.add_apply]
  have h3 := apply_nonneg q₃ f
  have h4 := apply_nonneg q₄ f
  rcases le_or_gt r r₀ with hrr | hrr
  · refine le_trans ?_ (le_add_of_nonneg_right h4)
    rw [e₃, abs_of_nonneg (by positivity)]
    calc p (R s f) * (1 + r) ^ N ≤ ((1 + |A|) ^ M * (1 + r) ^ M * q₁ f) * (1 + r) ^ N := by
          gcongr; exact (hb₁ s f).trans (by gcongr)
      _ = (1 + |A|) ^ M * (1 + r) ^ (M + N) * q₁ f := by ring
      _ ≤ _ := by gcongr
  · refine le_trans ?_ (le_add_of_nonneg_left h3)
    obtain ⟨u, huC, hu0⟩ := hu (by linarith)
    have hC : C ≤ r₀ := le_max_left _ _
    have hu1 : ‖u‖ ≤ 1 := by
      by_contra hcon
      nlinarith [not_le.1 hcon]
    have hstep : ∀ g, p (R s g) ≤ p (R s ((R u - 1) g)) := fun g => by
      have e1 : (2 : ℂ) • R s g = R s (R u g + g) - R s ((R u - 1) g) := by
        rw [← map_sub, ← map_smul, LinearMap.sub_apply, Module.End.one_apply, two_smul]; congr 1; abel
      have e2 := map_sub_le_add p (R s (R u g + g)) (R s ((R u - 1) g))
      rw [← e1, map_smul_eq_mul, hu0] at e2
      have := apply_nonneg p (R s g)
      simp only [Complex.norm_ofNat] at e2
      linarith
    have hit : ∀ j : ℕ, p (R s f) ≤ p (R s (((R u - 1) ^ j) f)) := fun j => by
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact ih.trans (hstep _)
    have hur : ‖u‖ * (1 + r) ≤ 2 * r₀ := by nlinarith
    rw [e₄, abs_of_nonneg (by positivity)]
    calc p (R s f) * (1 + r) ^ N ≤ ((1 + |A|) ^ M * (1 + r) ^ M * (‖u‖ ^ (M + N) * q₂ f)) * (1 + r) ^ N := by
          gcongr
          refine (hit (M + N)).trans ((hb₁ s _).trans ?_)
          gcongr
          exact hb₂ u hu1 f
      _ = (1 + |A|) ^ M * (‖u‖ * (1 + r)) ^ (M + N) * q₂ f := by rw [mul_pow ‖u‖]; ring
      _ ≤ _ := by gcongr
end Tame
end GlobalTheory.DiffDecay
