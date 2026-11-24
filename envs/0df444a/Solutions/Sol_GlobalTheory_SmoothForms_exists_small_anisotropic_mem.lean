-- Prove2me | solution 1 for GlobalTheory.SmoothForms.exists_small_anisotropic_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:51:58.474596+00:00
-- url     : https://prove2.me/submissions/f583b9a4-57e7-4a45-ba0c-eda8ff27657e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalAnisotropicFrameBoundedCM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SmoothForms
theorem _root_.solution {V : Type} [AddCommGroup V] [Module E V] {h : V →ₗ[E] V →ₗ⋆[E] E}
    {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B₀ : ℝ} (H : Sized h Λ N ν B₀) {B : ℝ} (hB : 2 ≤ B)
    {W : Submodule E V} (hW : W ≠ ⊥) (hnd : ∀ y ∈ W, (∀ x ∈ W, h y x = 0) → y = 0)
    (hsp : W ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}) :
    ∃ v, v ∈ Λ ∧ v ∈ W ∧ h v v ≠ 0 ∧ ν v ≤ B ^ 4 := by
  have hB1 : B ≤ B ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  obtain ⟨x, ⟨hx1, hx2, hx3⟩, hx0⟩ : ∃ x ∈ {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}, x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hW (le_bot_iff.1 (hsp.trans (Submodule.span_eq_bot.2 hc).le))
  obtain ⟨y, ⟨hy1, hy2, hy3⟩, hxy⟩ : ∃ y ∈ {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}, h x y ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hx0 (hnd x hx2 fun z hz => ?_)
    have : Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} ≤ LinearMap.ker (h x) :=
      Submodule.span_le.2 fun z hz => hc z hz
    exact this (hsp hz)
  by_cases hxx : h x x = 0
  swap
  · exact ⟨x, hx1, hx2, hxx, hx3.trans hB1⟩
  by_cases hyy : h y y = 0
  swap
  · exact ⟨y, hy1, hy2, hyy, hy3.trans hB1⟩
  refine ⟨x + h x y • y, Λ.add_mem hx1 (H.stable _ (H.int x hx1 y hy1) y hy1),
    W.add_mem hx2 (W.smul_mem _ hy2), ?_, ?_⟩
  · have : h (x + h x y • y) (x + h x y • y) = 2 * (h x y * star (h x y)) := by
      simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, hxx, hyy, H.symm x y,
        smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
      ring
    rw [this]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hxy (star_ne_zero.2 hxy))
  · have h0 : (0 : ℝ) ≤ B := by linarith
    have h1 : house (h x y) ≤ B * B := (H.form_le x y).trans (mul_le_mul hx3 hy3 (H.nonneg _) h0)
    have h2 : ν (h x y • y) ≤ B * B * B :=
      (H.smul_le _ _).trans (mul_le_mul h1 hy3 (H.nonneg _) (by positivity))
    have h3 : B ≤ B ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have h4 : 2 * B ^ 3 ≤ B * B ^ 3 := mul_le_mul_of_nonneg_right hB (by positivity)
    have := H.add_le x (h x y • y)
    nlinarith
end GlobalTheory.SmoothForms
