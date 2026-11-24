-- Prove2me | solution 1 for GlobalTheory.sq_scalar_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:53.315396+00:00
-- url     : https://prove2.me/submissions/3a492092-1fb3-4527-89b5-0b97f2fa3205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SqScalarCharacterOfDoubleCoverUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (G G' M H : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [Group M]
    [TopologicalSpace M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H] (pr : G' →* M) (s : G →* M)
    (om : G' →* (H ≃ₗᵢ[ℂ] H)) (ω : G →* (H ≃ₗᵢ[ℂ] H)) (ε : G'), IsCoveringMap pr → Function.Surjective pr →
    (∀ g, pr g = 1 → g = 1 ∨ g = ε) → (∀ v, om ε v = -v) → Continuous s → (∀ v, Continuous fun g => om g v) →
    (∀ v, Continuous fun g => ω g v) → (∀ g g', pr g' = s g → ∃ a : ℂ, ∀ v, ω g v = a • om g' v) →
    ∃ η : G → ℂ, (∀ g h, η (g * h) = η g * η h) ∧ Continuous η ∧ (∀ g, η g ≠ 0) ∧
      ∀ g g' (a : ℂ), pr g' = s g → (∀ v, ω g v = a • om g' v) → a ^ 2 = η g := by
  intro G G' M H _ _ _ _ _ _ _ _ _ pr s om ω ε hcov hsurj hker hε hs hom hω hrel
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : H)
  have huniq : ∀ g (g₁ g₂ : G') (a b : ℂ), pr g₁ = s g → pr g₂ = s g →
      (∀ v, ω g v = a • om g₁ v) → (∀ v, ω g v = b • om g₂ v) → a ^ 2 = b ^ 2 := by
    intro g g₁ g₂ a b h₁ h₂ ha hb
    have hw : om g₁ v₀ ≠ 0 := by
      intro h; apply hv₀; exact (om g₁).map_eq_zero_iff.mp h
    have hk : pr (g₁⁻¹ * g₂) = 1 := by simp [map_mul, map_inv, h₁, h₂]
    rcases hker _ hk with h | h
    · have h2 : g₂ = g₁ := by rw [← mul_inv_cancel_left g₁ g₂, h, mul_one]
      subst h2
      have : a • om g₂ v₀ = b • om g₂ v₀ := by rw [← ha, ← hb]
      have hab : a = b := smul_left_injective ℂ hw this
      rw [hab]
    · have h2 : g₂ = g₁ * ε := by rw [← h, mul_inv_cancel_left]
      have : a • om g₁ v₀ = (-b) • om g₁ v₀ := by
        rw [← ha, hb, h2, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hε,
          map_neg, smul_neg, neg_smul]
      have hab : a = -b := smul_left_injective ℂ hw this
      rw [hab]; ring
  have hlift : ∀ g, ∃ g', pr g' = s g := fun g => hsurj (s g)
  choose L hL using hlift
  choose A hA using fun g => hrel g (L g) (hL g)
  refine ⟨fun g => A g ^ 2, ?_, ?_, ?_, ?_⟩
  · intro g h
    have hmul : pr (L g * L h) = s (g * h) := by simp [map_mul, hL]
    have hsc : ∀ v, ω (g * h) v = (A g * A h) • om (L g * L h) v := by
      intro v
      rw [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hA h, LinearIsometryEquiv.map_smul,
        hA g, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, smul_smul, mul_comm (A h)]
    have := huniq (g * h) (L (g * h)) (L g * L h) _ _ (hL _) hmul (hA _) hsc
    simp only
    rw [this]; ring
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨e, he, hpe⟩ := hcov.isLocalHomeomorph (L g₀)
    have hopen : IsOpen (s ⁻¹' e.target) := e.open_target.preimage hs
    have hmem : g₀ ∈ s ⁻¹' e.target := by
      show s g₀ ∈ e.target
      rw [← hL g₀, hpe]; exact e.map_source he
    let f : G → ℂ := fun g => (inner ℂ (om (e.symm (s g)) v₀) (ω g v₀) / inner ℂ v₀ v₀) ^ 2
    have hf : ContinuousAt f g₀ := by
      have h1 : ContinuousAt (fun g => om (e.symm (s g)) v₀) g₀ :=
        (hom v₀).continuousAt.comp ((e.continuousAt_symm hmem).comp hs.continuousAt)
      exact ((h1.inner (hω v₀).continuousAt).div_const _).pow 2
    refine hf.congr ?_
    filter_upwards [hopen.mem_nhds hmem] with g hg
    have hpr : pr (e.symm (s g)) = s g := by rw [hpe]; exact e.right_inv hg
    obtain ⟨c, hc⟩ := hrel g _ hpr
    have hcval : c = inner ℂ (om (e.symm (s g)) v₀) (ω g v₀) / inner ℂ v₀ v₀ := by
      rw [hc, inner_smul_right, LinearIsometryEquiv.inner_map_map, mul_div_assoc,
        div_self (inner_self_ne_zero.2 hv₀), mul_one]
    show f g = A g ^ 2
    simp only [f]
    rw [← hcval]
    exact huniq g _ _ c (A g) hpr (hL g) hc (hA g)
  · intro g
    refine pow_ne_zero 2 ?_
    intro h0
    have := hA g v₀
    rw [h0, zero_smul] at this
    exact hv₀ ((ω g).map_eq_zero_iff.mp this)
  · intro g g' a hg' ha
    exact huniq g g' (L g) a (A g) hg' (hL g) ha (hA g)
end GlobalTheory
