-- Prove2me | solution 1 for InconsistentDR.Shadow.proposition_2_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:57:41.885147+00:00
-- url     : https://prove2.me/submissions/f62eee0b-e65c-4f04-a245-c0eaeaf6c859

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (hzer : ∃ x, ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g x, a + b = 0) :
    {x | ∀ y, f x + g x ≤ f y + g y} = {x | (0 : X) ∈ subgrad (f + g) x} ∧
      {x | (0 : X) ∈ subgrad (f + g) x} =
        {x | ∃ a ∈ subgrad f x, ∃ b ∈ subgrad g x, a + b = 0} := by
  obtain ⟨x0, a, ha, b, hb, hab⟩ := hzer
  obtain ⟨F0, hF0⟩ : ∃ r : ℝ, f x0 = r := ⟨(f x0).toReal, (EReal.coe_toReal ha.2.1 ha.1).symm⟩
  obtain ⟨G0, hG0⟩ : ∃ r : ℝ, g x0 = r := ⟨(g x0).toReal, (EReal.coe_toReal hb.2.1 hb.1).symm⟩
  -- zero subgradient of the sum ↔ minimizer with finite value
  have hzero : ∀ x, (0 : X) ∈ subgrad (f + g) x ↔ ∀ y, f x + g x ≤ f y + g y := by
    intro x
    constructor
    · rintro ⟨-, -, h⟩ y
      have := h y
      simpa using this
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · simp only [Pi.add_apply]
        exact EReal.add_ne_bot_iff.mpr ⟨hf.1 x, hg.1 x⟩
      · simp only [Pi.add_apply]
        intro htop
        have := h x0
        rw [htop, hF0, hG0, top_le_iff, ← EReal.coe_add] at this
        exact EReal.coe_ne_top _ this
      · intro u
        simpa using h u
  refine ⟨?_, ?_⟩
  · ext x
    exact (hzero x).symm
  · ext x
    simp only [Set.mem_setOf_eq]
    rw [hzero x]
    constructor
    · intro hmin
      -- `f x`, `g x` are finite
      have hlt := hmin x0
      rw [hF0, hG0] at hlt
      have hfx : f x ≠ ⊤ := by
        intro h; rw [h, EReal.top_add_of_ne_bot (hg.1 x), top_le_iff, ← EReal.coe_add] at hlt
        exact EReal.coe_ne_top _ hlt
      have hgx : g x ≠ ⊤ := by
        intro h; rw [h, EReal.add_top_of_ne_bot (hf.1 x), top_le_iff, ← EReal.coe_add] at hlt
        exact EReal.coe_ne_top _ hlt
      obtain ⟨F, hF⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal hfx (hf.1 x)).symm⟩
      obtain ⟨G, hG⟩ : ∃ r : ℝ, g x = r := ⟨(g x).toReal, (EReal.coe_toReal hgx (hg.1 x)).symm⟩
      have h1 := ha.2.2 x
      have h2 := hb.2.2 x
      rw [hF0, hF] at h1
      rw [hG0, hG] at h2
      rw [hF, hG] at hlt
      have h1' : F0 + ⟪x - x0, a⟫_ℝ ≤ F := by exact_mod_cast h1
      have h2' : G0 + ⟪x - x0, b⟫_ℝ ≤ G := by exact_mod_cast h2
      have hlt' : F + G ≤ F0 + G0 := by exact_mod_cast hlt
      have hb' : b = -a := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hab
      rw [hb', inner_neg_right] at h2'
      have eF : F = F0 + ⟪x - x0, a⟫_ℝ := by linarith
      have eG : G = G0 - ⟪x - x0, a⟫_ℝ := by linarith
      refine ⟨a, ⟨?_, ?_, ?_⟩, b, ⟨?_, ?_, ?_⟩, hab⟩
      · rw [hF]; exact EReal.coe_ne_bot F
      · rw [hF]; exact EReal.coe_ne_top F
      · intro u
        have := ha.2.2 u
        rw [hF0] at this
        rw [hF]
        have hs : ⟪u - x, a⟫_ℝ = ⟪u - x0, a⟫_ℝ - ⟪x - x0, a⟫_ℝ := by
          rw [← inner_sub_left]; congr 1; abel
        have e : F + ⟪u - x, a⟫_ℝ = F0 + ⟪u - x0, a⟫_ℝ := by
          rw [eF, hs]; ring
        rw [← EReal.coe_add, e, EReal.coe_add]; exact this
      · rw [hG]; exact EReal.coe_ne_bot G
      · rw [hG]; exact EReal.coe_ne_top G
      · intro u
        have := hb.2.2 u
        rw [hG0] at this
        rw [hG]
        have hs : ⟪u - x, b⟫_ℝ = ⟪u - x0, b⟫_ℝ - ⟪x - x0, b⟫_ℝ := by
          rw [← inner_sub_left]; congr 1; abel
        have hxb : ⟪x - x0, b⟫_ℝ = -⟪x - x0, a⟫_ℝ := by rw [hb', inner_neg_right]
        have e : G + ⟪u - x, b⟫_ℝ = G0 + ⟪u - x0, b⟫_ℝ := by
          rw [eG, hs, hxb]; ring
        rw [← EReal.coe_add, e, EReal.coe_add]; exact this
    · rintro ⟨a', ha', b', hb', hab'⟩ y
      have h1 := ha'.2.2 y
      have h2 := hb'.2.2 y
      have hs : ⟪y - x, a'⟫_ℝ + ⟪y - x, b'⟫_ℝ = 0 := by
        rw [← inner_add_right, hab', inner_zero_right]
      calc f x + g x = f x + g x + (((⟪y - x, a'⟫_ℝ + ⟪y - x, b'⟫_ℝ : ℝ)) : EReal) := by
              rw [hs]; simp
        _ = (f x + ((⟪y - x, a'⟫_ℝ : ℝ) : EReal)) + (g x + ((⟪y - x, b'⟫_ℝ : ℝ) : EReal)) := by
              rw [EReal.coe_add]
              obtain ⟨F, hF⟩ : ∃ r : ℝ, f x = r :=
                ⟨(f x).toReal, (EReal.coe_toReal ha'.2.1 ha'.1).symm⟩
              obtain ⟨G, hG⟩ : ∃ r : ℝ, g x = r :=
                ⟨(g x).toReal, (EReal.coe_toReal hb'.2.1 hb'.1).symm⟩
              rw [hF, hG]
              norm_cast
              ring
        _ ≤ f y + g y := add_le_add h1 h2
