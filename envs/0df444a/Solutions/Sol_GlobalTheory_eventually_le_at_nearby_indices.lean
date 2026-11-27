-- Prove2me | solution 1 for GlobalTheory.eventually_le_at_nearby_indices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:15.138385+00:00
-- url     : https://prove2.me/submissions/080b5473-fe00-40db-bbf2-9d98f287a417

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EventuallyLeAtNearbyIndices
import Theorems.Thm_GlobalTheory_tendsto_comp_div_pow_of_ratio
import Theorems.Thm_GlobalTheory_tendsto_natDiv_div_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (d b c : ℕ) (f : ℝ → ℕ → ℝ) (g : ℤ → ℝ) (f₀ : ℤ → ℝ) (α β : ℝ), 0 < d → 0 < b →
      (∀ η, 0 ≤ η → Tendsto (fun j : ℕ => f η j / (j : ℝ) ^ d) atTop (𝓝 (α + β * η))) →
      (∀ j : ℕ, f₀ j = f 0 j) → (∀ η, 0 < η → ∀ᶠ j : ℕ in atTop, g j ≤ f η j) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
        g (b * M + (M / n : ℕ) - c) ≤ f₀ (b * M - c) + ε * (M : ℝ) ^ d := by
  intro d b c f g f₀ α β _hd hb hf hf₀ hg ε hε
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hlim : Tendsto (fun n : ℕ => α * ((b:ℝ) + 1 / (n:ℝ)) ^ d) atTop
      (𝓝 (α * (b:ℝ) ^ d)) := by
    have := ((tendsto_one_div_atTop_nhds_zero_nat.const_add (b : ℝ)).pow d).const_mul α
    rwa [add_zero] at this
  have hn : ∀ᶠ n : ℕ in atTop, α * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * (b:ℝ) ^ d + ε / 3 :=
    (tendsto_order.1 hlim).2 _ (by linarith)
  filter_upwards [hn, eventually_gt_atTop 0] with n hn hn0
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hrpos : (0:ℝ) < (b:ℝ) + 1 / (n:ℝ) := by positivity
  obtain ⟨η, hη, hηlt⟩ : ∃ η : ℝ, 0 < η ∧
      (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 := by
    have hcont : Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝[>] 0)
        (𝓝 (α * ((b:ℝ) + 1 / (n:ℝ)) ^ d)) := by
      have : Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝 0)
          (𝓝 ((α + β * 0) * ((b:ℝ) + 1 / (n:ℝ)) ^ d)) :=
        ((continuous_const.add (continuous_const.mul continuous_id)).mul
          continuous_const).tendsto 0
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev := (hcont.eventually (gt_mem_nhds (show α * ((b:ℝ) + 1 / (n:ℝ)) ^ d <
      α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 by linarith))).and
      (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0:ℝ), x ∈ Set.Ioi 0)
    obtain ⟨η, h1, h2⟩ := hev.exists
    exact ⟨η, h2, h1⟩
  have hc0 : Tendsto (fun M : ℕ => (c:ℝ) / M) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hr₁ : Tendsto (fun M : ℕ => ((b * M + M / n - c : ℕ) : ℝ) / M) atTop
      (𝓝 ((b:ℝ) + 1 / (n:ℝ))) := by
    have : Tendsto (fun M : ℕ => (b:ℝ) + ((M / n : ℕ) : ℝ) / M - (c:ℝ) / M) atTop
        (𝓝 ((b:ℝ) + 1 / n - 0)) :=
      ((tendsto_natDiv_div_self n hn0).const_add _).sub hc0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0
    have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hle : c ≤ b * M + M / n :=
      le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
  have hr₀ : Tendsto (fun M : ℕ => ((b * M - c : ℕ) : ℝ) / M) atTop (𝓝 (b:ℝ)) := by
    have : Tendsto (fun M : ℕ => (b:ℝ) - (c:ℝ) / M) atTop (𝓝 ((b:ℝ) - 0)) :=
      tendsto_const_nhds.sub hc0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0
    have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hle : c ≤ b * M := le_trans hMc (Nat.le_mul_of_pos_left M hb)
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
  obtain ⟨hA, hu₁⟩ := tendsto_comp_div_pow_of_ratio d (f η) (α + β * η) _ _ hrpos
    (hf η hη.le) hr₁
  obtain ⟨hB, -⟩ := tendsto_comp_div_pow_of_ratio d (f 0) (α + β * 0) _ _ hbR
    (hf 0 le_rfl) hr₀
  have hev : ∀ᶠ M : ℕ in atTop,
      f η (b * M + M / n - c) / (M:ℝ) ^ d - f 0 (b * M - c) / (M:ℝ) ^ d < ε :=
    (tendsto_order.1 (hA.sub hB)).2 ε (by rw [mul_zero, add_zero]; linarith)
  filter_upwards [hev, hu₁.eventually (hg η hη), eventually_ge_atTop c, eventually_gt_atTop 0]
    with M hM hgM hMc hM0
  have hMR : (0:ℝ) < M := by exact_mod_cast hM0
  have hle1 : c ≤ b * M + M / n :=
    le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))
  have hle0 : c ≤ b * M := le_trans hMc (Nat.le_mul_of_pos_left M hb)
  have e1 : ((b:ℤ) * M + ((M / n : ℕ) : ℤ) - c) = ((b * M + M / n - c : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle1]; push_cast; ring
  have e0 : ((b:ℤ) * M - c) = ((b * M - c : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle0]; push_cast; ring
  rw [e1, e0, hf₀]
  have hpos : 0 < (M:ℝ) ^ d := pow_pos hMR d
  rw [← sub_div, div_lt_iff₀ hpos] at hM
  linarith
end GlobalTheory
