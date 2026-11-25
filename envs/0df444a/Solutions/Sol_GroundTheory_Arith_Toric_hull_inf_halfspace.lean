-- Prove2me | solution 1 for GroundTheory.Arith.Toric.hull_inf_halfspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:48.438527+00:00
-- url     : https://prove2.me/submissions/12805a8e-2413-461f-9c11-482c7a2a1763

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Theorems.Thm_GroundTheory_Arith_Toric_nonneg_of_mem_hull
import Theorems.Thm_GroundTheory_Arith_Toric_exists_dual_neg_of_not_mem_hull_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
namespace GroundTheory.Arith.Toric
theorem _root_.solution (S : Finset V) (g : Dual 𝕜 V) [DecidableEq V] :
    hull 𝕜 (S : Set V) ⊓ (positive 𝕜 𝕜).comap g =
      hull 𝕜 ((S.filter (fun s => 0 ≤ g s) ∪
        ((S ×ˢ S).filter (fun st => 0 < g st.1 ∧ g st.2 < 0)).image
          (fun st => g st.1 • st.2 - g st.2 • st.1) : Finset V) : Set V) := by
  set G : Finset V := S.filter (fun s => 0 ≤ g s) ∪
        ((S ×ˢ S).filter (fun st => 0 < g st.1 ∧ g st.2 < 0)).image
          (fun st => g st.1 • st.2 - g st.2 • st.1) with hG
  have memP : ∀ y ∈ S, 0 ≤ g y → y ∈ G := fun y hy hgy =>
    Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hy, hgy⟩)
  have memQ : ∀ s ∈ S, ∀ t ∈ S, 0 < g s → g t < 0 → g s • t - g t • s ∈ G :=
    fun s hs t ht h1 h2 => Finset.mem_union_right _
      (Finset.mem_image.2 ⟨(s, t), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs, ht⟩, h1, h2⟩, rfl⟩)
  apply le_antisymm
  · rintro x ⟨hxS, hxg⟩
    have hxg : 0 ≤ g x := by simpa [mem_comap, mem_positive] using hxg
    by_contra hxG
    obtain ⟨h, hh, hhx⟩ := exists_dual_neg_of_not_mem_hull_finset G hxG
    obtain ⟨l, hl0, hlQ, hlP⟩ : ∃ l : 𝕜, 0 ≤ l ∧ (∀ t ∈ S, g t < 0 → h t / g t ≤ l) ∧
        (∀ s ∈ S, 0 < g s → l ≤ h s / g s) := by
      by_cases hT : (S.filter (fun t => g t < 0)).Nonempty
      · obtain ⟨t0, ht0, hmax⟩ := Finset.exists_max_image _ (fun t => h t / g t) hT
        obtain ⟨ht0S, hgt0⟩ := Finset.mem_filter.1 ht0
        refine ⟨max 0 (h t0 / g t0), le_max_left _ _,
          fun t ht hgt => (hmax t (Finset.mem_filter.2 ⟨ht, hgt⟩)).trans (le_max_right _ _),
          fun s hs hgs => max_le (div_nonneg (hh s (memP s hs hgs.le)) hgs.le) ?_⟩
        have h1 := hh _ (memQ s hs t0 ht0S hgs hgt0)
        simp only [map_sub, map_smul, smul_eq_mul] at h1
        rw [div_le_iff_of_neg hgt0, div_mul_eq_mul_div, div_le_iff₀ hgs]
        nlinarith
      · refine ⟨0, le_rfl, fun t ht hgt => absurd ⟨t, Finset.mem_filter.2 ⟨ht, hgt⟩⟩ hT,
          fun s hs hgs => div_nonneg (hh s (memP s hs hgs.le)) hgs.le⟩
    have hk : ∀ y ∈ (S : Set V), 0 ≤ (h - l • g) y := by
      intro y hy
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rcases lt_trichotomy (g y) 0 with hgy | hgy | hgy
      · have := hlQ y hy hgy
        rw [div_le_iff_of_neg hgy] at this
        linarith
      · rw [hgy, mul_zero, sub_zero]
        exact hh y (memP y hy hgy.ge)
      · have := hlP y hy hgy
        rw [le_div_iff₀ hgy] at this
        linarith
    have h1 := nonneg_of_mem_hull hk hxS
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    nlinarith [mul_nonneg hl0 hxg]
  · rw [Submodule.span_le]
    intro y hy
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hy) with hy | hy
    · obtain ⟨hyS, hgy⟩ := Finset.mem_filter.1 hy
      exact ⟨subset_hull hyS, by simpa [mem_comap, mem_positive] using hgy⟩
    · obtain ⟨⟨s, t⟩, hst, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨hst, h1, h2⟩ := Finset.mem_filter.1 hst
      obtain ⟨hs, ht⟩ := Finset.mem_product.1 hst
      refine ⟨?_, ?_⟩
      · rw [sub_eq_add_neg, ← neg_smul]
        exact add_mem (smul_mem _ h1.le (subset_hull ht))
          (smul_mem _ (neg_nonneg.2 h2.le) (subset_hull hs))
      · simp [mul_comm]
end GroundTheory.Arith.Toric
