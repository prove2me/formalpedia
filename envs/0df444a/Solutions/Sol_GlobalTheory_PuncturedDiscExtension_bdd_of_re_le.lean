-- Prove2me | solution 1 for GlobalTheory.PuncturedDiscExtension.bdd_of_re_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:40:09.072692+00:00
-- url     : https://prove2.me/submissions/407677bf-cb7d-4f33-aff7-25408c8ecb9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossZeroOfExpTwoPiIBound
import Theorems.Thm_GlobalTheory_PuncturedDiscExtension_analyticAt_update_of_bdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory GlobalTheory.PuncturedDiscExtension
namespace GlobalTheory.PuncturedDiscExtension
theorem _root_.solution {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    {M : ℝ} (hM : ∀ᶠ z in 𝓝[≠] (0:ℂ), (F z).re ≤ M) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B := by
  set g : ℂ → ℂ := fun z => (F z - ((M:ℂ) + 1))⁻¹ with hg
  have hre : ∀ᶠ z in 𝓝[≠] (0:ℂ), (F z - ((M:ℂ)+1)).re ≤ -1 := by
    filter_upwards [hM] with z hz
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hne : ∀ᶠ z in 𝓝[≠] (0:ℂ), F z - ((M:ℂ)+1) ≠ 0 := by
    filter_upwards [hre] with z hz h
    rw [h, Complex.zero_re] at hz
    linarith
  have hnorm : ∀ᶠ z in 𝓝[≠] (0:ℂ), 1 ≤ ‖F z - ((M:ℂ)+1)‖ := by
    filter_upwards [hre] with z hz
    have h1 := Complex.abs_re_le_norm (F z - ((M:ℂ)+1))
    have h2 : 1 ≤ |(F z - ((M:ℂ)+1)).re| := by
      rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hgd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g z := by
    filter_upwards [hd, hne] with z h1 h2
    exact (h1.sub_const _).inv h2
  have hgb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖g z‖ ≤ B := ⟨1, by
    filter_upwards [hnorm] with z hz
    simp only [hg, norm_inv]
    exact inv_le_one_of_one_le₀ hz⟩
  have ha := analyticAt_update_of_bdd hgd hgb
  set g' := Function.update g 0 (limUnder (𝓝[≠] (0:ℂ)) g) with hg'
  have hg'eq : ∀ z, z ≠ 0 → g' z = g z := fun z hz => Function.update_of_ne hz _ _
  by_cases hL : g' 0 = 0
  · exfalso
    rcases ha.eventually_constant_or_nhds_le_map_nhds with h | h
    · have hF : ∀ᶠ z in 𝓝[≠] (0:ℂ), False := by
        filter_upwards [nhdsWithin_le_nhds h, hne, self_mem_nhdsWithin] with z h1 h2 h3
        rw [hg'eq z h3, hL] at h1
        exact inv_ne_zero h2 h1
      exact hF.exists.elim fun _ h => h
    · have hS : ∀ᶠ z in 𝓝 (0:ℂ), g' z = 0 ∨ ((g' z)⁻¹).re ≤ -1 := by
        have h0 := eventually_nhdsWithin_iff.1 hre
        filter_upwards [h0] with z hz
        by_cases hz0 : z = 0
        · left; rw [hz0]; exact hL
        · right; rw [hg'eq z hz0]; simp only [hg, inv_inv]; exact hz hz0
      have hS' : {w : ℂ | w = 0 ∨ (w⁻¹).re ≤ -1} ∈ 𝓝 (g' 0) := h hS
      rw [hL] at hS'
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS'
      have hmem : ((ε/2 : ℝ) : ℂ) ∈ ball (0:ℂ) ε := by
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      rcases hball hmem with h1 | h1
      · have : (ε/2 : ℝ) = 0 := by exact_mod_cast h1
        linarith
      · rw [← Complex.ofReal_inv, Complex.ofReal_re] at h1
        have : 0 < (ε/2)⁻¹ := inv_pos.2 (by linarith)
        linarith
  · have hpos : 0 < ‖g' 0‖ := norm_pos_iff.2 hL
    have hc : ContinuousAt g' 0 := ha.continuousAt
    have hev : ∀ᶠ z in 𝓝 (0:ℂ), ‖g' 0‖ / 2 < ‖g' z‖ :=
      hc.norm.eventually (lt_mem_nhds (by linarith))
    refine ⟨‖(M:ℂ)+1‖ + 2 / ‖g' 0‖, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin, hne] with z h1 h2 h3
    rw [hg'eq z h2] at h1
    have hq : 0 < ‖F z - ((M:ℂ)+1)‖ := norm_pos_iff.2 h3
    have hgz : ‖g z‖ = ‖F z - ((M:ℂ)+1)‖⁻¹ := by simp only [hg, norm_inv]
    rw [hgz] at h1
    have key : ‖F z - ((M:ℂ)+1)‖ ≤ 2 / ‖g' 0‖ := by
      have h4 := mul_lt_mul_of_pos_right h1 hq
      rw [inv_mul_cancel₀ hq.ne'] at h4
      rw [le_div_iff₀ hpos]
      nlinarith
    have h5 := norm_sub_norm_le (F z) ((M:ℂ)+1)
    linarith
end GlobalTheory.PuncturedDiscExtension
