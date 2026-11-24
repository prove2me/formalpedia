-- Prove2me | solution 1 for GlobalTheory.RealZeros.eta_eq_of_strip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:42:48.912309+00:00
-- url     : https://prove2.me/submissions/5da04001-0f5e-4bed-a19d-e1dc557b65f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
import Theorems.Thm_GlobalTheory_RealZeros_differentiableOn_tsum_br
import Theorems.Thm_GlobalTheory_RealZeros_convex_re_pos
import Theorems.Thm_GlobalTheory_RealZeros_eta_eq_of_one_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros
namespace GlobalTheory.RealZeros
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s = ∑' k, br 2 1 2 k s := by
  have hF : ∀ U : Set ℂ, IsOpen U → (1 : ℂ) ∉ U →
      AnalyticOnNhd ℂ (fun s => (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s) U := by
    intro U hU h1
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    have hz1 : z ≠ 1 := fun h => h1 (h ▸ hz)
    exact (((differentiableAt_const _).sub ((differentiableAt_id.neg.const_cpow
      (Or.inl two_ne_zero)).const_mul _)).mul
      (differentiableAt_riemannZeta hz1)).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ (fun s => ∑' k, br 2 1 2 k s) {s | 0 < s.re} :=
    (differentiableOn_tsum_br (by norm_num) le_rfl (by norm_num)).analyticOnNhd
      (isOpen_lt continuous_const continuous_re)
  have hAo : IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}) :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im)
  have hBo : IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1}) :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hA := (hF _ hAo (by simp)).eqOn_of_preconnected_of_eventuallyEq
    (hG.mono Set.inter_subset_left)
    (convex_re_pos.inter (convex_halfSpace_im_gt 0)).isPreconnected (z₀ := 2 + I) (by simp)
    (by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℝ) < (2 + I : ℂ).re by simp)] with z hz using eta_eq_of_one_lt hz)
  have hB := (hF _ hBo (by simp)).eqOn_of_preconnected_of_eventuallyEq
    (hG.mono Set.inter_subset_left)
    (convex_re_pos.inter (convex_halfSpace_re_lt 1)).isPreconnected (z₀ := 2⁻¹ + I)
    (by norm_num)
    (by
      filter_upwards [hAo.mem_nhds (show (2⁻¹ + I : ℂ) ∈ _ by norm_num)] with z hz using hA hz)
  exact hB ⟨hs, hs1⟩
end GlobalTheory.RealZeros
