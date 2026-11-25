-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.stage_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:43:39.32638+00:00
-- url     : https://prove2.me/submissions/872eb46d-2005-491c-acc0-23fb70c1604f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_pairing_convolution
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_continuous_opT
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasDerivAt_opT
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_opT_succ
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_opT_mul
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport__C_147c0388f3f8
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_KC_succ
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_KC
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasCompactSupport_KC
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_contDiff_conv__C_0b797dd792e8
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_hasCompactSupport_conv__C_94b8ee077835
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_kern
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_rem
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_step_identity
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_kern_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    F 0 = (∫ u, opT a (n + 1) F u * KC a r n u) +
      ∑ j ∈ Finset.range (n + 1), ∫ u, F u * ρ a r j u := by
  induction n with
  | zero =>
    have hd : ∀ t, HasDerivAt F (deriv F t) t := fun t =>
      (hF.differentiable (by simp) t).hasDerivAt
    have h := step_identity (ha 0) (hr 0) hd (hF.continuous_deriv (by simp))
    rw [h, Finset.sum_range_one]
    congr 1
    congr 1; funext u
    have hT : opT a 1 F u = F u - (a 0 : ℂ)⁻¹ * deriv F u := by
      simp [opT, sc, coef, Finset.sum_range_succ, iteratedDeriv_one]; ring
    rw [hT]; rfl
  | succ n ih =>
    rw [ih, Finset.sum_range_succ _ (n + 1)]
    suffices hs : ∫ u, opT a (n + 1) F u * KC a r n u =
        (∫ u, opT a (n + 1 + 1) F u * KC a r (n + 1) u) + ∫ u, F u * ρ a r (n + 1) u by
      rw [hs]; ring
    set G := opT a (n + 1) F with hG
    set G2 := opT a (n + 2) F with hG2
    have hGc : Continuous G := continuous_opT a _ hF
    have hG2c : Continuous G2 := continuous_opT a _ hF

    have hpt : ∀ s, G s = (∫ t, G2 (s + t) * kC a r (n + 1) t) +
        ∫ t, G (s + t) * ηC a r (n + 1) t := by
      intro s
      have hd : ∀ t, HasDerivAt (fun t => G (s + t))
          (∑ p ∈ Finset.range (n + 2), sc a (n + 1) p * iteratedDeriv (p + 1) F (s + t)) t :=
        fun t => (hasDerivAt_opT a (n + 1) hF (s + t)).comp_const_add s t
      have hdc : Continuous fun t =>
          ∑ p ∈ Finset.range (n + 2), sc a (n + 1) p * iteratedDeriv (p + 1) F (s + t) :=
        continuous_finsetSum _ fun p _ => continuous_const.mul
          ((hF.continuous_iteratedDeriv (p + 1) (by exact_mod_cast le_top)).comp
            (continuous_const.add continuous_id))
      have h := step_identity (ha (n + 1)) (hr (n + 1)) hd hdc
      simp only [add_zero] at h
      rw [h]
      congr 1
      congr 1; funext t
      congr 1
      exact (opT_succ a (n + 1) F (s + t)).symm
    have hpk := pairing_convolution (k := kC a r (n + 1)) hG2c (integrable_KC ha hr n)
      (integrable_kern (ha (n + 1)).le (hr (n + 1))).ofReal (hasCompactSupport_KC ha hr n)
      ((HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        (support_kern_subset (hr (n + 1)))).comp_left Complex.ofReal_zero)
    have hpη := pairing_convolution (k := ηC a r (n + 1)) hGc (integrable_KC ha hr n)
      (integrable_rem (hr (n + 1))).ofReal (hasCompactSupport_KC ha hr n)
      (hasCompactSupport_ηC ha hr (n + 1))
    calc ∫ u, G u * KC a r n u
        = ∫ s, KC a r n s * ((∫ t, G2 (s + t) * kC a r (n + 1) t) +
            ∫ t, G (s + t) * ηC a r (n + 1) t) := by
          congr 1; funext s; rw [hpt s, mul_comm]
      _ = (∫ s, KC a r n s * ∫ t, G2 (s + t) * kC a r (n + 1) t) +
            ∫ s, KC a r n s * ∫ t, G (s + t) * ηC a r (n + 1) t := by
          simp only [mul_add]; exact integral_add hpk.1 hpη.1
      _ = (∫ u, G2 u * KC a r (n + 1) u) + ∫ u, F u * ρ a r (n + 1) u := by
          rw [← hpk.2, ← hpη.2, KC_succ ha hr n]
          congr 1
          rw [integral_opT_mul a (n + 1) hF (contDiff_conv_ηC ha hr n)
            (hasCompactSupport_conv_ηC ha hr n)]
          rfl
end GroundTheory.Automorphic.LineKernel
