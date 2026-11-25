-- Prove2me | solution 1 for GlobalTheory.FlatFamily.flatZetaHolomorphic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:43:49.107222+00:00
-- url     : https://prove2.me/submissions/284a1968-5920-4f4f-b617-3cbd6d6e0d2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_FlatZetaIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFamilyZetaConvergenceHolomorphy
import Theorems.Thm_GlobalTheory_FlatFamily_flatIntegrand_rebase
import Theorems.Thm_GlobalTheory_FlatFamily_norm_flatIntegrand_le
import Theorems.Thm_GlobalTheory_FlatFamily_aestronglyMeasurable_flatIntegrand
import Theorems.Thm_GlobalTheory_FlatFamily_hasDerivAt_flatIntegrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open GlobalTheory GlobalTheory.FlatFamily
open GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
variable {X : Type} [MeasurableSpace X]
namespace GlobalTheory.FlatFamily
theorem _root_.solution : FlatZetaHolomorphic := by
  intro X _ μ f a s₀ s₁ hm ha ha1 hint
  have hmeas := aestronglyMeasurable_flatIntegrand hm ha hint.aestronglyMeasurable
  have hI : ∀ s : ℂ, s₁.re ≤ s.re → Integrable (flatIntegrand f a s₀ s) μ := fun s hs =>
    hint.norm.mono' (hmeas s) (Filter.Eventually.of_forall (norm_flatIntegrand_le f ha ha1 s₀ hs))
  refine ⟨⟨hI, fun s _ => ⟨_, self_mem_nhdsWithin, _, hint.norm,
    fun s' hs' x => norm_flatIntegrand_le f ha ha1 s₀ hs' x⟩⟩, ?_, ?_⟩
  · intro s hs
    have hs' : s₁.re < s.re := hs
    set ε : ℝ := (s.re - s₁.re) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have hU : {z : ℂ | s₁.re + ε < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        change s₁.re + ε < s.re
        rw [hε]; linarith)
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun z x => flatIntegrand f a s₀ z x)
      (F' := fun z x => flatIntegrand f a s₀ z x * ((Real.log (a x) : ℝ) : ℂ))
      (x₀ := s) (bound := fun x => ‖flatIntegrand f a s₀ s₁ x‖ * (1 / ε)) hU
      (Filter.Eventually.of_forall hmeas) (hI s hs'.le)
      ((hmeas s).mul
        (Complex.measurable_ofReal.comp (Real.measurable_log.comp hm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x z hz => by
        have hz' : s₁.re + ε < z.re := hz
        rw [flatIntegrand_rebase f ha s₀ s₁ z x, mul_assoc, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha x), Complex.norm_real,
          Real.norm_eq_abs, Complex.sub_re]
        have h1 : a x ^ (z.re - s₁.re) ≤ a x ^ ε :=
          Real.rpow_le_rpow_of_exponent_ge (ha x) (ha1 x) (by linarith)
        have h2 := Real.abs_log_mul_self_rpow_lt (a x) ε (ha x) (ha1 x) hεpos
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (ha x) ε), mul_comm] at h2
        exact (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)).trans h2.le)
      (hint.norm.mul_const _)
      (Filter.Eventually.of_forall fun x z _ => hasDerivAt_flatIntegrand f ha s₀ z x)
    exact key.2.differentiableAt.differentiableWithinAt
  · exact continuousOn_of_dominated (bound := fun x => ‖flatIntegrand f a s₀ s₁ x‖)
      (fun s _ => hmeas s)
      (fun s hs => Filter.Eventually.of_forall (norm_flatIntegrand_le f ha ha1 s₀ hs))
      hint.norm
      (Filter.Eventually.of_forall fun x z _ =>
        (hasDerivAt_flatIntegrand f ha s₀ z x).continuousAt.continuousWithinAt)
end GlobalTheory.FlatFamily
