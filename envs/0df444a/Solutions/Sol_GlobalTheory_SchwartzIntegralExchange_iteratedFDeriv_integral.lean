-- Prove2me | solution 1 for GlobalTheory.SchwartzIntegralExchange.iteratedFDeriv_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:04:16.938799+00:00
-- url     : https://prove2.me/submissions/dbe2af3a-4e4e-4c4e-b319-cab6ae1f0651

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition
import Theorems.Thm_GlobalTheory_SchwartzIntegralExchange_integrable_iteratedFDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open GlobalTheory.SchwartzIntegralExchange
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type} [TopologicalSpace P] [SecondCountableTopology P] [MeasurableSpace P]
  [OpensMeasurableSpace P] {ν : Measure P} {Φ : P → SchwartzMap E ℂ} {c : P → ℂ}
namespace GlobalTheory.SchwartzIntegralExchange
theorem _root_.solution (hΦ : Continuous Φ) (hc : AEStronglyMeasurable c ν)
    (hi : ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) ν)
    (u : E → ℂ) (hu : ∀ x, u x = ∫ ξ, c ξ * Φ ξ x ∂ν) (n : ℕ) :
    ∀ x, iteratedFDeriv ℝ n u x = ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν := by
  induction n with
  | zero =>
    intro x
    ext m
    rw [ContinuousMultilinearMap.integral_apply (integrable_iteratedFDeriv hΦ hc hi 0 x)]
    simp [hu]
  | succ n ih =>
    intro x
    set L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ with hL
    have hfun : iteratedFDeriv ℝ n u = fun x => ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν :=
      funext ih
    have hd : HasFDerivAt (fun x => ∫ ξ, c ξ • iteratedFDeriv ℝ n (Φ ξ) x ∂ν)
        (∫ ξ, L (c ξ • iteratedFDeriv ℝ (n + 1) (Φ ξ) x) ∂ν) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
        (F := fun x ξ => c ξ • iteratedFDeriv ℝ n (Φ ξ) x)
        (F' := fun x ξ => L (c ξ • iteratedFDeriv ℝ (n + 1) (Φ ξ) x))
        (bound := fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ 0 (n + 1) (Φ ξ))
        Filter.univ_mem
        (Filter.Eventually.of_forall fun y =>
          (integrable_iteratedFDeriv hΦ hc hi n y).aestronglyMeasurable)
        (integrable_iteratedFDeriv hΦ hc hi n x)
        (L.continuous.comp_aestronglyMeasurable
          (integrable_iteratedFDeriv hΦ hc hi (n + 1) x).aestronglyMeasurable)
        (ae_of_all _ fun ξ y _ => ?_) (hi 0 (n + 1)) (ae_of_all _ fun ξ y _ => ?_)
      · rw [LinearIsometryEquiv.norm_map, norm_smul]
        exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ _ y)
          (norm_nonneg _)
      · have h1 : DifferentiableAt ℝ (iteratedFDeriv ℝ n (Φ ξ)) y :=
          ((Φ ξ).smooth ⊤).differentiable_iteratedFDeriv
            (by exact_mod_cast ENat.coe_lt_top n) y
        have h2 := h1.hasFDerivAt.const_smul (c ξ)
        rw [fderiv_iteratedFDeriv] at h2
        exact h2
    have h3 := hd.fderiv
    rw [← hfun, fderiv_iteratedFDeriv] at h3
    apply L.injective
    exact h3.trans (L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (integrable_iteratedFDeriv hΦ hc hi (n + 1) x))
end GlobalTheory.SchwartzIntegralExchange
