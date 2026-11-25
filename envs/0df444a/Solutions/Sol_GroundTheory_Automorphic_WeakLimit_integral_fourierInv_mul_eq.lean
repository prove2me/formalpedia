-- Prove2me | solution 1 for GroundTheory.Automorphic.WeakLimit.integral_fourierInv_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:24.311912+00:00
-- url     : https://prove2.me/submissions/0bf85609-39ba-4abf-aeec-9865fa7a1fcc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Theorems.Thm_GroundTheory_Automorphic_WeakLimit_integral_fourier_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Set
open scoped FourierTransform ContDiff
open GroundTheory.Automorphic.WeakLimit
namespace GroundTheory.Automorphic.WeakLimit
theorem _root_.solution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x := by
  rw [Real.fourierInv_eq_fourier_comp_neg, integral_fourier_mul_eq hf.comp_neg hg,
    ← integral_neg_eq_self (fun x => f x * 𝓕⁻ g x)]
  congr 1; funext x
  simp [Real.fourierInv_eq_fourier_neg]
end GroundTheory.Automorphic.WeakLimit
