-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Mobius.comp_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:17:29.12488+00:00
-- url     : https://prove2.me/submissions/8f518496-eb7e-44c2-a920-39ebdc3bfa4a

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MobiusActionUpperHalfPlane
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Mobius_den_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Mobius_im_frac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Mobius
namespace GlobalTheory.CompanionTheory.SW.Core.Mobius
theorem _root_.solution (a b c d a' b' c' d' : ℝ) (hdet : a * d - b * c = 1)
    (hdet' : a' * d' - b' * c' = 1) (τ : ℂ) (h : 0 < τ.im) :
    (((a * a' + b * c' : ℝ) : ℂ) * τ + ((a * b' + b * d' : ℝ) : ℂ)) /
        (((c * a' + d * c' : ℝ) : ℂ) * τ + ((c * b' + d * d' : ℝ) : ℂ)) =
      ((a : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + b) /
        ((c : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + d) := by
  have h' := den_ne a' b' c' d' hdet' τ h
  have hX : 0 < (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')).im := by
    rw [im_frac a' b' c' d' hdet' τ h]
    have : 0 < ‖(c' : ℂ) * τ + d'‖ := norm_pos_iff.mpr h'
    positivity
  have h2 := den_ne a b c d hdet _ hX
  have e1 : (c : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + d =
      (((c * a' + d * c' : ℝ) : ℂ) * τ + ((c * b' + d * d' : ℝ) : ℂ)) / ((c' : ℂ) * τ + d') := by
    rw [eq_div_iff h', add_mul, mul_assoc, div_mul_cancel₀ _ h']
    push_cast
    ring
  have e2 : (a : ℂ) * (((a' : ℂ) * τ + b') / ((c' : ℂ) * τ + d')) + b =
      (((a * a' + b * c' : ℝ) : ℂ) * τ + ((a * b' + b * d' : ℝ) : ℂ)) / ((c' : ℂ) * τ + d') := by
    rw [eq_div_iff h', add_mul, mul_assoc, div_mul_cancel₀ _ h']
    push_cast
    ring
  rw [e1, e2, div_div_div_cancel_right₀ h']
end GlobalTheory.CompanionTheory.SW.Core.Mobius
