-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GaussOne.half_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:18:57.004827+00:00
-- url     : https://prove2.me/submissions/d9dbac76-52fb-4351-badd-b9609355f780

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SimultaneousNormalFormMajorant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransform

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GaussOne
namespace GlobalTheory.CompanionTheory.SW.GaussOne
theorem _root_.solution {b : ℂ} (hb : 0 < b.re) :
    (b⁻¹) ^ (1 / 2 : ℂ) * ((b⁻¹)⁻¹) ^ (1 / 2 : ℂ) = 1 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have harg : b.arg ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff, not_and_or, not_lt]
    exact Or.inl hb.le
  rw [inv_inv, Complex.inv_cpow _ _ harg, inv_mul_cancel₀]
  simp [Complex.cpow_eq_zero_iff, hb0]
end GlobalTheory.CompanionTheory.SW.GaussOne
