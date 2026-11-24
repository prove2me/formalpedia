-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.PoiLat.siegelGaussIntegral_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:15:13.986309+00:00
-- url     : https://prove2.me/submissions/2de3fcc3-8cc6-4529-8349-e7a3d01f4bf1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PoissonSummationGaussian
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_PoiLat_quad_mulVec
import Theorems.Thm_GlobalTheory_integral_comp_mulVec_of_det_ne_zero


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.PoiLat
variable {κ : Type} [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.CompanionTheory.SW.Core.PoiLat
theorem _root_.solution (Z : Matrix κ κ ℂ) {g : Matrix κ κ ℝ} (hg : g.det ≠ 0) :
    GlobalTheory.siegelGaussIntegral ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) =
      ((|g.det|⁻¹ : ℝ) : ℂ) * GlobalTheory.siegelGaussIntegral Z := by
  have hv : Continuous fun y : κ → ℝ => fun i => (y i : ℂ) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hf : Continuous fun y : κ → ℝ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (y i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (y i : ℂ)))) :=
    Complex.continuous_exp.comp (continuous_const.mul (hv.dotProduct (continuous_const.matrix_mulVec hv)))
  have key := GlobalTheory.integral_comp_mulVec_of_det_ne_zero hg hf
  simp only [quad_mulVec] at key
  simp only [GlobalTheory.siegelGaussIntegral]
  rw [← abs_inv]
  exact key
end GlobalTheory.CompanionTheory.SW.Core.PoiLat
