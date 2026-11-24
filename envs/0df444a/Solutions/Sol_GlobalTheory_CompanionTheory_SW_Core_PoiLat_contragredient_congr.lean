-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.PoiLat.contragredient_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:15:11.064255+00:00
-- url     : https://prove2.me/submissions/cf55a52a-0f81-433b-b341-26ad573cb8e6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PoissonSummationGaussian
import Theorems.Thm_GlobalTheory_inv_map_ofReal


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
theorem _root_.solution {g : Matrix κ κ ℝ} (hg : g.det ≠ 0) (Z : Matrix κ κ ℂ) :
    (((g⁻¹)ᵀ).map Complex.ofReal)ᵀ * Z⁻¹ * ((g⁻¹)ᵀ).map Complex.ofReal =
      ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹ := by
  have hC : (g⁻¹).map Complex.ofReal = (g.map Complex.ofReal)⁻¹ := (GlobalTheory.inv_map_ofReal hg).symm
  have hC' : ((g⁻¹)ᵀ).map Complex.ofReal = ((g.map Complex.ofReal)⁻¹)ᵀ := by
    rw [Matrix.transpose_map, hC]
  rw [hC', Matrix.transpose_transpose, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.transpose_nonsing_inv, Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.SW.Core.PoiLat
