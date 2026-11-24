-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.PoiLat.quad_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:31.789336+00:00
-- url     : https://prove2.me/submissions/eada5a86-0a95-4e78-830f-1678bf887ead

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PoissonSummationGaussian
import Theorems.Thm_GlobalTheory_ofReal_mulVec_eq


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
theorem _root_.solution (P : Matrix κ κ ℝ) (W : Matrix κ κ ℂ) (v : κ → ℝ) :
    (fun i => (((P *ᵥ v) i : ℝ) : ℂ)) ⬝ᵥ (W *ᵥ fun i => (((P *ᵥ v) i : ℝ) : ℂ)) =
      (fun i => (v i : ℂ)) ⬝ᵥ
        (((P.map Complex.ofReal)ᵀ * W * P.map Complex.ofReal) *ᵥ fun i => (v i : ℂ)) := by
  rw [GlobalTheory.ofReal_mulVec_eq, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (fun i => (v i : ℂ)) ((P.map Complex.ofReal)ᵀ), Matrix.vecMul_transpose]
end GlobalTheory.CompanionTheory.SW.Core.PoiLat
