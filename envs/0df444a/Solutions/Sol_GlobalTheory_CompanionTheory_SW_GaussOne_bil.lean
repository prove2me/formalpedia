-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GaussOne.bil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:56.499212+00:00
-- url     : https://prove2.me/submissions/2bcaea5b-92e5-485b-8882-6718f0b79233

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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.GaussOne
theorem _root_.solution (g A : Matrix ι ι ℝ) (u w : ι → ℝ) :
    (g *ᵥ u) ⬝ᵥ (A *ᵥ (g *ᵥ w)) = u ⬝ᵥ ((gᵀ * A * g) *ᵥ w) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u gᵀ,
    Matrix.vecMul_transpose]
end GlobalTheory.CompanionTheory.SW.GaussOne
