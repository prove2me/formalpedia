-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Dens.continuous_qMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:13:54.429071+00:00
-- url     : https://prove2.me/submissions/0640314c-50f9-4d01-9fbe-9b6f6e338c8b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourierStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotentStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuadraticLevelSetDensity

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Dens
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.Core.Dens
theorem _root_.solution (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) :
    Continuous (qMap B ρ) := by
  refine continuous_pi fun w => ?_
  exact continuous_const.mul (Continuous.dotProduct (continuous_apply w)
    (Continuous.matrix_mulVec continuous_const (continuous_apply w)))
end GlobalTheory.CompanionTheory.SW.Core.Dens
