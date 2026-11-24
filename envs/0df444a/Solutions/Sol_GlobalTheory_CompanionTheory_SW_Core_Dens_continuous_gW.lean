-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Dens.continuous_gW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:13:52.465176+00:00
-- url     : https://prove2.me/submissions/18bc155c-8de7-4080-bac3-02584dfba519

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
theorem _root_.solution (P : InfinitePlace F → Matrix ι ι ℝ) : Continuous (gW P) := by
  refine Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun w _ => ?_))
  exact Continuous.dotProduct (continuous_apply w)
    (Continuous.matrix_mulVec continuous_const (continuous_apply w))
end GlobalTheory.CompanionTheory.SW.Core.Dens
