-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.integral_cur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:54:21.062003+00:00
-- url     : https://prove2.me/submissions/7d1143e3-6cd3-4dc9-a99d-1600ae6c6c58

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianFourierTransformFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussFlat_swapCurry_measurePreserving

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
theorem _root_.solution (f : (InfinitePlace F → ι → ℝ) → ℂ) :
    ∫ x : ι × InfinitePlace F → ℝ, f (cur x) = ∫ z, f z :=
  (swapCurry_measurePreserving ι (InfinitePlace F)).integral_comp' f
end GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
