-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.wt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:48.294994+00:00
-- url     : https://prove2.me/submissions/94dc7e34-977a-44df-9aaf-5e2ebd5bcae6

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianSumOfCounting

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
namespace GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
theorem _root_.solution (c : ℝ) (j : ℕ) : 0 ≤ wt c j := by
  unfold wt; split_ifs
  · exact zero_le_one
  · exact (Real.exp_pos _).le
end GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
