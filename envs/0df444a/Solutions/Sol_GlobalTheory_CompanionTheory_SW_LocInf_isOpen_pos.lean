-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocInf.isOpen_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:44.001317+00:00
-- url     : https://prove2.me/submissions/5c5a7725-491c-41de-88bc-81c5aaa527a7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInf
namespace GlobalTheory.CompanionTheory.SW.LocInf
theorem _root_.solution (ι : Type) [Finite ι] : IsOpen {x : ι → ℝ | ∀ i, 0 < x i} := by
  have h1 : {x : ι → ℝ | ∀ i, 0 < x i} = ⋂ i, {x : ι → ℝ | 0 < x i} := by
    ext x
    simp
  rw [h1]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
end GlobalTheory.CompanionTheory.SW.LocInf
