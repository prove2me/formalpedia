-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SmallPair.det_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:33:20.029054+00:00
-- url     : https://prove2.me/submissions/e45a1720-6815-4a0d-b20a-5cc9b1486e8f

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBound

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SmallPair
namespace GlobalTheory.CompanionTheory.SW.SmallPair
theorem _root_.solution (τ : ℂ) (h : 0 < τ.im) : (block τ).det = 1 := by
  have : √τ.im ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  simp [block, det_fin_two]
  field_simp
end GlobalTheory.CompanionTheory.SW.SmallPair
