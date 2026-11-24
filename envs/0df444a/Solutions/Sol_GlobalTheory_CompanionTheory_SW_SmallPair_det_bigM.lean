-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SmallPair.det_bigM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:53:25.137074+00:00
-- url     : https://prove2.me/submissions/0ad8c35d-5fc6-4aa6-ae22-32f981982a34

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBound
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SmallPair_det_block

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → ℂ)
    (h : ∀ w, 0 < (τ w).im) : (bigM τ).det = 1 := by
  simp [bigM, det_blockDiagonal, det_block _ (h _)]
end GlobalTheory.CompanionTheory.SW.SmallPair
