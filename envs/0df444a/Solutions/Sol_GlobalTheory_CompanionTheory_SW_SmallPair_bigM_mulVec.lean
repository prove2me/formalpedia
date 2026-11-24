-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SmallPair.bigM_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:47.074405+00:00
-- url     : https://prove2.me/submissions/464721e5-bdc8-49e3-a64a-884dcc8d8fea

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → ℂ)
    (v : Fin 2 × ι → ℝ) (k : Fin 2) (w : ι) :
    (bigM τ *ᵥ v) (k, w) = ∑ j, block (τ w) k j * v (j, w) := by
  simp only [bigM, mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply]
  rw [Finset.sum_comm]
  simp
end GlobalTheory.CompanionTheory.SW.SmallPair
