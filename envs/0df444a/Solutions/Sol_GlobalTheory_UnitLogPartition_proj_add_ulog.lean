-- Prove2me | solution 1 for GlobalTheory.UnitLogPartition.proj_add_ulog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:36:06.466238+00:00
-- url     : https://prove2.me/submissions/dea5ed64-540f-4937-8bd0-b538cabd4342

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslate
import Theorems.Thm_GlobalTheory_UnitLogPartition_ulog_idx
import Theorems.Thm_GlobalTheory_UnitLogPartition_sum_ulog_idx
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
open scoped ContDiff
noncomputable section
open GlobalTheory
open GlobalTheory.UnitLogPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I] {φ : I → K →+* ℂ}
namespace GlobalTheory.UnitLogPartition
theorem _root_.solution [IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) (u : (𝓞 K)ˣ) :
    proj hφ (y + GlobalTheory.HeckeTheta.ulog φ u) = proj hφ y + logEmbedding K (Additive.ofMul u) := by
  funext w
  have hm : mean hφ (y + GlobalTheory.HeckeTheta.ulog φ u) = mean hφ y := by
    unfold mean
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_ulog_idx hφ, add_zero]
  simp only [proj, hm, Pi.add_apply, logEmbedding_component, ← ulog_idx hφ]
  ring
end GlobalTheory.UnitLogPartition
