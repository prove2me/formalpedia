-- Prove2me | solution 1 for GlobalTheory.UnitLogPartition.sum_ulog_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:25:55.325536+00:00
-- url     : https://prove2.me/submissions/8b17a9da-f055-4cc6-b7ee-d58588f5dca9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslate
import Theorems.Thm_GlobalTheory_UnitLogPartition_ulog_idx
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
theorem _root_.solution [IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) :
    ∑ w : InfinitePlace K, GlobalTheory.HeckeTheta.ulog φ u (idx hφ w) = 0 := by
  simp only [ulog_idx hφ]
  exact sum_mult_mul_log u
end GlobalTheory.UnitLogPartition
