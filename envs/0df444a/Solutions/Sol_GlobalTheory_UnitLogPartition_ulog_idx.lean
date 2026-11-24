-- Prove2me | solution 1 for GlobalTheory.UnitLogPartition.ulog_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:39.466711+00:00
-- url     : https://prove2.me/submissions/d12ffd57-6fc8-4ee7-86a4-6867af5060bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslate
import Theorems.Thm_GlobalTheory_UnitLogPartition_apply_eq_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped ContDiff
noncomputable section
open GlobalTheory
open GlobalTheory.UnitLogPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I] {φ : I → K →+* ℂ}
namespace GlobalTheory.UnitLogPartition
theorem _root_.solution [IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    GlobalTheory.HeckeTheta.ulog φ u (idx hφ w) = w.mult * Real.log (w (u : K)) := by
  unfold GlobalTheory.HeckeTheta.ulog
  rw [(IsTotallyComplex.isComplex w).mult_eq_two, ← apply_eq_norm hφ, Real.log_pow]
end GlobalTheory.UnitLogPartition
