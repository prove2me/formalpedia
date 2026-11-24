-- Prove2me | solution 1 for GlobalTheory.PosOneCell.app_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:00:12.438958+00:00
-- url     : https://prove2.me/submissions/79370dcd-7a4f-4f13-8adc-5ac72c722ab6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsQuotIntCellsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EntriesWellDefined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_QuotIntPosOne
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FourierJacobiAverage_app_coe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents app_coe)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale volR)
noncomputable section
open GlobalTheory GlobalTheory.PosOneCell
variable {X : Type} [TopologicalSpace X] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.PosOneCell
theorem _root_.solution (l : SB X →ₗ[ℂ] V) (z : ℂ) (f : X → ℂ) : app l (z • f) = z • app l f := by
  by_cases hz : z = 0
  · subst hz
    have : app l (0 : X → ℂ) = 0 := by
      rw [show (0 : X → ℂ) = ((0 : SB X) : X → ℂ) from rfl, app_coe, map_zero]
    rw [zero_smul, zero_smul, this]
  · by_cases hf : f ∈ SB X
    · have hzf : z • f ∈ SB X := (SB X).smul_mem z hf
      simp only [app, hf, hzf, dif_pos]
      rw [← map_smul]
      rfl
    · have hzf : z • f ∉ SB X := fun h => hf (((SB X).smul_mem_iff hz).1 h)
      simp [app, hf, hzf]
end GlobalTheory.PosOneCell
