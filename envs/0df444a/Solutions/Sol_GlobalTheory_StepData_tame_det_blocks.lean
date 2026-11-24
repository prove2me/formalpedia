-- Prove2me | solution 1 for GlobalTheory.StepData.tame_det_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:43.223798+00:00
-- url     : https://prove2.me/submissions/4d18e502-6cfe-4674-9637-2e22b8080a0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_StepData_maxM_zero
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_tame_det_of_mem_KOne
import Theorems.Thm_GlobalTheory_StepData_inv_mul_mem_KOne
import Theorems.Thm_GlobalTheory_StepData_maxM_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_blockGL_mem_KO
import Theorems.Thm_GlobalTheory_StepData_det_blockGL
import Theorems.Thm_GlobalTheory_StepData_exists_diag_blocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData
theorem _root_.solution {μ : kˣ →* ℂˣ} (hμ : IsTame μ) {h : GL (a ⊕ t) k} (hh : h ∈ KO k (a ⊕ t))
    (hC : MaxM h.val.toBlocks₂₁) {g : GL a k} (hg : g.val = h.val.toBlocks₁₁) {D : GL t k}
    (hD : D.val = h.val.toBlocks₂₂) :
    μ (Matrix.GeneralLinearGroup.det h) =
      μ (Matrix.GeneralLinearGroup.det g) * μ (Matrix.GeneralLinearGroup.det D) := by
  obtain ⟨⟨g', hg1, hg2⟩, D', hD1, hD2⟩ := exists_diag_blocks hh hC
  obtain rfl : g' = g := Units.ext (hg2.trans hg.symm)
  obtain rfl : D' = D := Units.ext (hD2.trans hD.symm)
  have hb := blockGL_mem_KO hg1 (B := h.val.toBlocks₁₂) (fun i j => intM_of_mem_KO hh _ _) hD1
  have hu := inv_mul_mem_KOne (g' := h) hb (by
    rw [← fromBlocks_toBlocks h.val]
    change MaxM (_ - fromBlocks g'.val h.val.toBlocks₁₂ 0 D'.val)
    rw [hg, hD, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    simp only [add_neg_cancel, neg_zero, add_zero]
    exact maxM_fromBlocks.2 ⟨maxM_zero, maxM_zero, hC, maxM_zero⟩)
  have := tame_det_of_mem_KOne hμ hu
  rw [map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one, det_blockGL, map_mul] at this
  exact this.symm
end GlobalTheory.StepData
