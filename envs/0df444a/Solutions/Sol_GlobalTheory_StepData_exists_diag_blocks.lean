-- Prove2me | solution 1 for GlobalTheory.StepData.exists_diag_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:13:34.783691+00:00
-- url     : https://prove2.me/submissions/fe2885d1-9c3e-4d60-b973-f28e6901d04f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_blocks_inv
import Theorems.Thm_GlobalTheory_StepData_exists_mem_KO_of_mul

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
theorem _root_.solution {h : GL (a ⊕ t) k} (hh : h ∈ KO k (a ⊕ t)) (hC : MaxM h.val.toBlocks₂₁) :
    (∃ g ∈ KO k a, g.val = h.val.toBlocks₁₁) ∧ ∃ D ∈ KO k t, D.val = h.val.toBlocks₂₂ := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hh
  obtain ⟨m1, m2, -⟩ := blocks_inv hh hC
  exact ⟨exists_mem_KO_of_mul (fun i j => h1 _ _) (fun i j => h2 _ _) m1,
    exists_mem_KO_of_mul (fun i j => h1 _ _) (fun i j => h2 _ _) m2⟩
end GlobalTheory.StepData
