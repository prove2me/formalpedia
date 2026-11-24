-- Prove2me | solution 1 for GlobalTheory.StepData.blockGL_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:58:46.604597+00:00
-- url     : https://prove2.me/submissions/2df5073e-6983-4d72-a3da-eedad590ef5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_StepData_intM_zero
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_intM_fromBlocks

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
theorem _root_.solution {g : GL a k} {B : Matrix a t k} {D : GL t k} (hg : g ∈ KO k a) (hB : IntM B)
    (hD : D ∈ KO k t) : blockGL g B D ∈ KO k (a ⊕ t) := by
  obtain ⟨g1, g2⟩ := mem_KO.1 hg
  obtain ⟨d1, d2⟩ := mem_KO.1 hD
  exact mem_KO.2 ⟨intM_fromBlocks.2 ⟨g1, hB, intM_zero, d1⟩,
    intM_fromBlocks.2 ⟨g2, ((g2.mul hB).mul d2).neg, intM_zero, d2⟩⟩
end GlobalTheory.StepData
