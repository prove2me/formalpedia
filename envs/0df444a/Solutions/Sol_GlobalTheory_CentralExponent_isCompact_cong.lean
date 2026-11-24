-- Prove2me | solution 1 for GlobalTheory.CentralExponent.isCompact_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:09:29.235679+00:00
-- url     : https://prove2.me/submissions/83ca012c-36ff-49a0-9122-c5f92416efcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IrreducibleTensorCharacter
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Theorems.Thm_GlobalTheory_CentralExponent_isOpen_cong
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_mem_KOne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.StepData ValuativeRel Matrix Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.CentralExponent
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CentralExponent
theorem _root_.solution (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) :
    IsCompact (cong n γ hγ : Set (GL n k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_cong γ hγ))
    fun _ hg => KOne_le_KO (mem_KOne.2 fun i j => (hg i j).trans_le hγ)
end GlobalTheory.CentralExponent
