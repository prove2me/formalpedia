-- Prove2me | solution 1 for GlobalTheory.LastStep.mm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:41:01.936805+00:00
-- url     : https://prove2.me/submissions/32a27e71-9e15-4cbf-b6f6-cdd861571623

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowAdditiveAndRoots
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IndependentModFirstCoeffChainLastStep
import Theorems.Thm_GlobalTheory_FrobRoot_mm_add
import Theorems.Thm_GlobalTheory_FrobRoot_mm_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical GlobalTheory.FrobRoot
open GlobalTheory GlobalTheory.LastStep
namespace GlobalTheory.LastStep
theorem _root_.solution {C : Type} [Field C] {V : VF C} {ι : Type} (s : Finset ι) (f : ι → C)
    (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (mm_zero (V := V))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end GlobalTheory.LastStep
