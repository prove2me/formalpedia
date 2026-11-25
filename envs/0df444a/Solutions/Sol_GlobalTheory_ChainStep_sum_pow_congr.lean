-- Prove2me | solution 1 for GlobalTheory.ChainStep.sum_pow_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:54:19.044419+00:00
-- url     : https://prove2.me/submissions/6a894ac3-9859-4956-99fa-4e616ddc18d2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainStepKernelRankLeModMaxIdeal
import Theorems.Thm_GlobalTheory_ChainStep_mm_zero
import Theorems.Thm_GlobalTheory_ChainStep_mm_add
import Theorems.Thm_GlobalTheory_ChainStep_add_pow_congr
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.ChainStep
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.ChainStep
theorem _root_.solution {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.Ge 0 (f i)) (n : ℕ) :
    V.MM ((∑ i ∈ s, f i) ^ (V.l ^ n) - ∑ i ∈ s, f i ^ (V.l ^ n)) := by
  induction s using Finset.induction_on with
  | empty => simpa [V.l_prime.ne_zero] using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h' := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h1 := add_pow_congr (h a (Finset.mem_insert_self a s)) (VF.Ge.sum h') n
    have h2 := mm_add h1 (ih h')
    convert h2 using 1
    ring
end GlobalTheory.ChainStep
