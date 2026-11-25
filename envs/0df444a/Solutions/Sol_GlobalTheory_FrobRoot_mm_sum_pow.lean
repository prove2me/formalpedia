-- Prove2me | solution 1 for GlobalTheory.FrobRoot.mm_sum_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:54:21.494603+00:00
-- url     : https://prove2.me/submissions/d4607bfe-bb6c-4bc5-b015-2c0dcda8e689

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodOfMemSlots
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowAdditiveAndRoots
import Theorems.Thm_GlobalTheory_FrobRoot_mm_add
import Theorems.Thm_GlobalTheory_FrobRoot_mm_zero
import Theorems.Thm_GlobalTheory_FrobRoot_mm_add_pow
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
open Formalism.L2.FormalSeriesBounds GlobalTheory.LeafTerm
open GlobalTheory GlobalTheory.FrobRoot
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.FrobRoot
theorem _root_.solution (e : ℕ) {ι : Type} (s : Finset ι) (x : ι → C) (hx : ∀ i ∈ s, V.Ge 0 (x i)) :
    V.MM ((∑ i ∈ s, x i) ^ (V.l ^ e) - ∑ i ∈ s, x i ^ (V.l ^ e)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero e V.l_prime.ne_zero), sub_zero]
    exact mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : ∀ i ∈ s, V.Ge 0 (x i) := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have h := mm_add (mm_add_pow e (hx a (Finset.mem_insert_self a s)) (VF.Ge.sum hs)) (ih hs)
    convert h using 1
    ring
end GlobalTheory.FrobRoot
