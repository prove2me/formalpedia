-- Prove2me | solution 1 for GlobalTheory.FrobRoot.mm_add_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:23.886751+00:00
-- url     : https://prove2.me/submissions/e0d86331-f8f9-4e32-8656-54f0fe89d657

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodOfMemSlots
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowAdditiveAndRoots
import Theorems.Thm_GlobalTheory_FrobRoot_mm_of_ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_l_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int


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
theorem _root_.solution (e : ℕ) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.MM ((a + b) ^ (V.l ^ e) - (a ^ (V.l ^ e) + b ^ (V.l ^ e))) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime
    (⟨a, ha⟩ : intRing V) (⟨b, hb⟩ : intRing V) e
  have h := congrArg (Subtype.val) hr
  push_cast at h
  rw [h, add_sub_cancel_left]
  apply mm_of_ge_one
  have hr0 : V.Ge 0 (r : C) := r.2
  first
    | simpa using hr0.l_mul
    | simpa [mul_assoc] using (ha.mul_int (hb.mul_int hr0)).l_mul
end GlobalTheory.FrobRoot
