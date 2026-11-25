-- Prove2me | solution 1 for GlobalTheory.FrobRoot.mm_of_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:53.786945+00:00
-- url     : https://prove2.me/submissions/28e5a368-4adf-4823-97c3-4fdc51499b11

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodOfMemSlots
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowAdditiveAndRoots

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
theorem _root_.solution {a : C} (ha : V.Ge 1 a) : V.MM a := by
  refine lt_of_lt_of_le ?_ ha
  exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
end GlobalTheory.FrobRoot
