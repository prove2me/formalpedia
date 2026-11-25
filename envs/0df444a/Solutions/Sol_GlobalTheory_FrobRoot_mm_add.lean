-- Prove2me | solution 1 for GlobalTheory.FrobRoot.mm_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:35.781672+00:00
-- url     : https://prove2.me/submissions/5b1d7636-570a-4691-a86a-1cf4b821be71

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
theorem _root_.solution {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb
end GlobalTheory.FrobRoot
