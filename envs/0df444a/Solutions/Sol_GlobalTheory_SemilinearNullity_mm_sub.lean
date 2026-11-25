-- Prove2me | solution 1 for GlobalTheory.SemilinearNullity.mm_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:15.631988+00:00
-- url     : https://prove2.me/submissions/19a25a5d-7a53-4905-8942-74fdece4bec6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSemilinearRankNullityModMaxIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.SemilinearNullity
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.SemilinearNullity
theorem _root_.solution {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]
  refine V.v.map_lt_add ha ?_
  rw [V.v.map_neg]; exact hb
end GlobalTheory.SemilinearNullity
