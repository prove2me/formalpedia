-- Prove2me | solution 1 for GlobalTheory.FrobRoot.ge_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:03.342572+00:00
-- url     : https://prove2.me/submissions/10a543c3-ce6a-467b-8266-3c6dba3afbdf

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
theorem _root_.solution {a : C} {n : ℕ} (hn : n ≠ 0) (ha : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  unfold VF.Ge at *
  rw [V.v.map_pow] at ha
  rw [WithTop.coe_zero] at ha ⊢
  by_contra h
  exact absurd ha (not_le.mpr (nsmul_neg (not_le.mp h) hn))
end GlobalTheory.FrobRoot
