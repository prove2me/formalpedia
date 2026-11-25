-- Prove2me | solution 1 for GlobalTheory.LeafTerm.al_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:34:13.348061+00:00
-- url     : https://prove2.me/submissions/faff71a3-d5e1-4948-a477-5a0f42fe0578

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodOfMemSlots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.LeafTerm
variable {C : Type} [Field C]
variable {Z I J : Type} [Fintype I]
variable [Fintype J] {V : VF C} {d : ℕ} {X : Cart V d I J}
namespace GlobalTheory.LeafTerm
theorem _root_.solution (S : Sys X) (c x : I) : S.al c 0 x = S.tan c x := by
  simp [Sys.al, (S.curve c).2.1]
end GlobalTheory.LeafTerm
