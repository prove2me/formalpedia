-- Prove2me | solution 1 for GlobalTheory.LeafTerm.tan_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:01:04.712991+00:00
-- url     : https://prove2.me/submissions/70409fc6-e5e2-483d-992c-dba223e22620

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodOfMemSlots
import Theorems.Thm_GlobalTheory_LeafTerm_al_zero

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
theorem _root_.solution (S : Sys X) (c x : I) : V.Ge 0 (S.tan c x) := by
  rw [← al_zero]
  exact X.t2 _ (S.curve c).1 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) _
end GlobalTheory.LeafTerm
