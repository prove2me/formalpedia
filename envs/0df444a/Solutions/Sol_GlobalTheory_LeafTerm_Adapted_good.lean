-- Prove2me | solution 1 for GlobalTheory.LeafTerm.Adapted.good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:27:37.848589+00:00
-- url     : https://prove2.me/submissions/4ea0b5c8-483e-4d79-a1ce-4861f705608e

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
variable {S : Sys X} {D : Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d} {i : ℕ}
namespace GlobalTheory.LeafTerm
namespace Adapted
theorem _root_.solution (h : Adapted S D a i) {c : I} (hc : D.good c) :
    X.Good (X.ty (Sum.inl c)) (S.tan c) (S.cur c) := by
  refine ⟨S.curve c, fun x => ?_⟩
  have := h.2.2.2.1 c 1 x le_rfl
  simpa [D.al_one c hc, Sys.al] using this
end Adapted
end GlobalTheory.LeafTerm
