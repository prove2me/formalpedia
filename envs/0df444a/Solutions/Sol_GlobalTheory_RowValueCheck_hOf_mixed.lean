-- Prove2me | solution 1 for GlobalTheory.RowValueCheck.hOf_mixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:17:26.345392+00:00
-- url     : https://prove2.me/submissions/744f7180-9b71-41e8-9c09-2a0d411d6586

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep

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
open GlobalTheory GlobalTheory.RowValueCheck
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
namespace GlobalTheory.RowValueCheck
theorem _root_.solution [NeZero d] (X : RowData C V d I J) (w0 w1 : WV I) (h0 : w0.1 = 0) (h1 : w1.1 = 1)
    (g : Fin 2) (a a' : ZMod d) (l0 : OnLeafV X.G g a a' w0) (l1 : OnLeafV X.G g a a' w1) :
    X.hL g a a' = X.hL 0 (tyW X.G w0) (tyW X.G w1) := by
  have hg : g = 0 ∨ g = 1 := (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) g
  unfold OnLeafV at l0 l1
  rw [h0] at l0
  rw [h1] at l1
  rcases hg with rfl | rfl
  · have e0 : tyW X.G w0 = a := by simpa using l0
    have e1 : tyW X.G w1 = a' := by simpa using l1
    rw [e0, e1]
  · have e0 : tyW X.G w0 = a' := by simpa using l0
    have e1 : tyW X.G w1 = a := by simpa using l1
    rw [e0, e1, X.hL_swap]
end GlobalTheory.RowValueCheck
