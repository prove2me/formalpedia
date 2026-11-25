-- Prove2me | solution 1 for GlobalTheory.RowValueCheck.agree_hOf_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:29.351412+00:00
-- url     : https://prove2.me/submissions/f9c74ab1-e673-4d5d-ae43-57f5c71ed02d

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
theorem _root_.solution [NeZero d] (X : RowData C V d I J) (T : Set (WV I)) (g0 : Fin 2)
    (hT : ∀ w ∈ T, w.1 = g0) (k : Option (Fin 2 × ZMod d × ZMod d)) : Agree T (hOf X.hL k) 0 := by
  intro μ hμ
  rcases k with _ | ⟨g, a, a'⟩
  · rfl
  · rw [map_zero]
    refine X.hL_axes g a a' μ ?_
    have : g0 = g ∨ g0 = 1 - g := (by decide : ∀ x y : Fin 2, x = y ∨ x = 1 - y) g0 g
    rcases this with e | e
    · exact Or.inl fun w hw => (hT w (hμ w (Finsupp.mem_support_iff.1 hw))).trans e
    · exact Or.inr fun w hw => (hT w (hμ w (Finsupp.mem_support_iff.1 hw))).trans e
end GlobalTheory.RowValueCheck
