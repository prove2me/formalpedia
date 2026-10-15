-- Prove2me | solution 1 for OAI.ParityWL.liftEquations_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:07:35.325324+00:00
-- url     : https://prove2.me/submissions/f4784f3a-bbec-4bd1-9924-ae9f64877e3d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/LiftCounts.lean:L204-L223
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.liftEquations_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts

-- ---- from OAI.Combinatorics.ParityLifts.LiftCounts ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section Lifts

variable {A V : Type} [Fintype A] (T : SimpleGraph A) (G : SimpleGraph V)

end Lifts

section LiftCounts

open scoped Classical

variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

omit [Fintype V] [Fintype W] in
lemma liftEquations_iff (b : A → Bit) (z : Variables T G F τ φ) :
    LiftEquations T G F τ φ b z ↔
      constraintMap T G F τ φ z = constraintRHS T G F τ φ b := by
  constructor
  · rintro ⟨hvertex, hedge⟩
    funext row
    cases row with
    | inl x => exact hvertex x
    | inr d =>
      change z d.fst _ + z d.snd _ = 0
      rw [hedge d.fst d.snd d.adj, CharTwo.add_self_eq_zero]
  · intro h
    constructor
    · intro x
      exact congrFun h (.inl x)
    · intro x y hxy
      have he := congrFun h (.inr ⟨(x, y), hxy⟩)
      change z x _ + z y _ = 0 at he
      rwa [← CharTwo.sub_eq_add, sub_eq_zero] at he

end LiftCounts

section BinaryDuality

variable {E H : Type} [AddCommGroup E] [Module Bit E] [AddCommGroup H] [Module Bit H]

end BinaryDuality

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.liftEquations_iff := @_root_.OAI.ParityWL.liftEquations_iff
