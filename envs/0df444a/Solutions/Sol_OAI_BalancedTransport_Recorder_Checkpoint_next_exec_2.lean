-- Prove2me | solution 2 for OAI.BalancedTransport.Recorder.Checkpoint.next_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:35:57.021337+00:00
-- url     : https://prove2.me/submissions/11105b13-b0ed-4fe9-86c8-b8b691c1b26a

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RecorderSimulation.lean:L184-L205
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Recorder.Checkpoint.next_exec. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RecorderRules ----
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Instruction
open Stream'
variable {Q Γ : Type*}

end BalancedTransport.Recorder.Instruction
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Row
open Stream'
variable {Q Γ : Type*}
open Control Letter

end BalancedTransport.Recorder.Row
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} [DecidableEq Q] [DecidableEq Γ]
open Letter Control

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} [DecidableEq Q] [DecidableEq Γ]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*} (M : Machine Q Γ)
open Letter Control

theorem row_step (r : Row Q Γ) (hr : r.valid M) (t : Tails Q Γ) :
    Step M ((r.instruction M).source t) ((r.instruction M).target t) :=
  ⟨r, hr, t, rfl, rfl⟩

theorem outward_scan (q : Q) (hq : q ≠ M.halt) (w : List Γ)
    (L R J : Stream' (Letter Q Γ)) :
    Exec M w.length
      ⟨outward q, L, w.map work ++ₛ R, J⟩
      ⟨outward q, w.reverse.map work ++ₛ L, R, J⟩ := by
  induction w generalizing L with
  | nil => simpa using Exec.refl (M := M) (⟨outward q, L, R, J⟩ : Configuration Q Γ)
  | cons a as ih =>
      have h := row_step M (.outward q a) hq ⟨L, as.map work ++ₛ R, J⟩
      have hh := Exec.cons h (ih (work a :: L))
      simpa [Row.instruction, Instruction.source, Instruction.target,
        Stream'.appendStream', List.reverse_cons, List.map_append] using hh

theorem returning_scan (q : Q) (hq : q ≠ M.halt) (w : List Γ)
    (L R J : Stream' (Letter Q Γ)) :
    Exec M w.length
      ⟨returning q, w.map work ++ₛ L, R, J⟩
      ⟨returning q, L, w.reverse.map work ++ₛ R, J⟩ := by
  induction w generalizing R with
  | nil => simpa using Exec.refl (M := M) (⟨returning q, L, R, J⟩ : Configuration Q Γ)
  | cons a as ih =>
      have h := row_step M (.backward q a) hq ⟨as.map work ++ₛ L, R, J⟩
      have hh := Exec.cons h (ih (work a :: R))
      simpa [Row.instruction, Instruction.source, Instruction.target,
        Stream'.appendStream', List.reverse_cons, List.map_append] using hh

end BalancedTransport.Recorder
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.PrefixCoding ----
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*}

namespace Exec

variable {M : Machine Q Γ}

theorem single {source target : Configuration Q Γ} (step : Step M source target) :
    Exec M 1 source target :=
  .cons step (.refl target)

theorem trans {firstLength secondLength : ℕ} {source middle target : Configuration Q Γ}
    (first : Exec M firstLength source middle) (second : Exec M secondLength middle target) :
    Exec M (firstLength + secondLength) source target := by
  induction first with
  | refl => simpa using second
  | cons step _ inductionHypothesis =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Exec.cons step (inductionHypothesis second))

end Exec

variable (M : Machine Q Γ)
open Letter Control

theorem preparation (q : Q) (hq : q ≠ M.halt) (a : Γ) (w : List Γ)
    (L B J : Stream' (Letter Q Γ)) :
    Exec M (2 * w.length + 3)
      ⟨ready q, L, work a :: (w.map work ++ₛ (boundary :: work M.blank :: B)), J⟩
      ⟨execute q, L, work a :: (w.map work ++ₛ (boundary :: B)), work M.blank :: J⟩ := by
  have h₁ := row_step M (.enter q a) hq
    ⟨L, w.map work ++ₛ (boundary :: work M.blank :: B), J⟩
  have h₂ := outward_scan M q hq w (marked a :: L) (boundary :: work M.blank :: B) J
  have h₃ := row_step M (.supply q) hq
    ⟨w.reverse.map work ++ₛ (marked a :: L), B, J⟩
  have h₄ := returning_scan M q hq w.reverse (marked a :: L)
    (boundary :: B) (work M.blank :: J)
  have h₅ := row_step M (.restore q a) hq
    ⟨L, w.map work ++ₛ (boundary :: B), work M.blank :: J⟩
  simp only [List.reverse_reverse, List.length_reverse] at h₄
  have h₁' := Exec.single h₁
  have h₃' := Exec.single h₃
  have h₅' := Exec.single h₅
  simp only [Row.instruction, Instruction.source, Instruction.target,
    Stream'.appendStream'] at h₁' h₃' h₅'
  have hh := (((h₁'.trans h₂).trans h₃').trans h₄).trans h₅'
  convert hh using 1
  omega

theorem preparation_blank_tail (q : Q) (hq : q ≠ M.halt) (a : Γ) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * w.length + 3)
      ⟨ready q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨execute q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        work M.blank :: J⟩ := by
  have hh := preparation M q hq a w L (Stream'.const (work M.blank)) J
  have hb : (work M.blank :: Stream'.const (work M.blank) : Stream' (Letter Q Γ)) =
      Stream'.const (work M.blank) := by
    ext n
    cases n <;> rfl
  simpa only [hb] using hh

theorem checkpoint_length (q : Q) (hq : q ≠ M.halt) (a : Γ) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) (d : Configuration Q Γ)
    (hd : Step M
      ⟨execute q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        work M.blank :: J⟩ d) :
    Exec M (2 * (w.length + 1) + 2)
      ⟨ready q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩ d := by
  have hh := (preparation_blank_tail M q hq a w L J).trans (Exec.single hd)
  convert hh using 1
  omega

theorem checkpoint_stay (q : Q) (hq : q ≠ M.halt) (a : Γ)
    (hm : (M.transition q a).move = .stay) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * (w.length + 1) + 2)
      ⟨ready q, L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨ready (M.transition q a).state, L,
        work (M.transition q a).write ::
          (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        record (.stay q a) :: J⟩ := by
  apply checkpoint_length M q hq a w L J
  exact row_step M (.stay q a) ⟨hq, hm⟩
    ⟨L, w.map work ++ₛ (boundary :: Stream'.const (work M.blank)), J⟩

theorem checkpoint_left (q : Q) (hq : q ≠ M.halt) (a c : Γ)
    (hm : (M.transition q a).move = .left) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * (w.length + 1) + 2)
      ⟨ready q, work c :: L,
        work a :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨ready (M.transition q a).state, L,
        work c :: work (M.transition q a).write ::
          (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        record (.left q a c) :: J⟩ := by
  apply checkpoint_length M q hq a w (work c :: L) J
  exact row_step M (.left q a c) ⟨hq, hm⟩
    ⟨L, w.map work ++ₛ (boundary :: Stream'.const (work M.blank)), J⟩

theorem checkpoint_right (q : Q) (hq : q ≠ M.halt) (a c : Γ)
    (hm : (M.transition q a).move = .right) (w : List Γ)
    (L J : Stream' (Letter Q Γ)) :
    Exec M (2 * (w.length + 2) + 2)
      ⟨ready q, L,
        work a :: work c :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))), J⟩
      ⟨ready (M.transition q a).state, work (M.transition q a).write :: L,
        work c :: (w.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
        record (.right q a c) :: J⟩ := by
  have hh := checkpoint_length M q hq a (c :: w) L J _
    (row_step M (.right q a c) ⟨hq, hm⟩
      ⟨L, w.map work ++ₛ (boundary :: Stream'.const (work M.blank)), J⟩)
  simpa [Nat.add_assoc, Row.instruction, Instruction.target, Stream'.appendStream'] using hh

theorem checkpoint_extend (q : Q) (hq : q ≠ M.halt) (a : Γ)
    (hm : (M.transition q a).move = .right) (L J : Stream' (Letter Q Γ)) :
    Exec M 4
      ⟨ready q, L, work a :: boundary :: Stream'.const (work M.blank), J⟩
      ⟨ready (M.transition q a).state, work (M.transition q a).write :: L,
        work M.blank :: boundary :: Stream'.const (work M.blank),
        record (.extend q a) :: J⟩ := by
  apply checkpoint_length M q hq a [] L J
  have hh := row_step M (.extend q a) ⟨hq, hm⟩
    ⟨L, Stream'.const (work M.blank), J⟩
  have hb : (work M.blank :: Stream'.const (work M.blank) : Stream' (Letter Q Γ)) =
      Stream'.const (work M.blank) := by
    ext n
    cases n <;> rfl
  simpa [Row.instruction, Instruction.source, Instruction.target,
    Stream'.appendStream', hb] using hh

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

end BalancedTransport.Coding
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RecorderSimulation ----
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]
variable [DecidableEq Q]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}
open Stream' Letter Control

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control

theorem next_exec (M : Machine Q Γ) (c : Checkpoint Q Γ) (hc : c.state ≠ M.halt) :
    Exec M (2 * (c.right.length + 1) + 2) (c.expand M) ((c.next M).expand M) := by
  cases hm : (M.transition c.state c.current).move with
  | stay =>
      simpa [next, hm, expand] using
        checkpoint_stay M c.state hc c.current hm c.right (Stream'.map work c.left) c.history
  | left =>
      have h := checkpoint_left M c.state hc c.current c.left.head hm c.right
        (Stream'.map work c.left.tail) c.history
      have hl : (work c.left.head :: Stream'.map work c.left.tail : Stream' (Letter Q Γ)) =
          Stream'.map work c.left := by
        funext n
        cases n <;> rfl
      simpa only [next, hm, expand, List.map_cons, Stream'.appendStream', hl] using h
  | right =>
      cases hw : c.right with
      | nil =>
          simpa [next, hm, expand, hw, Stream'.map_cons] using
            checkpoint_extend M c.state hc c.current hm (Stream'.map work c.left) c.history
      | cons a w =>
          simpa [next, hm, expand, hw, Stream'.map_cons, Stream'.appendStream', Nat.add_assoc] using
            checkpoint_right M c.state hc c.current a hm w (Stream'.map work c.left) c.history

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}
open Stream' Letter Control

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Exec
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ] {M : Machine Q Γ}

end BalancedTransport.Recorder.Exec
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ]

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter
variable [Fintype Q] [Fintype Γ] [DecidableEq Q]

end BalancedTransport.Recorder.Checkpoint
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Recorder OAI.BalancedTransport.Recorder.Checkpoint
open Stream' Letter Control


theorem solution : type_of% @_root_.OAI.BalancedTransport.Recorder.Checkpoint.next_exec := @_root_.OAI.BalancedTransport.Recorder.Checkpoint.next_exec
