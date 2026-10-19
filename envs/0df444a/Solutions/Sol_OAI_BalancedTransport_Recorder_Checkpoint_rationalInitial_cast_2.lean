-- Prove2me | solution 2 for OAI.BalancedTransport.Recorder.Checkpoint.rationalInitial_cast
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:37:45.66099+00:00
-- url     : https://prove2.me/submissions/7a63cc7c-4d3b-42f5-9696-83ad02641841

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RecorderSimulation.lean:L373-L393
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Recorder.Checkpoint.rationalInitial_cast. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.PrefixCoding ----
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
open Stream'
variable {Q Γ : Type*}

namespace Exec

variable {M : Machine Q Γ}

end Exec

variable (M : Machine Q Γ)
open Letter Control

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

theorem stream_cons {B : ℕ} (digit : S → Fin B) (a : S) (s : Stream' S) :
    stream digit (a :: s) = (B : ℝ)⁻¹ * ((digit a : ℝ) + stream digit s) := by
  have hh := Real.ofDigits_eq_sum_add_ofDigits (fun n => digit ((a :: s) n)) 1
  simpa [stream, Real.ofDigitsTerm, Stream'.cons, mul_add, mul_comm] using hh

theorem stream_append {B : ℕ} (digit : S → Fin B) (w : List S) (s : Stream' S) :
    stream digit (w ++ₛ s) =
      prefixPoint (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) w (stream digit s) := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [Stream'.appendStream', stream_cons, ih, prefix_cons]

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

theorem rationalWord_cast {B : ℕ} (digit : S → Fin B) (w : List S) :
    (rationalWord digit w : ℝ) = word (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) w := by
  induction w with
  | nil => simp [rationalWord]
  | cons a w ih => simp [rationalWord, word, ih]

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem stream_const {B : ℕ} (hB : 1 < B) (digit : S → Fin B) (a : S) :
    stream digit (Stream'.const a) = (digit a : ℝ) / ((B : ℝ) - 1) := by
  have hs : (a :: Stream'.const a : Stream' S) = Stream'.const a := by
    funext n
    cases n <;> rfl
  have he := stream_cons digit a (Stream'.const a)
  rw [hs, mul_comm, ← div_eq_mul_inv] at he
  have hB' : (1 : ℝ) < B := by exact_mod_cast hB
  have hn : (B : ℝ) ≠ 0 := by linarith
  have hsub : (B : ℝ) - 1 ≠ 0 := by linarith
  apply (eq_div_iff hsub).mpr
  have he' := (eq_div_iff hn).mp he
  nlinarith only [he']

theorem rationalTailCode_cast {B : ℕ} (hB : 1 < B) (digit : S → Fin B)
    (w : List S) (a : S) :
    (rationalTailCode digit w a : ℝ) = stream digit (w ++ₛ Stream'.const a) := by
  rw [stream_append, stream_const hB]
  simp [rationalTailCode, prefixPoint, rationalWord_cast]

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

omit [DecidableEq Q] in

theorem base_gt_one : 1 < base Q Γ := by
  have hh : 0 < Fintype.card (Letter Q Γ) := Fintype.card_pos_iff.mpr ⟨.boundary⟩
  dsimp [base]
  omega

theorem rationalInitial_cast (M : Machine Q Γ) (q₀ : Q) (w : List Γ) :
    rationalSpace (rationalInitial M q₀ w) = ((initial M q₀ w).expand M).code M := by
  have hb := Coding.rationalTailCode_cast (base_gt_one (Q := Q) (Γ := Γ))
    digit [] (work M.blank : Letter Q Γ)
  have hr := Coding.rationalTailCode_cast (base_gt_one (Q := Q) (Γ := Γ))
    digit (work (w.headD M.blank) :: (w.tail.map work ++ [boundary]))
    (work M.blank : Letter Q Γ)
  have hr' : (Coding.rationalTailCode (digit (Q := Q) (Γ := Γ))
      (work (w.headD M.blank) :: (w.tail.map work ++ [boundary])) (work M.blank) : ℝ) =
      Coding.stream (digit (Q := Q) (Γ := Γ)) (work (w.headD M.blank) ::
        (w.tail.map work ++ₛ (boundary :: Stream'.const (work M.blank)))) := by
    simpa only [Stream'.appendStream', Stream'.append_append_stream] using hr
  simp only [Stream'.nil_append_stream] at hb
  funext i
  fin_cases i
  · simp [rationalSpace, rationalInitial, Configuration.code, Configuration.stacks,
      Coding.codedPoint, Coding.origin, expand, initial, Stream'.map_const, hb]
  · simpa [rationalSpace, rationalInitial, Configuration.code, Configuration.stacks,
      Coding.codedPoint, Coding.origin, expand, initial] using hr'
  · simpa [rationalSpace, rationalInitial, Configuration.code, Configuration.stacks,
      Coding.codedPoint, Coding.origin, expand, initial] using hb

end BalancedTransport.Recorder.Checkpoint
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Recorder OAI.BalancedTransport.Recorder.Checkpoint
open Stream' Letter


theorem solution : type_of% @_root_.OAI.BalancedTransport.Recorder.Checkpoint.rationalInitial_cast := @_root_.OAI.BalancedTransport.Recorder.Checkpoint.rationalInitial_cast
