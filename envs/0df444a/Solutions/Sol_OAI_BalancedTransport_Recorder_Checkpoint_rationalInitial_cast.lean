-- Prove2me | solution 1 for OAI.BalancedTransport.Recorder.Checkpoint.rationalInitial_cast
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:56:13.856574+00:00
-- url     : https://prove2.me/submissions/206d1da7-acc9-40b5-a99f-101c5df08360

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Recorder OAI.BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter
variable [Fintype Q] [Fintype Γ] [DecidableEq Q]
theorem h45_stream_cons {S : Type*} {B : ℕ} (digit : S → Fin B) (a : S) (s : Stream' S) :
    Coding.stream digit (Stream'.cons a s) = (B:ℝ)⁻¹ * ((digit a : ℝ) + Coding.stream digit s) := by
  unfold Coding.stream
  rw [Real.ofDigits_eq_sum_add_ofDigits _ 1]
  simp only [Finset.range_one, Finset.sum_singleton, Real.ofDigitsTerm, zero_add, pow_one]
  have : (fun i => digit (Stream'.cons a s (i + 1))) = fun i => digit (s i) := rfl
  rw [this]
  show ((digit a : ℕ) : ℝ) * (B:ℝ)⁻¹ + _ = _
  ring

theorem h45_stream_const {S : Type*} {B : ℕ} (hB : 1 < B) (digit : S → Fin B) (a : S) :
    Coding.stream digit (Stream'.const a) = (digit a : ℝ) / ((B:ℝ) - 1) := by
  have h := h45_stream_cons digit a (Stream'.const a)
  rw [← Stream'.const_eq] at h
  have hB' : (1:ℝ) < B := by exact_mod_cast hB
  have hne : (B:ℝ) ≠ 0 := by positivity
  have hinv : (B:ℝ) * (B:ℝ)⁻¹ = 1 := mul_inv_cancel₀ hne
  rw [eq_div_iff (by linarith)]
  linear_combination (B:ℝ) * h + ((digit a : ℝ) + Coding.stream digit (Stream'.const a)) * hinv

theorem h45_stream_append {S : Type*} {B : ℕ} (digit : S → Fin B) (l : List S) (s : Stream' S) :
    Coding.stream digit (l ++ₛ s) =
      (Coding.rationalWord digit l : ℝ) + (B:ℝ)⁻¹ ^ l.length * Coding.stream digit s := by
  induction l with
  | nil => simp [Coding.rationalWord]
  | cons a l ih =>
    rw [Stream'.cons_append_stream, h45_stream_cons, ih]
    simp only [Coding.rationalWord, List.length_cons]
    push_cast
    ring

theorem h45_tail {S : Type*} {B : ℕ} (hB : 1 < B) (digit : S → Fin B) (l : List S) (a : S) :
    ((Coding.rationalTailCode digit l a : ℚ) : ℝ) = Coding.stream digit (l ++ₛ Stream'.const a) := by
  rw [h45_stream_append, h45_stream_const hB]
  simp only [Coding.rationalTailCode]
  push_cast
  ring

theorem solution (M : Machine Q Γ) (q₀ : Q) (w : List Γ) :
    rationalSpace (rationalInitial M q₀ w) = ((initial M q₀ w).expand M).code M := by
  have hcard : 0 < Fintype.card (Letter Q Γ) := Fintype.card_pos_iff.mpr ⟨Letter.boundary⟩
  have hB : 1 < base Q Γ := by unfold base; omega
  have S4 := fun (l : List (Letter Q Γ)) (a : Letter Q Γ) => h45_tail hB (digit (Q := Q) (Γ := Γ)) l a
  funext i
  fin_cases i
  · show ((4 * (placement M (.ready q₀) : ℚ) +
        Coding.rationalTailCode (digit (Q := Q) (Γ := Γ)) [] (work M.blank) : ℚ) : ℝ) =
      Coding.origin (placement M (.ready q₀)) 0 +
        Coding.stream digit (Stream'.map work (Stream'.const M.blank))
    push_cast
    rw [S4]
    simp [Coding.origin, Stream'.map_const]
  · show ((Coding.rationalTailCode (digit (Q := Q) (Γ := Γ))
        (work (w.headD M.blank) :: (w.tail.map work ++ [boundary])) (work M.blank) : ℚ) : ℝ) =
      Coding.origin (placement M (.ready q₀)) 1 +
        Coding.stream digit (work (w.headD M.blank) :: ((w.tail.map work) ++ₛ
          (boundary :: Stream'.const (work M.blank))))
    rw [S4]
    simp [Coding.origin, Stream'.cons_append_stream, Stream'.append_append_stream]
  · show ((Coding.rationalTailCode (digit (Q := Q) (Γ := Γ)) [] (work M.blank) : ℚ) : ℝ) =
      Coding.origin (placement M (.ready q₀)) 2 + Coding.stream digit (Stream'.const (work M.blank))
    rw [S4]
    simp [Coding.origin]

