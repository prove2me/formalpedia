-- Prove2me | solution 1 for LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:53:52.221704+00:00
-- url     : https://prove2.me/submissions/1548330d-dea4-4a8f-aaa8-78077fff1ce5

-- Generated proof for MIPStarRE.Quantum.Measurement.postprocess_comp.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Upstream

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Distribution.IsProbability
end LIDT.MIPStarRE.LDT.Distribution.IsProbability
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement

/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `f382c801026f53a9efc260fdee707cb35e0adb15`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open LIDT.MIPStarRE.Quantum.Measurement
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

theorem solution {γ : Type*} [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α d) (f : α → β) (g : β → γ) :
    (M.postprocess f).postprocess g = M.postprocess (fun a => g (f a)) := by
  classical
  apply _root_.LIDT.MIPStarRE.Quantum.Measurement.ext
  intro c
  calc
    ((M.postprocess f).postprocess g).effect c =
        ∑ b : β, if g b = c then
          ∑ a : α, if f a = b then M.effect a else 0
        else 0 := by
          change (∑ b ∈ Finset.univ.filter (fun b : β => g b = c),
            ∑ a ∈ Finset.univ.filter (fun a : α => f a = b), M.effect a) = _
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro b _
          by_cases hgb : g b = c
          · simp only [hgb, ite_true]
            rw [Finset.sum_filter]
          · simp [hgb]
    _ = ∑ b : β, ∑ a : α,
        if g b = c ∧ f a = b then M.effect a else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hgc : g b = c <;> simp [hgc]
    _ = ∑ a : α, ∑ b : β,
        if g b = c ∧ f a = b then M.effect a else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ a : α,
        if g (f a) = c then M.effect a else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases hgc : g (f a) = c
          · rw [Finset.sum_eq_single (f a)]
            · simp [hgc]
            · intro b _ hba
              by_cases hfa : f a = b
              · exact (hba hfa.symm).elim
              · simp [hfa]
            · simp
          · have hzero :
                (∑ b : β,
                  if g b = c ∧ f a = b then M.effect a else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro b _
              by_cases hfa : f a = b
              · subst b
                simp [hgc]
              · simp [hfa]
            simp [hgc, hzero]
    _ = (M.postprocess (fun a => g (f a))).effect c := by
          change _ = ∑ a ∈ Finset.univ.filter
            (fun a : α => g (f a) = c), M.effect a
          rw [Finset.sum_filter]
