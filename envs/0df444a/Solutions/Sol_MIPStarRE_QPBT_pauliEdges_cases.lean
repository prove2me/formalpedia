-- Prove2me | solution 1 for MIPStarRE.QPBT.pauliEdges_cases
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:56:54.301482+00:00
-- url     : https://prove2.me/submissions/ff77469e-2dca-4103-a4cc-745306243a60

-- Generated proof for MIPStarRE.QPBT.pauliEdges_cases.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Test_Completeness_Commutation
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Commutation of the honest Pauli measurements

This module proves that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` has commuting effects
on every question pair of positive weight for the Pauli question sampler.  The
argument first characterises the supported question pairs as the typed
conditionally linear images of a single ambient coefficient vector along an edge
of the Pauli type graph, and then treats the five edge families of that graph.

## References

This is the commutation obligation in the proof of `lem:pauli-completeness`,
blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1382`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



set_option maxRecDepth 8000

/-! ### The supported question pairs -/

theorem solution {t₁ t₂ : _root_.MIPStarRE.QPBT.PauliType} (h : Sym2.mk t₁ t₂ ∈ _root_.MIPStarRE.QPBT.pauliEdges) :
    t₁ = t₂ ∨
      (∃ s₁ s₂ : _root_.MIPStarRE.QPBT.MsType, t₁ = .ms s₁ ∧ t₂ = .ms s₂ ∧ Sym2.mk s₁ s₂ ∈ _root_.MIPStarRE.QPBT.msEdges) ∨
      _root_.MIPStarRE.QPBT.PauliEdgeOriented t₁ t₂ ∨ _root_.MIPStarRE.QPBT.PauliEdgeOriented t₂ t₁ := by
  classical
  simp only [_root_.MIPStarRE.QPBT.pauliEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
    Prod.exists] at h
  rcases h with (((hl | ((ha | hb) | hc)) | (hd | he | he)) | hp) | hm
  · obtain ⟨a, hEq⟩ := hl
    rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact Or.inl rfl
  · obtain ⟨W, hEq⟩ := ha
    rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨W, rfl, Or.inl rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl, Or.inl rfl⟩)))
  · obtain ⟨W, hEq⟩ := hb
    rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨W, rfl, Or.inr (Or.inl rfl)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl, Or.inr (Or.inl rfl)⟩)))
  · obtain ⟨W, hEq⟩ := hc
    rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨W, rfl, Or.inr (Or.inr (Or.inl rfl))⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl, Or.inr (Or.inr (Or.inl rfl))⟩)))
  · obtain ⟨W, hEq⟩ := hd
    rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨W, rfl, Or.inr (Or.inr (Or.inr rfl))⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl, Or.inr (Or.inr (Or.inr rfl))⟩)))
  · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
  · obtain ⟨W, hEq⟩ := hp
    rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨W, rfl, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨W, rfl, rfl⟩))))
  · obtain ⟨s₁, s₂, hms, hEq⟩ := hm
    rcases Sym2.eq_iff.mp hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨s₁, s₂, rfl, rfl, hms⟩)
    · exact Or.inr (Or.inl ⟨s₂, s₁, rfl, rfl, by rwa [Sym2.eq_swap]⟩)
