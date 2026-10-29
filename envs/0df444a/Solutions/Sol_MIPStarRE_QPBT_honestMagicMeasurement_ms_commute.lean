-- Prove2me | solution 1 for MIPStarRE.QPBT.honestMagicMeasurement_ms_commute
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:08:26.672489+00:00
-- url     : https://prove2.me/submissions/ac96961c-3680-489f-929b-2ff2a80e5488

-- Generated proof for MIPStarRE.QPBT.honestMagicMeasurement_ms_commute.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Basic
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_msGame_support_incidence
import Theorems.Thm_MIPStarRE_QPBT_msStrategyMeasurement_incident_commute

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Completeness/HonestStrategy.lean. -/
/-!
# The honest Pauli basis measurements of the completeness proof

This module builds the measurements used by the honest strategy of
`lem:pauli-completeness`: the generalized Pauli basis measurement in a fixed
basis `W`, and its coarse-graining by the binary trace
`h ↦ tr(g_h(u_W) r_W)` which the source calls `A` (for `W = X`) and `B`
(for `W = Z`).  The main results are the observable identity

  `A_0 - A_1 = τ^W(ind_m(u_W) r_W)`

of `eq:finally-got-an-observable`, and the resulting commutation law

  `𝒪_A 𝒪_B = (-1)^γ 𝒪_B 𝒪_A`

with `γ` the phase bit `eq:gamma-value`.  When `γ ≠ 0` the two observables
anticommute, so `thm:ms-from-ac` produces the Magic Square part of the honest
strategy.

## References

The construction is the strategy displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`;
blueprint `lem:pauli-completeness`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
  [Fintype ι] [DecidableEq ι]

/-! ### The generalized Pauli basis measurement -/









/-! ### Symmetry and Hermiticity of the generalized Pauli observables -/



/-! ### Orthogonality of the generalized Pauli projectors

The generalized Pauli projectors in a fixed basis are pairwise orthogonal, so
every coarse-graining of a Pauli basis measurement is again projective.  This is
the projectivity used throughout the honest strategy of `lem:pauli-completeness`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`.
-/








/-! ### The honest Pair/W measurements

For an ambient question `ω = (u_X, u_Z, r_X, r_Z)` the honest player measures
the Pauli register in basis `W` and reports the binary trace
`tr(g_h(u_W) r_W)` of the resulting label.  These are the measurements `A` and
`B` of the proof of `lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1277-1286`.
-/

















/-! ### The honest Point/W measurements -/







/-! ### Honest line measurements -/



















/-! ### The commutation law of the honest pair -/







/-! ### The pointwise Magic Square measurement -/













/-- The Pauli-induced Magic Square measurements commute on an incident
constraint-variable pair. -/
theorem pauliMagicMeasurement_incident_commute (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (hgamma : _root_.MIPStarRE.QPBT.pauliPairGamma P z ≠ 0)
    (i : Fin 6) (k : Fin 3) (a b : _root_.MIPStarRE.QPBT.MsAnswer) :
    Commute ((_root_.MIPStarRE.QPBT.pauliMagicMeasurement P z hgamma (.constraint i)).effect a)
      ((_root_.MIPStarRE.QPBT.pauliMagicMeasurement P z hgamma
        (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k))).effect b) := by
  exact _root_.MIPStarRE.QPBT.msStrategyMeasurement_incident_commute _ _ _ i k a b



/-! ### The Pair measurement in the case `γ = 0`

If the phase bit vanishes, the two honest Pair/W measurements commute and their
product is the Pair measurement `E^{Pair,ω}_{β_X, β_Z} = A_{β_X} B_{β_Z}` of
Equation `eq:pair-definition` in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`.
-/

















end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Completeness/HonestStrategy/MeasurementFamily.lean. -/
/-!
# The honest Pauli measurement family

This module collects the measurements of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy` into a single measurement
family indexed by the question type of the Pauli basis test.  Each honest
measurement acts on the tensor product of the Pauli register with the qubit
supplied to the Magic Square construction, and every outcome is relabelled into
the common answer alphabet of the test.  The results recorded here are the
projectivity and the symmetry of every effect of that family.

## References

The measurement family described here is the one displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`;
blueprint `lem:pauli-completeness`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ### Tensor placement and relabeling -/









/-- A deterministic measurement has zero effect away from its prescribed
outcome. -/
theorem deterministicMeasurement_effect_eq_zero_of_ne {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    {a₀ a : α} (ha : a ≠ a₀) :
    (_root_.MIPStarRE.QPBT.deterministicMeasurement (V := V) a₀).effect a = 0 := by
  rw [show _root_.MIPStarRE.QPBT.deterministicMeasurement (V := V) a₀ =
      (_root_.MIPStarRE.QPBT.unitMeasurement V).postprocess (fun _ => a₀) by rfl]
  apply _root_.MIPStarRE.QPBT.postprocess_effect_eq_zero_of_notMem
  rintro ⟨u, hu⟩
  exact ha hu.symm























/-! ### The total honest measurement family -/









































end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Completeness/Commutation.lean. -/
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

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

set_option maxRecDepth 8000

/-! ### The supported question pairs -/







/-! ### Coarse-graining and tensor placement -/

/-- Pairwise commuting effects stay commuting under coarse-graining. -/
theorem postprocess_commute_of_commute {α β γ δ V : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    [Fintype V] [DecidableEq V]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α V) (N : _root_.LIDT.MIPStarRE.Quantum.Measurement β V)
    (h : ∀ x y, Commute (M.effect x) (N.effect y))
    (f : α → γ) (g : β → δ) (a : γ) (b : δ) :
    Commute ((M.postprocess f).effect a) ((N.postprocess g).effect b) := by
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => h x y







/-- The deterministic measurement reports its prescribed outcome with the
identity effect. -/
theorem deterministicMeasurement_effect_self {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V] (a₀ : α) :
    (_root_.MIPStarRE.QPBT.deterministicMeasurement (V := V) a₀).effect a₀ = 1 := by
  change ((_root_.MIPStarRE.QPBT.unitMeasurement V).postprocess (fun _ => a₀)).effect a₀ = 1
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [_root_.MIPStarRE.QPBT.unitMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne]

/-- Every effect of a deterministic measurement commutes with every
operator. -/
theorem deterministicMeasurement_effect_commute {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    (a₀ a : α) (A : _root_.LIDT.MIPStarRE.Quantum.Op V) :
    Commute ((_root_.MIPStarRE.QPBT.deterministicMeasurement (V := V) a₀).effect a) A := by
  by_cases h : a = a₀
  · subst h
    rw [_root_.MIPStarRE.QPBT.deterministicMeasurement_effect_self]
    exact Commute.one_left A
  · rw [_root_.MIPStarRE.QPBT.deterministicMeasurement_effect_eq_zero_of_ne h]
    exact Commute.zero_left A

/-! ### Honest measurements sharing a Pauli basis -/





/-! ### The Pair and Magic Square measurements -/







/-! ### Commutation along the Pauli type graph -/





end

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







/-! ### Coarse-graining and tensor placement -/













/-! ### Honest measurements sharing a Pauli basis -/





/-! ### The Pair and Magic Square measurements -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) {s₁ s₂ : _root_.MIPStarRE.QPBT.MsType} (hms : Sym2.mk s₁ s₂ ∈ _root_.MIPStarRE.QPBT.msEdges)
    (a b : _root_.MIPStarRE.QPBT.PauliAnswer P) :
    Commute ((_root_.MIPStarRE.QPBT.honestMagicMeasurement P s₁ z).effect a)
      ((_root_.MIPStarRE.QPBT.honestMagicMeasurement P s₂ z).effect b) := by
  classical
  by_cases hg : _root_.MIPStarRE.QPBT.pauliPairGamma P z = 0
  · cases s₁ with
    | constraint i =>
        have h₁ : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.constraint i) z =
            _root_.MIPStarRE.QPBT.deterministicMeasurement (V := _root_.MIPStarRE.QPBT.HonestIndex P)
              (_root_.MIPStarRE.QPBT.PauliAnswer.msTriple 0 : _root_.MIPStarRE.QPBT.PauliAnswer P) := by
          simp [_root_.MIPStarRE.QPBT.honestMagicMeasurement, hg]
        rw [h₁]
        exact _root_.MIPStarRE.QPBT.deterministicMeasurement_effect_commute _ _ _
    | var j =>
        have h₁ : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var j) z =
            _root_.MIPStarRE.QPBT.deterministicMeasurement (V := _root_.MIPStarRE.QPBT.HonestIndex P)
              (_root_.MIPStarRE.QPBT.PauliAnswer.bit 0 : _root_.MIPStarRE.QPBT.PauliAnswer P) := by
          simp [_root_.MIPStarRE.QPBT.honestMagicMeasurement, hg]
        rw [h₁]
        exact _root_.MIPStarRE.QPBT.deterministicMeasurement_effect_commute _ _ _
  · have h₁ : ∀ s : _root_.MIPStarRE.QPBT.MsType, _root_.MIPStarRE.QPBT.honestMagicMeasurement P s z =
        (_root_.MIPStarRE.QPBT.pauliMagicMeasurement P z hg s).postprocess (_root_.MIPStarRE.QPBT.pauliAnswerOfMs (P := P)) := by
      intro s
      simp [_root_.MIPStarRE.QPBT.honestMagicMeasurement, hg]
    have hsupp : (s₁, s₂) ∈ _root_.MIPStarRE.QPBT.msGameSymm.μ.support := by
      change (s₁, s₂) ∈ (Finset.univ : Finset (_root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType)).filter
        (fun ab => Sym2.mk ab.1 ab.2 ∈ _root_.MIPStarRE.QPBT.msEdges)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hms⟩
    rcases _root_.MIPStarRE.QPBT.msGame_support_incidence s₁ s₂ hsupp with
      ⟨i, k, rfl, rfl⟩ | ⟨i, k, rfl, rfl⟩
    · rw [h₁ _, h₁ _]
      exact _root_.MIPStarRE.QPBT.postprocess_commute_of_commute _ _
        (fun x y => _root_.MIPStarRE.QPBT.pauliMagicMeasurement_incident_commute P z hg i k x y) _ _ a b
    · rw [h₁ _, h₁ _]
      exact _root_.MIPStarRE.QPBT.postprocess_commute_of_commute _ _
        (fun x y => (_root_.MIPStarRE.QPBT.pauliMagicMeasurement_incident_commute P z hg i k y x).symm)
        _ _ a b
