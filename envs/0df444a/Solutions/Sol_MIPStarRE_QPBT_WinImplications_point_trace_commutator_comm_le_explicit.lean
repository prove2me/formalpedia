-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.point_trace_commutator_comm_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:27:10.619981+00:00
-- url     : https://prove2.me/submissions/2b43773a-5f13-433c-8acf-e402bd1409cd

-- Generated proof for MIPStarRE.QPBT.WinImplications.point_trace_commutator_comm_le_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_CommutingObs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_op_dist_sq_commutator_le_explicit

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/WinImplications/CommutingObs.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyCommObs
/-!
# Approximate commutation of the point observables on commuting tuples

This module carries out the commuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`: the chain of
consistency relations `eq:lc-11`, the commutation analysis
`lem:commutation-analysis`, and the expansion `eq:lc-12` of the observables in
terms of the trace-coarse-grained point projections.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-341`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications



/-! ## Algebraic preliminaries -/







/-! ## Pair/W self-consistency on commuting tuples -/





/-! ## The chained relation of Equation `eq:lc-11` -/



/-! ## The commutation analysis on commuting tuples -/

/-- Padding an answer alphabet by a unit factor does not change the operator
distance. Formalization-only support for `lem:commutation-analysis`, blueprint
`ch12_qpbt_games.tex:418-431`. -/
theorem opFamilyDistSq_unit_prod {X β ι : Type*} [Fintype β]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → β → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x (ub : Unit × β) => M x ub.2)
        (fun x (ub : Unit × β) => N x ub.2) ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ M N ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  congr 1
  funext x
  rw [Fintype.sum_prod_type]
  simp

/-- Relabelling the outcomes of a measurement along the inclusion into a
one-point product leaves every effect unchanged. Formalization-only support for
`lem:commutation-analysis`, blueprint `ch12_qpbt_games.tex:418-431`. -/
theorem unitProd_postprocess_effect {β ι : Type*} [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement β ι)
    (b : β) :
    (M.postprocess (fun b' : β => ((), b'))).effect ((), b) = M.effect b := by
  classical
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [show (Finset.univ.filter
      (fun b' : β => ((), b') = ((), b))) = {b} from by
    ext b'
    simp [Prod.ext_iff, Finset.mem_filter]]
  exact Finset.sum_singleton _ _





/-! ## From projections to observables -/









end WinImplications

end

end MIPStarRE.QPBT

/-!
# Approximate commutation of the point observables on commuting tuples

This module carries out the commuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`: the chain of
consistency relations `eq:lc-11`, the commutation analysis
`lem:commutation-analysis`, and the expansion `eq:lc-12` of the observables in
terms of the trace-coarse-grained point projections.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-341`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications



/-! ## Algebraic preliminaries -/







/-! ## Pair/W self-consistency on commuting tuples -/





/-! ## The chained relation of Equation `eq:lc-11` -/



/-! ## The commutation analysis on commuting tuples -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyCommObs

theorem solution :
    ∀ {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL]
        [Fintype ιR] [DecidableEq ιR]
        (MX MZ : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
        (N : _root_.MIPStarRE.QPBT.PauliTuple P →
          _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2 × ZMod 2) ιR)
        (χ : EuclideanSpace ℂ (ιL × ιR)) {δ : ℝ},
      (∀ ω, _root_.MIPStarRE.QPBT.Measurement.IsProjective (N ω)) →
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.commTupleDist P)
          (fun ω b => _root_.MIPStarRE.QPBT.heteroKron ((MX ω).effect b) 1)
          (fun ω b => _root_.MIPStarRE.QPBT.heteroKron 1
            (((N ω).postprocess (fun bits => bits.1)).effect b)) χ ≤ δ →
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.commTupleDist P)
          (fun ω b => _root_.MIPStarRE.QPBT.heteroKron ((MZ ω).effect b) 1)
          (fun ω b => _root_.MIPStarRE.QPBT.heteroKron 1
            (((N ω).postprocess (fun bits => bits.2)).effect b)) χ ≤ δ →
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.commTupleDist P) (fun ω =>
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron
          ((MX ω).effect 1 * (MZ ω).effect 1 -
            (MZ ω).effect 1 * (MX ω).effect 1) 1) χ‖ ^ 2) ≤ 16 * δ := by
  classical
  intro P ιL ιR _ _ _ _ MX MZ N χ δ hN hX hZ
  set A : _root_.MIPStarRE.QPBT.PauliTuple P →
      _root_.LIDT.MIPStarRE.Quantum.Measurement (Unit × ZMod 2) ιL := fun ω =>
    (MX ω).postprocess (fun b => ((), b)) with hAdef
  set D : _root_.MIPStarRE.QPBT.PauliTuple P →
      _root_.LIDT.MIPStarRE.Quantum.Measurement (Unit × ZMod 2) ιL := fun ω =>
    (MZ ω).postprocess (fun c => ((), c)) with hDdef
  set B : _root_.MIPStarRE.QPBT.PauliTuple P →
      _root_.LIDT.MIPStarRE.Quantum.Measurement ((Unit × ZMod 2) × ZMod 2) ιR := fun ω =>
    (N ω).postprocess (fun bits => (((), bits.1), bits.2)) with hBdef
  have hBproj : ∀ ω, _root_.MIPStarRE.QPBT.Measurement.IsProjective (B ω) := by
    intro ω
    exact _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _ (hN ω) _
  have hAB : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.commTupleDist P)
      (fun ω ab => _root_.MIPStarRE.QPBT.heteroKron ((A ω).effect ab) 1)
      (fun ω ab => _root_.MIPStarRE.QPBT.heteroKron 1
        (((B ω).postprocess (fun abc => abc.1)).effect ab)) χ ≤ δ := by
    have hrw : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω ab => _root_.MIPStarRE.QPBT.heteroKron ((A ω).effect ab) 1)
        (fun ω ab => _root_.MIPStarRE.QPBT.heteroKron 1
          (((B ω).postprocess (fun abc => abc.1)).effect ab)) χ =
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω (ub : Unit × ZMod 2) => _root_.MIPStarRE.QPBT.heteroKron
          ((MX ω).effect ub.2) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR))
        (fun ω (ub : Unit × ZMod 2) => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL)
          (((N ω).postprocess (fun bits => bits.1)).effect ub.2)) χ := by
      congr 1 <;> funext ω ab
      · rw [hAdef]
        obtain ⟨⟨⟩, b⟩ := ab
        rw [_root_.MIPStarRE.QPBT.WinImplications.unitProd_postprocess_effect]
      · obtain ⟨⟨⟩, b⟩ := ab
        congr 1
        rw [hBdef, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
        rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
          _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext bits
        simp [Prod.ext_iff, Finset.mem_filter]
    refine le_of_eq_of_le hrw ?_
    refine le_of_eq_of_le (_root_.MIPStarRE.QPBT.WinImplications.opFamilyDistSq_unit_prod (_root_.MIPStarRE.QPBT.commTupleDist P)
      (fun ω b => _root_.MIPStarRE.QPBT.heteroKron ((MX ω).effect b) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR))
      (fun ω b => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL)
        (((N ω).postprocess (fun bits => bits.1)).effect b)) χ) hX
  have hDB : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.commTupleDist P)
      (fun ω ac => _root_.MIPStarRE.QPBT.heteroKron ((D ω).effect ac) 1)
      (fun ω ac => _root_.MIPStarRE.QPBT.heteroKron 1
        (((B ω).postprocess (fun abc => (abc.1.1, abc.2))).effect ac))
      χ ≤ δ := by
    have hrw : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω ac => _root_.MIPStarRE.QPBT.heteroKron ((D ω).effect ac) 1)
        (fun ω ac => _root_.MIPStarRE.QPBT.heteroKron 1
          (((B ω).postprocess (fun abc => (abc.1.1, abc.2))).effect ac))
        χ =
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω (ub : Unit × ZMod 2) => _root_.MIPStarRE.QPBT.heteroKron
          ((MZ ω).effect ub.2) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR))
        (fun ω (ub : Unit × ZMod 2) => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL)
          (((N ω).postprocess (fun bits => bits.2)).effect ub.2)) χ := by
      congr 1 <;> funext ω ac
      · rw [hDdef]
        obtain ⟨⟨⟩, c⟩ := ac
        rw [_root_.MIPStarRE.QPBT.WinImplications.unitProd_postprocess_effect]
      · obtain ⟨⟨⟩, c⟩ := ac
        congr 1
        rw [hBdef, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
        rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
          _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext bits
        simp [Prod.ext_iff, Finset.mem_filter]
    refine le_of_eq_of_le hrw ?_
    refine le_of_eq_of_le (_root_.MIPStarRE.QPBT.WinImplications.opFamilyDistSq_unit_prod (_root_.MIPStarRE.QPBT.commTupleDist P)
      (fun ω b => _root_.MIPStarRE.QPBT.heteroKron ((MZ ω).effect b) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR))
      (fun ω b => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL)
        (((N ω).postprocess (fun bits => bits.2)).effect b)) χ) hZ
  have hout := _root_.MIPStarRE.QPBT.op_dist_sq_commutator_le_explicit
    (_root_.MIPStarRE.QPBT.commTupleDist P) A B D χ δ hBproj hAB hDB
  refine le_trans ?_ hout
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  intro ω
  simp only [sub_zero]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum
    (f := fun abc : (Unit × ZMod 2) × ZMod 2 =>
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron
        ((A ω).effect (abc.1.1, abc.1.2) * (D ω).effect (abc.1.1, abc.2) -
          (D ω).effect (abc.1.1, abc.2) * (A ω).effect (abc.1.1, abc.1.2)) 1)
        χ‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ (((), 1), 1)))
  rw [hAdef, hDdef]
  simp only [_root_.MIPStarRE.QPBT.WinImplications.unitProd_postprocess_effect]
