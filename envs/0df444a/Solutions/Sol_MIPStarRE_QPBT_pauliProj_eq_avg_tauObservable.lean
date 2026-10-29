-- Prove2me | solution 1 for MIPStarRE.QPBT.pauliProj_eq_avg_tauObservable
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:54:55.209227+00:00
-- url     : https://prove2.me/submissions/24fe13b3-a512-46d5-8dc4-8eeb32a710cc

-- Generated proof for MIPStarRE.QPBT.pauliProj_eq_avg_tauObservable.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Pauli

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Generalized Pauli operators and EPR states

The definitions here use finite matrix entries and rank-one projectors, so they
are usable by the later game statements without introducing an abstract
operator algebra.  The observable/projector expansions are obtained from
finite-field Fourier orthogonality in characteristic two.

## References

The source-facing nodes are blueprint `def:lin-reg`, `def:EPR`,
`def:generalized-pauli`, and `lem:pauli-observable-expansion`.  The paper origin is
`references/qpbt-paper/04_preliminaries.tex:908-1161`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.Preliminaries

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod 2) K]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : _root_.MIPStarRE.QPBT.PauliKind) (e : ι → K) :
    _root_.MIPStarRE.QPBT.pauliProj W e =
      (Fintype.card (ι → K) : ℂ)⁻¹ •
        ∑ a : ι → K, _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct a e)) • _root_.MIPStarRE.QPBT.tauObservable W a := by
  have hcoeff (x : ι → K) :
      ∑ i : ι → K,
          (Fintype.card (ι → K) : ℂ)⁻¹ *
            (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct i e)) *
              _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct i x))) =
        if x = e then 1 else 0 := by
    rw [← Finset.mul_sum]
    rw [show
      (∑ i : ι → K,
        _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct i e)) *
          _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct i x))) =
        ∑ i : ι → K, _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.binTrace K (dotProduct i (e + x))) by
          apply Finset.sum_congr rfl
          intro i _
          exact phaseSign_binTrace_dotProduct_add i e x]
    rw [sum_phaseSign_dotProduct]
    have hzero : e + x = 0 ↔ x = e := by
      simpa using
        (add_add_eq_zero_iff_eq_add (K := K) e x (0 : ι → K))
    by_cases hx : x = e
    · rw [if_pos hx, if_pos (hzero.mpr hx)]
      exact inv_mul_cancel₀
        (show (Fintype.card (ι → K) : ℂ) ≠ 0 by positivity)
    · rw [if_neg hx, if_neg (fun h => hx (hzero.mp h))]
      simp
  simp_rw [_root_.MIPStarRE.QPBT.tauObservable_eq_sum_pauliProj]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  simp_rw [hcoeff]
  simp
