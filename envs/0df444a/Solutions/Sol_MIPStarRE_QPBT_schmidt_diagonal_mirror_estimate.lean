-- Prove2me | solution 1 for MIPStarRE.QPBT.schmidt_diagonal_mirror_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:49:11.112123+00:00
-- url     : https://prove2.me/submissions/d4ff3b81-6766-497f-b1e4-5dd0780b64fb

-- Generated proof for MIPStarRE.QPBT.schmidt_diagonal_mirror_estimate.
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
import Theorems.Thm_MIPStarRE_QPBT_schmidt_pair_mirror_estimate

namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # State-dependent Schmidt mirrors

This module constructs the opposite-register mirror used in the one-sided
pasting argument. The auxiliary construction uses the spectral theorem and
orthonormal completion, including zero Schmidt coefficients.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, `lem:pasting`;
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#201. The
Schmidt-mirror
argument is a formalization auxiliary, not an additional paper hypothesis.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (values : ι → ℝ) (hvalues : ∀ index, 0 ≤ values index)
    (alice bob : _root_.LIDT.MIPStarRE.Quantum.Op ι) (halice : alice.IsHermitian) (hbob : bob.IsHermitian) :
    (∑ row, ∑ col, Complex.normSq
      ((bob * Matrix.diagonal (fun index => (values index : ℂ)) -
        Matrix.diagonal (fun index => (values index : ℂ)) * bob) row col)) ≤
      2 * ∑ row, ∑ col, Complex.normSq
        ((alice * Matrix.diagonal (fun index => (values index : ℂ)) -
          Matrix.diagonal (fun index => (values index : ℂ)) * bob) row col) := by
  have hpoint (row col : ι) :
      Complex.normSq (bob row col * (values col : ℂ) - (values row : ℂ) * bob row col) ≤
        Complex.normSq (alice row col * (values col : ℂ) -
          (values row : ℂ) * bob row col) +
        Complex.normSq (alice col row * (values row : ℂ) -
          (values col : ℂ) * bob col row) := by
    have hpair := _root_.MIPStarRE.QPBT.schmidt_pair_mirror_estimate (values row) (values col)
      (hvalues row) (hvalues col) (alice row col) (bob row col)
    have hleft : Complex.normSq
        (bob row col * (values col : ℂ) - (values row : ℂ) * bob row col) =
        (values row - values col) ^ 2 * Complex.normSq (bob row col) := by
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      ring
    have hright : Complex.normSq
        (alice col row * (values row : ℂ) - (values col : ℂ) * bob col row) =
        Complex.normSq ((values row : ℂ) * alice row col -
          (values col : ℂ) * bob row col) := by
      rw [← Complex.normSq_conj
        (alice col row * (values row : ℂ) - (values col : ℂ) * bob col row)]
      have ha : (starRingEnd ℂ) (alice col row) = alice row col := halice.apply row col
      have hb : (starRingEnd ℂ) (bob col row) = bob row col := hbob.apply row col
      simp only [map_sub, map_mul, Complex.conj_ofReal, ha, hb, mul_comm]
    rw [hleft, hright]
    simpa only [mul_comm] using hpair
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hsum := Finset.sum_le_sum fun row (_ : row ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum fun col (_ : col ∈ (Finset.univ : Finset ι)) => hpoint row col
  simp only [Finset.sum_add_distrib] at hsum
  have hswap : (∑ row : ι, ∑ col : ι, Complex.normSq
      (alice col row * (values row : ℂ) - (values col : ℂ) * bob col row)) =
      ∑ row : ι, ∑ col : ι, Complex.normSq
        (alice row col * (values col : ℂ) - (values row : ℂ) * bob row col) :=
    Finset.sum_comm
  rw [hswap] at hsum
  linarith
