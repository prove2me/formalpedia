-- Prove2me | solution 1 for MIPStarRE.QPBT.PolynomialImageBounds.avg_weighted_fiber_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:12:56.823285+00:00
-- url     : https://prove2.me/submissions/105f8c6d-d87b-4fd2-af55-cd09d693a2a0

-- Generated proof for MIPStarRE.QPBT.PolynomialImageBounds.avg_weighted_fiber_le.
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
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_PolynomialImageBounds_exists_common_exceptional_coefficient

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.PolynomialImageBounds
end MIPStarRE.QPBT.PolynomialImageBounds

/-!
# Common exceptional fibers for polynomial coefficients

A nonconstant polynomial in one block, with polynomial coefficients in a
second block, has a nonzero coefficient at a nonconstant monomial. Its zero set controls
all exceptional specializations simultaneously, independently of the outcome
of a measurement. The weights may depend on the fixed block but not on the
block being averaged.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1341-1358`,
especially `eq:qld-g-2`; support for blueprint `lem:qld-4-7`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.PolynomialImageBounds

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem solution {n k C D : ℕ}
    (p : MvPolynomial (Fin n) (MvPolynomial (Fin k) F))
    (hp : ¬ ∃ r, p = MvPolynomial.C r)
    (hcoeff : ∀ e, (p.coeff e).totalDegree ≤ C) (hdegree : p.totalDegree ≤ D)
    (w : (Fin k → F) → F → ℝ) (M : ℝ)
    (hw : ∀ z b, 0 ≤ w z b) (hsum : ∀ z, ∑ b, w z b = M) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin k → F)) (fun z => ∑ b : F,
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F))
        (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
          then 1 else 0) * w z b) ≤ ((C + D : ℕ) : ℝ) / Fintype.card F * M := by
  classical
  obtain ⟨e, _, _, hbad, hgood⟩ :=
    _root_.MIPStarRE.QPBT.PolynomialImageBounds.exists_common_exceptional_coefficient p hp hcoeff hdegree
  have hM : 0 ≤ M := by
    rw [← hsum (fun _ => 0)]
    exact Finset.sum_nonneg fun b _ => hw _ b
  have hpoint (z : Fin k → F) :
      (∑ b : F, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F))
        (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
          then 1 else 0) * w z b) ≤
      (if MvPolynomial.eval z (p.coeff e) = 0 then 1 else 0) * M +
        (D : ℝ) / Fintype.card F * M := by
    by_cases hz : MvPolynomial.eval z (p.coeff e) = 0
    · simp only [hz, if_true, one_mul]
      apply le_trans (b := M)
      · rw [← hsum z]
        apply Finset.sum_le_sum
        intro b _
        apply le_trans (b := 1 * w z b)
        · apply mul_le_mul_of_nonneg_right _ (hw z b)
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_le_const
          intro x
          split_ifs <;> norm_num
        · rw [one_mul]
      · exact le_add_of_nonneg_right (mul_nonneg (by positivity) hM)
    · simp only [hz, if_false, zero_mul, zero_add]
      rw [← hsum z, Finset.mul_sum]
      exact Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_right (hgood z hz b) (hw z b)
  calc
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin k → F)) (fun z =>
        (if MvPolynomial.eval z (p.coeff e) = 0 then 1 else 0) * M +
          (D : ℝ) / Fintype.card F * M) := _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ hpoint
    _ ≤ (C : ℝ) / Fintype.card F * M + (D : ℝ) / Fintype.card F * M := by
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_mul_const, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
      exact add_le_add (mul_le_mul_of_nonneg_right hbad hM) le_rfl
    _ = _ := by push_cast; ring
