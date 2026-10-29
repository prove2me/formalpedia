-- Prove2me | solution 1 for MIPStarRE.QPBT.norm_inner_applyOperatorToState_le_sqrt_mul_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:55:47.133822+00:00
-- url     : https://prove2.me/submissions/b8751a7d-bb11-405a-8d74-e727073032ae

-- Generated proof for MIPStarRE.QPBT.norm_inner_applyOperatorToState_le_sqrt_mul_sqrt.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Replacing one factor of a measurement-weighted overlap

The scalar estimates used to combine the two Pauli bases compare averaged
overlaps whose left factor is one complete measurement and whose right factors
are operator families at small state-dependent distance.  This module records
the corresponding Cauchy--Schwarz estimate.  The right-hand families are
arbitrary, so the estimate covers an ordered product of point effects, which
is not itself a measurement.

## References

The estimate is `lem:overlap-gap-distance` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; it is the Cauchy--Schwarz
step at paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1147-1166`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## The Cauchy--Schwarz inequality weighted by a positive operator -/

theorem solution {ι : Type*}
    [Fintype ι] [DecidableEq ι] {A : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hA : 0 ≤ A)
    (u v : EuclideanSpace ℂ ι) :
    ‖inner ℂ u (_root_.MIPStarRE.QPBT.applyOperatorToState A v)‖ ≤
      Real.sqrt (inner ℂ u (_root_.MIPStarRE.QPBT.applyOperatorToState A u)).re *
        Real.sqrt (inner ℂ v (_root_.MIPStarRE.QPBT.applyOperatorToState A v)).re := by
  set R : _root_.LIDT.MIPStarRE.Quantum.Op ι := CFC.sqrt A with hR
  have hRnonneg : 0 ≤ R := CFC.sqrt_nonneg A
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA
  have hRherm : Rᴴ = R :=
    (Matrix.nonneg_iff_posSemidef.mp hRnonneg).isHermitian.eq
  have hadjoint : (Matrix.toEuclideanLin R).adjoint = Matrix.toEuclideanLin R := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hRherm]
  have hsplit : ∀ w z : EuclideanSpace ℂ ι,
      inner ℂ w (_root_.MIPStarRE.QPBT.applyOperatorToState A z) =
        inner ℂ (_root_.MIPStarRE.QPBT.applyOperatorToState R w) (_root_.MIPStarRE.QPBT.applyOperatorToState R z) := by
    intro w z
    have h := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin R) w
      (Matrix.toEuclideanLin R z)
    rw [hadjoint] at h
    rw [← hRR, _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
    exact h
  have hnorm : ∀ w : EuclideanSpace ℂ ι,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState R w‖ =
        Real.sqrt (inner ℂ w (_root_.MIPStarRE.QPBT.applyOperatorToState A w)).re := by
    intro w
    have h2 : ‖_root_.MIPStarRE.QPBT.applyOperatorToState R w‖ ^ 2 =
        (inner ℂ (_root_.MIPStarRE.QPBT.applyOperatorToState R w) (_root_.MIPStarRE.QPBT.applyOperatorToState R w)).re := by
      rw [@norm_sq_eq_re_inner ℂ]
      rfl
    rw [hsplit, ← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [hsplit, ← hnorm, ← hnorm]
  exact norm_inner_le_norm _ _
