-- Prove2me | solution 1 for MIPStarRE.QPBT.inner_prodShuffle_vecTensor_heteroKron
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:40:56.831503+00:00
-- url     : https://prove2.me/submissions/d89bd25c-08a6-4081-8bb3-26e14131ba21

-- Generated proof for MIPStarRE.QPBT.inner_prodShuffle_vecTensor_heteroKron.
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
import Definitions.Def_QPBT_QPBT_State

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-! # Consistency under independent additive convolution

Adding the outcomes of an independently perfectly correlated ancillary measurement
pair preserves the consistency defect. The four register types are independent;
`prodShuffle` places the two registers of each player next to one another.

These are formalization-only auxiliary identities. Perfect ancillary correlation
is a hypothesis of the generic result, to be proved for the Pauli measurements
before applying it to the expanded point construction.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-438`,
  the expanded state and the convolution formula for expanded point effects.
- The same paper, `lem:qld-construct-the-paulis`.
- Blueprint `def:expanded-state` and `def:expanded-point-measurement`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#266; the ideal-point specialization is the separate issue
  Dengnifer/MIPStarRE-QPBT-bak#267.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



variable {ιA ιB κA κB : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]

theorem solution
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (φ : EuclideanSpace ℂ (κA × κB))
    (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) (R : _root_.LIDT.MIPStarRE.Quantum.Op κA) (T : _root_.LIDT.MIPStarRE.Quantum.Op κB) :
    inner ℂ (_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor ψ φ))
        (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron A R) (_root_.MIPStarRE.QPBT.heteroKron B T))
          (_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor ψ φ))) =
      inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron A B) ψ) *
        inner ℂ φ (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron R T) φ) := by
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [← (_root_.MIPStarRE.QPBT.prodShuffle : (ιA × ιB) × (κA × κB) ≃ _).sum_comp]
  simp_rw [← (_root_.MIPStarRE.QPBT.prodShuffle : (ιA × ιB) × (κA × κB) ≃ _).sum_comp]
  change (∑ p : (ιA × ιB) × (κA × κB), ∑ q : (ιA × ιB) × (κA × κB),
    ((A p.1.1 q.1.1 * R p.2.1 q.2.1) * (B p.1.2 q.1.2 * T p.2.2 q.2.2) *
      (ψ q.1 * φ q.2)) * star (ψ p.1 * φ p.2)) =
    ∑ i : ιA × ιB, ∑ j : ιA × ιB, ∑ k : κA × κB, ∑ l : κA × κB,
      ((A i.1 j.1 * B i.2 j.2 * ψ j) * star (ψ i)) *
        ((R k.1 l.1 * T k.2 l.2 * φ l) * star (φ k))
  simp only [Fintype.sum_prod_type (α₁ := ιA × ιB) (α₂ := κA × κB), star_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  congr! 4 with i j k l
  ring
