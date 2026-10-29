-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:57:38.181285+00:00
-- url     : https://prove2.me/submissions/50acde16-d7bf-4f16-b289-1b5318d38f82

-- Generated proof for MIPStarRE.LDT.Test.mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_mainFormalStep5_expansionBound

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Preliminaries/PolynomialAgreement.lean. -/
/-!
# Polynomial agreement bound (Step 5 hammer)

Public packaging of Schwartz-Zippel for the project's `Polynomial params`
class. This is the building block invoked at:

* paper `references/ldt-paper/inductive_step.tex`, lines 119–133 — the
  `md/q` term in the `mainFormal` self-consistency cascade,
* paper `references/ldt-paper/commutativity-G.tex`, the analogous step in
  `comMain` (issue #297).

The earlier private form of this lemma lived in
`MIPStarRE.LDT.Commutativity.Scaffold.Symmetry`. Promoting it lets both `comMain`
and `mainFormal` Step 5 (#425) share one proof.

## References

* `references/ldt-paper/inductive_step.tex`
* `references/ldt-paper/preliminaries.tex`, Section 3
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT















open Classical in
/-- `mainFormal` Step 5's tensor-valued Schwartz--Zippel loss.

This is the specialization of `polynomialCollision_sandwichTensor_le_mdq` with
no outer sandwich. It supplies exactly the paper's line-126 estimate for the
collision term after the evaluated self-consistency defect has been expanded. -/
lemma polynomialCollisionMass_le_mdq
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ιA × ιB)) (hnorm : ψ.IsNormalized)
    (Left : SubMeas (Polynomial params) ιA) (Right : SubMeas (Polynomial params) ιB) :
    polynomialCollisionMass params ψ Left Right ≤
      (params.m * params.d : Error) / params.q := by
  let One : SubMeas Unit ιA :=
    SubMeas.singleOutcome (1 : MIPStarRE.Quantum.Op ιA) zero_le_one le_rfl
  have h := polynomialCollision_sandwichTensor_le_mdq
    (params := params) (ψ := ψ) (hnorm := hnorm)
    (Outer := One) (Inner := Left) (Right := Right)
  simpa [polynomialCollisionMass, One, leftTensor_mul_rightTensor_eq_opTensor] using h

end MIPStarRE.LDT.Preliminaries

end

end LIDT

open LIDT
/-!
# `mainFormal` Step 5 — Schwartz--Zippel self-consistency handoff

This file isolates the paper's Step 5 bridge in
`references/ldt-paper/inductive_step.tex`, lines 119--133.  The algebraic
expansion/reindexing from evaluated consistency to the full-polynomial
consistency defect is proved here, and the genuinely Schwartz--Zippel part is
provided by the shared tensor bound
`Preliminaries.polynomialCollisionMass_le_mdq`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (hnorm : ψ.IsNormalized)
    (Left : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA) (Right : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB)
    (ζ : _root_.LIDT.MIPStarRE.LDT.Error)
    (hevaluated : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Left)
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Right) ζ) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Left) (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Right)
      (ζ + (params.m * params.d : _root_.LIDT.MIPStarRE.LDT.Error) / params.q) := by
  constructor
  calc
    _root_.LIDT.MIPStarRE.LDT.bipartiteConsError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Left) (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Right)
      ≤ _root_.LIDT.MIPStarRE.LDT.bipartiteConsError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Left)
          (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Right) +
        _root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialCollisionMass params ψ Left Right :=
        _root_.LIDT.MIPStarRE.LDT.Test.mainFormalStep5_expansionBound params ψ Left Right
    _ ≤ ζ + (params.m * params.d : _root_.LIDT.MIPStarRE.LDT.Error) / params.q := by
        have hcollision :=
          _root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialCollisionMass_le_mdq params ψ hnorm Left Right
        linarith [hevaluated.offDiagonalBound, hcollision]
