-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.chernoffBernoulliMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:01:56.310911+00:00
-- url     : https://prove2.me/submissions/87907125-1a54-4aa7-b81f-cd1061418802

-- Generated proof for MIPStarRE.LDT.Pasting.chernoffBernoulliMatrix.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_bernoulliTailLowerAffine_le_scalarBernoulliTail

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/MatrixChernoff.lean. -/
/-!
# Section 12 pasting: matrix Chernoff comparison

Continuous-functional-calculus form of the Bernoulli matrix Chernoff lemma.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar Bernoulli tail polynomial lifted through continuous functional
calculus is exactly the matrix Bernoulli tail operator. -/
private lemma cfc_scalarBernoulliTail_eq_bernoulliTailOperator
    (A : MIPStarRE.Quantum.Op ι) (hA : IsSelfAdjoint A) (k degree : ℕ) :
    cfc (scalarBernoulliTail k degree) A = bernoulliTailOperator k degree A := by
  let s := Finset.Icc (degree + 1) k
  calc
    cfc (scalarBernoulliTail k degree) A
      = cfc (∑ r ∈ s, fun p => (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))) A := by
          unfold scalarBernoulliTail
          congr 1
          funext p
          simp [s]
    _ = ∑ r ∈ s, cfc (fun p => (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))) A := by
          simpa [s] using
            (cfc_sum (f := fun r p => (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)))
              (a := A) (s := s))
    _ = ∑ r ∈ s, (Nat.choose k r : ℂ) • (A ^ r * (1 - A) ^ (k - r)) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          rw [cfc_const_mul (a := A) (r := (Nat.choose k r : Error))
                (f := fun p => p ^ r * (1 - p) ^ (k - r))]
          rw [cfc_mul (a := A) (f := fun p => p ^ r) (g := fun p => (1 - p) ^ (k - r))]
          rw [cfc_pow (a := A) (f := fun p => p) (n := r) (ha := hA)]
          rw [cfc_pow (a := A) (f := fun p => 1 - p) (n := k - r) (ha := hA)]
          rw [cfc_sub (a := A) (f := fun _ => 1) (g := fun p => p)]
          rw [cfc_const (a := A) (r := (1 : Error)), Algebra.algebraMap_eq_smul_one]
          rw [cfc_id' (R := Error) (a := A) (ha := hA)]
          ext i j
          simp
    _ = bernoulliTailOperator k degree A := by
          simp [bernoulliTailOperator, s]

/-- Continuous functional calculus sends the affine lower envelope to the
expected affine operator expression. -/
private lemma cfc_bernoulliTailLowerAffine_eq
    (A : MIPStarRE.Quantum.Op ι) (hA : IsSelfAdjoint A) (theta c : Error) :
    cfc (bernoulliTailLowerAffine theta c) A =
      ((1 - c : Error) • (1 : MIPStarRE.Quantum.Op ι)) -
        ((1 / (1 - theta) : Error) • (1 - A)) := by
  unfold bernoulliTailLowerAffine
  rw [cfc_sub (a := A) (f := fun _ => 1 - c)
    (g := fun p => (1 / (1 - theta)) * (1 - p))]
  rw [cfc_const (a := A) (r := (1 - c : Error)), Algebra.algebraMap_eq_smul_one]
  rw [cfc_const_mul (a := A) (r := (1 / (1 - theta) : Error)) (f := fun p => 1 - p)]
  rw [cfc_sub (a := A) (f := fun _ => 1) (g := fun p => p)]
  rw [cfc_const (a := A) (r := (1 : Error)), Algebra.algebraMap_eq_smul_one]
  rw [cfc_id' (R := Error) (a := A) (ha := hA)]
  simp



end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: matrix Chernoff comparison

Continuous-functional-calculus form of the Bernoulli matrix Chernoff lemma.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι)
    (hnorm : ψ.IsNormalized)
    (theta : _root_.LIDT.MIPStarRE.LDT.Error) (k degree : ℕ) (X : _root_.LIDT.MIPStarRE.Quantum.Op ι) (kappa : _root_.LIDT.MIPStarRE.LDT.Error)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : _root_.LIDT.MIPStarRE.LDT.Error)) / theta ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error))
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1)
    (hcomplete : _root_.LIDT.MIPStarRE.LDT.CompletenessAtLeast ψ
      ({ outcome := fun _ => X
         total := X
         outcome_pos := fun _ => hXpsd
         sum_eq_total := Fintype.sum_unique fun _ => X
         total_le_one := hXleOne } : _root_.LIDT.MIPStarRE.LDT.SubMeas Unit ι)
      (1 - kappa)) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.ChernoffBernoulliMatrixStatement ψ theta k degree X kappa hXpsd hXleOne := by
  let expTerm : _root_.LIDT.MIPStarRE.LDT.Error := Real.exp (-((theta ^ (2 : ℕ)) * (k : _root_.LIDT.MIPStarRE.LDT.Error)) / 2)
  have hXsa : IsSelfAdjoint X :=
    (Matrix.nonneg_iff_posSemidef.mp hXpsd).isHermitian
  have hPointwise : ∀ x ∈ spectrum _root_.LIDT.MIPStarRE.LDT.Error X,
      _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta expTerm x ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.scalarBernoulliTail k degree x := by
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hXpsd hx
    have hx1 : x ≤ 1 := (CFC.le_one_iff (R := _root_.LIDT.MIPStarRE.LDT.Error) X (ha := hXsa)).1 hXleOne x hx
    exact _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine_le_scalarBernoulliTail theta k degree hθ0 hθ1 hk
      hx0 hx1
  have hContLower : ContinuousOn (_root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta expTerm) (spectrum _root_.LIDT.MIPStarRE.LDT.Error X) := by
    unfold _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine
    fun_prop
  have hContTail : ContinuousOn (_root_.LIDT.MIPStarRE.LDT.Pasting.scalarBernoulliTail k degree) (spectrum _root_.LIDT.MIPStarRE.LDT.Error X) := by
    unfold _root_.LIDT.MIPStarRE.LDT.Pasting.scalarBernoulliTail
    fun_prop
  have hCfcLe :
      cfc (_root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta expTerm) X ≤
        _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailOperator k degree X := by
    calc
      cfc (_root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta expTerm) X ≤ cfc (_root_.LIDT.MIPStarRE.LDT.Pasting.scalarBernoulliTail k degree) X := by
        exact (cfc_le_iff (f := _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta expTerm)
          (g := _root_.LIDT.MIPStarRE.LDT.Pasting.scalarBernoulliTail k degree) (a := X) (hf := hContLower)
          (hg := hContTail) (ha := hXsa)).2 hPointwise
      _ = _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailOperator k degree X :=
        cfc_scalarBernoulliTail_eq_bernoulliTailOperator X hXsa k degree
  have hEvLe :
      _root_.LIDT.MIPStarRE.LDT.ev ψ (cfc (_root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta expTerm) X) ≤
        _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailOperator k degree X) :=
    _root_.LIDT.MIPStarRE.LDT.ev_mono ψ _ _ hCfcLe
  have hEvOneSub : 1 - _root_.LIDT.MIPStarRE.LDT.ev ψ X ≤ kappa := by
    have hmass : 1 - kappa ≤ _root_.LIDT.MIPStarRE.LDT.ev ψ X := hcomplete.lowerBound
    linarith
  have hEvLower :
      1 - kappa / (1 - theta) - expTerm ≤
        _root_.LIDT.MIPStarRE.LDT.ev ψ (cfc (_root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine theta expTerm) X) := by
    have hθden : 0 < 1 - theta := sub_pos.mpr hθ1
    have hfrac : (1 / (1 - theta)) * (1 - _root_.LIDT.MIPStarRE.LDT.ev ψ X) ≤ kappa / (1 - theta) := by
      have hdiv : (1 - _root_.LIDT.MIPStarRE.LDT.ev ψ X) / (1 - theta) ≤ kappa / (1 - theta) :=
        div_le_div_of_nonneg_right hEvOneSub hθden.le
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    have hscale1 :
        _root_.LIDT.MIPStarRE.LDT.ev ψ ((1 - expTerm : _root_.LIDT.MIPStarRE.LDT.Error) • (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)) =
          (1 - expTerm) * _root_.LIDT.MIPStarRE.LDT.ev ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simpa using (_root_.LIDT.MIPStarRE.LDT.ev_scale ψ (1 - expTerm) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
    have hscale2 :
        _root_.LIDT.MIPStarRE.LDT.ev ψ ((1 / (1 - theta) : _root_.LIDT.MIPStarRE.LDT.Error) • (1 - X)) =
          (1 / (1 - theta)) * _root_.LIDT.MIPStarRE.LDT.ev ψ (1 - X) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simpa using (_root_.LIDT.MIPStarRE.LDT.ev_scale ψ (1 / (1 - theta)) (1 - X))
    rw [cfc_bernoulliTailLowerAffine_eq X hXsa theta expTerm, _root_.LIDT.MIPStarRE.LDT.ev_sub, hscale1, hscale2,
      _root_.LIDT.MIPStarRE.LDT.ev_sub, _root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized ψ hnorm]
    linarith
  refine { matrixTailBound := ⟨?_⟩ }
  show _ ≥ _
  unfold _root_.LIDT.MIPStarRE.LDT.subMeasMass
  exact le_trans hEvLower hEvLe
