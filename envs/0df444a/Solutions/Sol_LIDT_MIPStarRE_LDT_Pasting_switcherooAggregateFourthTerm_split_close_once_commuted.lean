-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm_split_close_once_commuted
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:06:53.569229+00:00
-- url     : https://prove2.me/submissions/2db40eb9-47e3-4369-829d-f5c46df42212

-- Generated proof for MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm_split_close_once_commuted.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
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
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_projSubMeas_sandwich_sum_le_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_switcherooAggregateFourthTerm_eq_split

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Pasting/SwitcherooSetup/Infrastructure.lean. -/
/-!
# Section 12 pasting: switcheroo infrastructure

Initial switcheroo infrastructure and aggregate expansion helpers.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Switcheroo infrastructure -/





/-- Read the switcheroo point-product commutation hypothesis as an average
`qSDDCore` bound. -/
lemma switcherooPointProductCommutation_coreBound
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (chi : Error)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDCore ψbi
          (fun go => (switcherooPointProductLeft params family M q).outcome go)
          (fun go => (switcherooPointProductRight params family M q).outcome go)) ≤
      chi := by
  simpa [sddErrorOp, qSDDOp] using hcomm.squaredDistanceBound





/-- The total operator of a projective submeasurement is idempotent. -/
lemma projSubMeas_total_sq
    {Outcome : Type*} [Fintype Outcome]
    (P : ProjSubMeas Outcome ι) :
    P.toSubMeas.total * P.toSubMeas.total = P.toSubMeas.total := by
  simpa using MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P



end MIPStarRE.LDT.Pasting

end

/- Source helpers from MIPStarRE/LDT/Pasting/SwitcherooContraction/Split.lean. -/
/-!
# Section 12 pasting: switcheroo split contraction

The split-form contraction and first mixed-term transfer.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Shared switcheroo contraction helper definitions -/



/-- The complete-part total operator is Hermitian. -/
lemma switcherooCompletePartTotal_hermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    ((completePartSubMeas params family q.1).total)ᴴ =
      (completePartSubMeas params family q.1).total :=
  (Matrix.nonneg_iff_posSemidef.mp
    (SubMeas.total_nonneg (completePartSubMeas params family q.1))).isHermitian.eq

/-- The complete-part total operator is idempotent. -/
lemma switcherooCompletePartTotal_sq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (completePartSubMeas params family q.1).total *
        (completePartSubMeas params family q.1).total =
      (completePartSubMeas params family q.1).total := by
  simpa [completePartSubMeas, postprocess_total] using
    projSubMeas_total_sq (family.meas q.1)

/-- The complete-part total operator is bounded by the identity. -/
lemma switcherooCompletePartTotal_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (completePartSubMeas params family q.1).total ≤ 1 :=
  (completePartSubMeas params family q.1).total_le_one

/-- Every outcome of the external projective family is Hermitian. -/
lemma switcherooMeasuredOutcome_hermitian
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (o : Outcome) :
    ((M q.2).outcome o)ᴴ = (M q.2).outcome o :=
  (Matrix.nonneg_iff_posSemidef.mp ((M q.2).outcome_pos o)).isHermitian.eq

/-- Every slice outcome of the completed family is Hermitian. -/
lemma switcherooSliceOutcome_hermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params)
    (g : Polynomial params) :
    ((family.meas q.1).outcome g)ᴴ = (family.meas q.1).outcome g :=
  (Matrix.nonneg_iff_posSemidef.mp ((family.meas q.1).outcome_pos g)).isHermitian.eq











/-- The middle sandwich sum used in the contraction bounds is a contraction. -/
lemma switcherooAggregateFourthTerm_middle_sum_le_one
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    ∑ o : Outcome,
        (M q.2).outcome o * (completePartSubMeas params family q.1).total * (M q.2).outcome o ≤ 1 :=
  projSubMeas_sandwich_sum_le_one (M q.2) ((completePartSubMeas params family q.1).total)
    (switcherooCompletePartTotal_le_one params family q)

/-- Contraction witness for the first `sqrt chi` switcheroo transfer. -/
private lemma switcherooAggregateFourthTerm_split_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    (∑ go : Polynomial params × Outcome,
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1)) *
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1))ᴴ) ≤ 1 := by
  let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family q.1).total
  let Gq : Polynomial params → MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome
  let Mo : Outcome → MIPStarRE.Quantum.Op ι := (M q.2).outcome
  have hGherm : Gᴴ = G := by
    simpa [G] using switcherooCompletePartTotal_hermitian params family q
  have hGsq : G * G = G := by
    simpa [G] using switcherooCompletePartTotal_sq params family q
  have hMoherm : ∀ o : Outcome, (Mo o)ᴴ = Mo o := by
    intro o
    simpa [Mo] using switcherooMeasuredOutcome_hermitian params M q o
  have hGqherm : ∀ g : Polynomial params, (Gq g)ᴴ = Gq g := by
    intro g
    simpa [Gq] using switcherooSliceOutcome_hermitian params family q g
  have hsum :
      (∑ go : Polynomial params × Outcome,
          (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1)) *
            (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1))ᴴ) =
        leftTensor (ι₂ := ι) (G * (∑ o : Outcome, Mo o * G * Mo o) * G) := by
    calc
      (∑ go : Polynomial params × Outcome,
          (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1)) *
            (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1))ᴴ)
        = ∑ go : Polynomial params × Outcome,
            leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1 * Mo go.2 * G) := by
              refine Finset.sum_congr rfl ?_
              intro go _
              calc
                (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1)) *
                    (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1))ᴴ
                  = (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1)) *
                      leftTensor (ι₂ := ι) ((G * Mo go.2 * Gq go.1)ᴴ) := by
                        congr 2
                        simpa [leftTensor, opTensor] using
                          (conjTranspose_opTensor (G * Mo go.2 * Gq go.1)
                            (1 : MIPStarRE.Quantum.Op ι))
                _ = leftTensor (ι₂ := ι)
                      ((G * Mo go.2 * Gq go.1) * (G * Mo go.2 * Gq go.1)ᴴ) := by
                        rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1 * Mo go.2 * G) := by
                        congr 1
                        calc
                          (G * Mo go.2 * Gq go.1) * (G * Mo go.2 * Gq go.1)ᴴ
                            = G * (Mo go.2 * (Gq go.1 * (Gq go.1 * (Mo go.2 * G)))) := by
                                simp [Matrix.conjTranspose_mul, mul_assoc, hGherm,
                                  hMoherm, hGqherm]
                          _ = G * (Mo go.2 * (Gq go.1 * (Mo go.2 * G))) := by
                                have hproj : Gq go.1 * Gq go.1 = Gq go.1 := by
                                  simpa [Gq] using (family.meas q.1).proj go.1
                                congr 1
                                congr 1
                                rw [← mul_assoc, hproj]
                          _ = G * Mo go.2 * Gq go.1 * Mo go.2 * G := by
                                simp [mul_assoc]
      _ = ∑ g : Polynomial params,
            ∑ o : Outcome, leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o * G) := by
            simpa using
              (Fintype.sum_prod_type' (f := fun g o =>
                leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o * G)))
      _ = ∑ g : Polynomial params,
            leftTensor (ι₂ := ι) (∑ o : Outcome, G * Mo o * Gq g * Mo o * G) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
      _ = leftTensor (ι₂ := ι)
            (∑ g : Polynomial params, ∑ o : Outcome, G * Mo o * Gq g * Mo o * G) := by
            rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
      _ = leftTensor (ι₂ := ι) (∑ o : Outcome, G * Mo o * G * Mo o * G) := by
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro o _
            calc
              ∑ g : Polynomial params, G * Mo o * Gq g * Mo o * G
                = G * Mo o * (∑ g : Polynomial params, Gq g) * Mo o * G := by
                    simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
              _ = G * Mo o * G * Mo o * G := by
                    rw [(family.meas q.1).sum_eq_total]
                    simp [G]
      _ = leftTensor (ι₂ := ι) (G * (∑ o : Outcome, Mo o * G * Mo o) * G) := by
            congr 1
            simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
  have hmid_le : ∑ o : Outcome, Mo o * G * Mo o ≤ 1 := by
    simpa [G, Mo] using switcherooAggregateFourthTerm_middle_sum_le_one params family M q
  have hsandwich_le : G * (∑ o : Outcome, Mo o * G * Mo o) * G ≤ G := by
    calc
      G * (∑ o : Outcome, Mo o * G * Mo o) * G ≤ G * 1 * G := by
        exact IsSelfAdjoint.conjugate_le_conjugate hmid_le hGherm
      _ = G := by simp [hGsq]
  calc
    (∑ go : Polynomial params × Outcome,
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1)) *
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1))ᴴ)
      = leftTensor (ι₂ := ι) (G * (∑ o : Outcome, Mo o * G * Mo o) * G) := by
          simpa [G, Gq, Mo] using hsum
    _ ≤ leftTensor (ι₂ := ι) G := by
          simpa [leftTensor, opTensor] using
            (opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
              hsandwich_le (show (0 : MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one))
    _ ≤ 1 := by
          simpa [G] using leftTensor_le_one (ι₂ := ι)
            ((completePartSubMeas params family q.1).total_le_one)







end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: switcheroo split contraction

The split-form contraction and first mixed-term transfer.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Shared switcheroo contraction helper definitions -/

theorem solution
    {Outcome : Type*} [Fintype Outcome]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψbi : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (M : _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas (_root_.LIDT.MIPStarRE.LDT.Fq params) Outcome ι)
    (chi : _root_.LIDT.MIPStarRE.LDT.Error)
    (hcomm : _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψbi
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family M)
      (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight params family M)
      chi) :
    |_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M -
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
          ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1 *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1)))| ≤
      Real.sqrt chi := by
  let 𝒟q : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params) :=
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)
  let A : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go => (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft params family M q).outcome go
  let B : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params → _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go => (_root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight params family M q).outcome go
  let C : _root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params →
      _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome → Unit → _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go () =>
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
        ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
          (M q.2).outcome go.2 *
          (family.meas q.1).outcome go.1)
  have h𝒟q : ∑ q ∈ 𝒟q.support, 𝒟q.weight q ≤ 1 := by
    simpa [𝒟q] using _root_.LIDT.MIPStarRE.LDT.uniformDistribution_weight_sum_le_one (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)
  have hAB : _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDCore ψbi (A q) (B q)) ≤ chi := by
    simpa [𝒟q, A, B] using
      _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductCommutation_coreBound params ψbi family M chi hcomm
  have hC :
      ∀ q,
        (∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
            (∑ u : Unit, C q go u) * (∑ u : Unit, C q go u)ᴴ) ≤ 1 := by
    intro q
    simpa [C] using switcherooAggregateFourthTerm_split_contraction params family M q
  have hclose :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_left ψbi hnorm 𝒟q h𝒟q A B C chi hAB hC
  have hleft :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q (fun q =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (C q a () * A q a)) =
        _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M := by
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q (fun q =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (C q a () * A q a))
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
            ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
              _root_.LIDT.MIPStarRE.LDT.ev ψbi
                (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                  ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                    (M q.2).outcome go.2 *
                    (family.meas q.1).outcome go.1 *
                    (family.meas q.1).outcome go.1 *
                    (M q.2).outcome go.2))) := by
              simp [𝒟q, A, C, _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductLeft, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedProductOpFamily,
                _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc]
      _ = _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm params ψbi family M := by
            symm
            exact _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateFourthTerm_eq_split params ψbi family M
  have hright :
      _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟q (fun q =>
          ∑ a : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi (C q a () * B q a)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Pasting.SlicePairQuestion params)) (fun q =>
          ∑ go : _root_.LIDT.MIPStarRE.LDT.Polynomial params × Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψbi
              (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι)
                ((_root_.LIDT.MIPStarRE.LDT.Pasting.completePartSubMeas params family q.1).total *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1 *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1))) := by
    simp [𝒟q, B, C, _root_.LIDT.MIPStarRE.LDT.Pasting.switcherooPointProductRight, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.reversedProductOpFamily,
      _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, mul_assoc]
  simpa [hleft, hright] using hclose
