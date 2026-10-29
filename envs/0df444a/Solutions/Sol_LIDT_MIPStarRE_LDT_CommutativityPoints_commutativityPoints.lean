-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPoints
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:19:23.395177+00:00
-- url     : https://prove2.me/submissions/b6379a89-69fb-482c-ad46-003c58e0a7ff

-- Generated proof for MIPStarRE.LDT.CommutativityPoints.commutativityPoints.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_orderedLiftToLineProduct
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_orderedLiftToMixedLine
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_pointDiagonalLineMixedProductRight_outcome
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sampledDiagonalLineApproximation_ignore_first
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sampledDiagonalLineApproximation_ignore_second
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sddOpRel_congr_outcome
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sddOpRel_reindex
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_subMeas_sum_adjoint_mul_le_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_qSDDOp_symm

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Basic/PMFAverages.lean. -/
/-!
# PMF-weighted finite expectation identities

This module contains finite expectation identities stated directly for
Mathlib probability mass functions.  They connect `PMF.map` and
`PMF.bind` to the real-weighted finite sums used by the
low individual degree test averaging layer.

## Main declarations

* `PMF.map_apply_toReal`
* `PMF.realWeightedSum`
* `PMF.realWeightedSumLinearMap`
* `PMF.realWeightedSum_map`
* `PMF.realWeightedSum_bind`
* `PMF.map_sum_smul`
* `PMF.bind_apply_toReal`
* `PMF.bind_sum_smul`
* `PMF.sum_toReal_eq_one`
* `PMF.sum_const_smul`
* `PMF.totalVariationDistance`
* `PMF.totalVariationDistance_eq_sum_max_sub`
* `PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq`
* `PMF.sum_le_sum_add_totalVariationDistance`
* `PMF.sum_rpow_one_div_le_rpow_sum`
* `PMF.realWeightedSum_rpow_one_div_le_rpow`
* `PMF.uniformOfFintype_map_equiv`
* `PMF.uniformOfFintype_prod_apply_toReal`
* `PMF.uniformOfFintype_prod_eq_bind`
* `PMF.uniformOfFintype_sum_equiv_smul`
* `PMF.uniformOfFintype_prod_sum_smul`
* `PMF.uniformOfFintype_sum_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_equiv_snd_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_snd_smul`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators

namespace PMF









end PMF

namespace PMF































/-- A uniform PMF-weighted sum pushed forward through a map has the first
coordinate uniform marginal when the seed is equivalent to a product. -/
theorem uniformOfFintype_sum_factor_equiv_fst_smul {α β γ δ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a)) =
      ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a))
        = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (e a).1 := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [h a]
    _ = ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
          exact uniformOfFintype_sum_equiv_fst_smul (e := e) (f := f)



end PMF

namespace PMF













/-- A uniform finite expectation pushed forward through a map has the first
coordinate uniform marginal when the seed is equivalent to a product. -/
theorem realWeightedSum_uniformOfFintype_factor_equiv_fst {α β γ δ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → M) :
    realWeightedSum (PMF.uniformOfFintype α) (fun a => f (g (m a))) =
      realWeightedSum (PMF.uniformOfFintype γ) f := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_factor_equiv_fst_smul
      (m := m) (g := g) (e := e) (h := h) (f := f)











end PMF

end

/- Source helpers from MIPStarRE/LDT/Basic/SubMeasurementCore.lean. -/
/-!
# Core submeasurement structures for the low individual degree test

Foundational measurement, submeasurement, and projective-measurement structures.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

















/-! ### Derived properties -/















































/-- Any two outcomes of a ProjMeas commute. -/
theorem ProjMeas.outcome_commute {α : Type*}
    {ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι]
    (P : ProjMeas α ι) (a b : α) :
    P.outcome a * P.outcome b =
      P.outcome b * P.outcome a := by
  classical
  by_cases hab : a = b
  · subst hab; rfl
  · rw [P.outcome_orthogonal a b hab,
        P.outcome_orthogonal b a (Ne.symm hab)]


end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/CommutativityPoints/SharedHelpers/Core.lean. -/
/-!
# Section 10 commutativity points: shared helpers core

Shared reindexing and tensor-placement helpers used by the Section 10
commutativity-of-points argument.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators
/-! ## Shared reindexing and tensor-placement helpers -/

lemma sddOpRel_symm
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddErrorOp, MIPStarRE.LDT.Preliminaries.qSDDOp_symm] using h









/-- Multiplying a left lift with a left-placed family stays on the left tensor factor. -/
lemma liftLeft_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftLeft).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      leftTensor (A.outcome a * B.outcome b) := by
  calc
    (A.liftLeft).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b
      = leftTensor (A.outcome a) * leftTensor (B.outcome b) := by
          rfl
    _ = leftTensor (A.outcome a * B.outcome b) := by
          rw [leftTensor_mul_leftTensor]

/-- Multiplying a left lift with a right-placed family gives the tensor product. -/
lemma liftLeft_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftLeft).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (A.outcome a) (B.outcome b) := by
  calc
    (A.liftLeft).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b
      = leftTensor (A.outcome a) * rightTensor (B.outcome b) := by
          rfl
    _ = opTensor (A.outcome a) (B.outcome b) := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]

/-- Multiplying a right lift with a left-placed family gives the tensor product. -/
lemma liftRight_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (B.outcome b) (A.outcome a) := by
  calc
    (A.liftRight).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b
      = rightTensor (A.outcome a) * leftTensor (B.outcome b) := by
          rfl
    _ = opTensor (B.outcome b) (A.outcome a) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor]

/-- Multiplying a right lift with a right-placed family stays on the right tensor factor. -/
lemma liftRight_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      rightTensor (A.outcome a * B.outcome b) := by
  calc
    (A.liftRight).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b
      = rightTensor (A.outcome a) * rightTensor (B.outcome b) := by
          rfl
    _ = rightTensor (A.outcome a * B.outcome b) := by
          rw [rightTensor_mul_rightTensor]

end MIPStarRE.LDT.CommutativityPoints

end

/- Source helpers from MIPStarRE/LDT/Basic/DistributionUniformSums.lean. -/
/-!
# Module-valued uniform finite sums for project distributions

This module contains the module-valued finite-sum algebra for the project
`Distribution` type.  The statements keep the paper-facing
`uniformDistribution` notation, but their proofs reduce the probability
calculation to the finite-expectation API for Mathlib probability mass
functions.

## Main declarations

* `Distribution.sum_smul_eq_toPMF_support_sum`
* `Distribution.sum_smul_eq_toPMF_sum`
* `uniformDistribution_sum_smul_eq_pmf_sum`
* `uniformDistribution_sum_smul_equiv`
* `uniformDistribution_sum_smul_prod`
* `uniformDistribution_sum_smul_comm`
* `uniformDistribution_sum_smul_prod_swap`
* `uniformDistribution_sum_smul_equiv_prod`
* `uniformDistribution_sum_smul_equiv_fst`
* `uniformDistribution_sum_smul_equiv_snd`
* `uniformDistribution_map_sum_smul_eq_uniform_of_factor_equiv`
* `uniformOnFinset_sum_smul_eq_subtype`
* `uniformOnFinset_filter_sum_smul_equiv`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Distribution





end Distribution

























/-- A uniformly sampled seed has the first-coordinate uniform module-valued
marginal when the observed coordinate factors through a product equivalence. -/
theorem uniformDistribution_sum_smul_factor_equiv_fst {α β γ δ M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → M) :
    ∑ a ∈ (uniformDistribution α).support,
        (uniformDistribution α).weight a • f (g (m a)) =
      ∑ c ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight c • f c := by
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := γ)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_factor_equiv_fst
      (m := m) (g := g) (e := e) (h := h) (f := f)





/-- A uniform push-forward has the first-coordinate uniform module-valued
marginal when the observed coordinate factors through a product equivalence. -/
theorem uniformDistribution_map_sum_smul_eq_uniform_fst_of_factor_equiv
    {α β γ δ M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → M) :
    ∑ b ∈ ((uniformDistribution α).map m).support,
        ((uniformDistribution α).map m).weight b • f (g b) =
      ∑ c ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight c • f c := by
  rw [Distribution.map_sum_smul]
  exact uniformDistribution_sum_smul_factor_equiv_fst
    (m := m) (g := g) (e := e) (h := h) (f := f)











end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean. -/
/-!
# Indexed and bipartite submeasurement infrastructure

Indexed measurement families, tensor placements, and lift/placement constructors.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Indexed measurement families -/









namespace IdxMeas



end IdxMeas

namespace IdxProjSubMeas



end IdxProjSubMeas

namespace IdxProjMeas





end IdxProjMeas



namespace SubMeas

















end SubMeas

namespace Measurement



end Measurement

namespace ProjSubMeas





end ProjSubMeas

namespace ProjMeas











end ProjMeas

/-- Postprocessed outcomes from the same ProjMeas commute. -/
theorem ProjMeas.postprocess_outcome_commute
    {α β γ : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ι] [DecidableEq ι]
    (P : ProjMeas α ι) (f : α → β) (g : α → γ)
    (b : β) (c : γ) :
    (MIPStarRE.LDT.postprocess P.toSubMeas f).outcome b *
      (MIPStarRE.LDT.postprocess P.toSubMeas g).outcome c =
    (MIPStarRE.LDT.postprocess P.toSubMeas g).outcome c *
      (MIPStarRE.LDT.postprocess P.toSubMeas f).outcome b := by
  classical
  simp only [MIPStarRE.LDT.postprocess]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  exact P.outcome_commute y x








/-! ### Tensor-placement constructors -/













/-! ### Square bipartite lifts -/











/-! ### General bipartite placement -/

















end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Basic/DistributionMapAverages.lean. -/
/-!
# Uniform push-forward averaging lemmas

This file contains shared averaging lemmas for uniformly sampled finite seeds
that are pushed forward to a question distribution.  The main use case is a
random seed `a : α`, a pushed-forward value `m a : β`, and an observed
coordinate `g (m a)` which is identified with a uniform coordinate by an
equivalence.

## Main declarations

* `avgOver_uniform_map_eq_uniform_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_of_factor_equiv`
* `avgOver_uniform_map_eq_uniform_fst_of_factor_equiv`
* `avgOver_uniform_map_eq_uniform_snd_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_fst_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_snd_of_factor_equiv`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Project-distribution map averages -/





/-- A uniform push-forward has the first-coordinate uniform marginal when the
observed coordinate factors through a product equivalence of the seed. -/
theorem avgOver_uniform_map_eq_uniform_fst_of_factor_equiv
    {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Finite δ] [Nonempty δ]
    (m : α → β) (g : β → γ) (e : α ≃ γ × δ)
    (h : ∀ a, g (m a) = (e a).1) (f : γ → Error) :
    avgOver ((uniformDistribution α).map m) (fun b => f (g b)) =
      avgOver (uniformDistribution γ) f := by
  simpa [avgOver, smul_eq_mul] using
    uniformDistribution_map_sum_smul_eq_uniform_fst_of_factor_equiv
      (m := m) (g := g) (e := e) (h := h) (f := f)







end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean. -/
/-!
# Section 10 commutativity points: shared-line helpers

Compatibility lemmas between sampled point pairs and shared-diagonal line
questions, used by both the lift and drop comparisons.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators












lemma avgOver_pointPairSharedDiagonalLine_sampled_pair
    (params : Parameters)
    [FieldModel params.q]
    (f : PointPairQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params)
      (fun q => f (sampledPointPairFromSharedDiagonalQuestion params q)) =
      avgOver (uniformDistribution (PointPairQuestion params)) f := by
  simpa [pointPairSharedDiagonalLineDistribution] using
    (avgOver_uniform_map_eq_uniform_fst_of_factor_equiv
      (m := sharedDiagonalLineQuestionOfPointPair params)
      (g := sampledPointPairFromSharedDiagonalQuestion params)
      (e := Equiv.refl (PointPairQuestion params × Fq params))
      (h := sharedDiagonalLineQuestionOfPointPair_sampledPointPair params)
      (f := f))



lemma pointMeasurementProductAlongSharedLineReversed_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (pointMeasurementProductAlongSharedLineReversed params strategy q).outcome (a, b) =
      leftTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b *
          (strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a) := by
  simp [pointMeasurementProductAlongSharedLineReversed, pointMeasurementProductRight,
    reversedProductOpFamily, sampledPointPairFromSharedDiagonalQuestion,
    OpFamily.leftPlacedOpFamily]







lemma diagonalLineProductReversed_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (diagonalLineProductReversed params strategy q).outcome (a, b) =
      rightTensor
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a *
          (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
  simp [diagonalLineProductReversed, sampledDiagonalLineEvaluation,
    OpFamily.rightPlacedOpFamily, orderedProductOpFamily]





end MIPStarRE.LDT.CommutativityPoints

end

/- Source helpers from MIPStarRE/LDT/CommutativityPoints/BridgeTheorems/DropBridges.lean. -/
/-!
# Section 10 commutativity points: drop comparisons

Comparison lemmas that drop structure from the mixed line family back to the
ordered diagonal-line product, used in the drop direction of the Section 10
point-commutativity argument.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators

private lemma reversedDropFromLineComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductReversed params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Third replacement step:
  `I ⊗ (L^ℓ_[f(u)=a] L^ℓ_[f(v)=b]) ≈ A^v_b ⊗ L^ℓ_[f(u)=a]`.
  -/
  let e := pointPairOutcomeSwapEquiv params
  let Araw :
      IdxOpFamily (PointPairDiagonalLineQuestion params)
        (Fq params × Fq params) (ι × ι) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Lu.liftRight).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily (ιA := ι) Lv.toOpFamily).outcome ab.1
  let Braw :
      IdxOpFamily (PointPairDiagonalLineQuestion params)
        (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Lu.liftRight).outcome ab.2 *
          (OpFamily.leftPlacedOpFamily (ιB := ι) Av).outcome ab.1
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (pointDiagonalLineApproxError params gamma)
      (sampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood)
  let hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily
            (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q _b a =>
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight).outcome a)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q b
        exact subMeas_sum_adjoint_mul_le_one
          ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight))
  have hreindexed :=
    sddOpRel_reindex e strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      Araw
      Braw
      (pointDiagonalLineApproxError params gamma)
      hcab
  let Astep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Araw q).outcome (e.symm ab)
         total := (Araw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
  let Bstep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Braw q).outcome (e.symm ab)
         total := (Braw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (diagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = rightTensor
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a *
                (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Astep, Araw, e, opFamilyOfOutcome,
                    pointPairOutcomeSwapEquiv] using
                    liftRight_mul_rightPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      a b
        _ = (diagonalLineProductReversed params strategy q).outcome (a, b) := by
              symm
              exact diagonalLineProductReversed_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Bstep, Braw, e, opFamilyOfOutcome,
                    pointPairOutcomeSwapEquiv] using
                    liftRight_mul_leftPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      a b
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductRight params strategy)) q).outcome (a, b) := by
              symm
              exact pointDiagonalLineMixedProductRight_outcome params strategy q a b)
    hreindexed

private lemma orderedDropFromLineComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    (diagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (diagonalLineProductOrdered params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ⟨a, b⟩
      symm
      simp only [diagonalLineProductOrdered, diagonalLineProductReversed,
        OpFamily.rightPlacedOpFamily, reversedProductOpFamily, orderedProductOpFamily,
        sampledDiagonalLineEvaluation]
      congr 1
      exact (strategy.diagonalMeasurement q.1).postprocess_outcome_commute
        (fun f => f q.2.2) (fun f => f q.2.1) b a)
    (by intro q ab; rfl)
    (reversedDropFromLineComparison params strategy eps delta gamma hgood)

private lemma reversedDropToPointsComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Final replacement step:
  `A^v_b ⊗ L^ℓ_[f(u)=a] ≈ (A^v_b A^u_a) ⊗ I`.
  -/
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      ({ outcome := fun ab : Fq params × Fq params =>
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι) (SubMeas.toOpFamily Lu)).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι) (SubMeas.toOpFamily Lu)).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      ({ outcome := fun ab : Fq params × Fq params =>
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma)
      (sampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood)
  have hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q _a b =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointMeasurementProductAlongSharedLineReversed params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Astep] using
                    liftLeft_mul_rightPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductRight params strategy)) q).outcome (a, b) := by
              symm
              exact pointDiagonalLineMixedProductRight_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = leftTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b *
                (strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a) := by
                  simpa [Bstep] using
                    liftLeft_mul_leftPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      b a
        _ = (pointMeasurementProductAlongSharedLineReversed params strategy q).outcome (a, b) := by
              symm
              exact pointMeasurementProductAlongSharedLineReversed_outcome params strategy q a b)
    hcab



end MIPStarRE.LDT.CommutativityPoints

end

end LIDT

open LIDT
/-!
# Section 10 commutativity points: drop comparisons

Comparison lemmas that drop structure from the mixed line family back to the
ordered diagonal-line product, used in the drop direction of the Section 10
point-commutativity argument.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params ι)
    (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.GlobalVariance.PointPairQuestion params))
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductLeft params strategy)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductRight params strategy)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params gamma) := by
  let δ := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma
  have hleft :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLine params strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.diagonalLineProductOrdered params strategy)
        (2 * (δ + δ)) := by
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLine params strategy)
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.toIdxOpFamily (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductLeft params strategy))
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.diagonalLineProductOrdered params strategy)
      δ δ
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedLiftToMixedLine params strategy eps delta gamma hgood)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.orderedLiftToLineProduct params strategy eps delta gamma hgood)
  have hright :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.diagonalLineProductOrdered params strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (δ + δ)) := by
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.diagonalLineProductOrdered params strategy)
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.toIdxOpFamily (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductRight params strategy))
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLineReversed params strategy)
      δ δ
      (orderedDropFromLineComparison params strategy eps delta gamma hgood)
      (reversedDropToPointsComparison params strategy eps delta gamma hgood)
  have hshared :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLine params strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (2 * (δ + δ) + 2 * (δ + δ))) := by
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLine params strategy)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.diagonalLineProductOrdered params strategy)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLineReversed params strategy)
      (2 * (δ + δ)) (2 * (δ + δ))
      hleft hright
  have hshared' :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLine params strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLineReversed params strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params gamma) := by
    refine _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono
      strategy.state
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLine params strategy)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLineReversed params strategy)
      (2 * (2 * (δ + δ) + 2 * (δ + δ)))
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params gamma)
      ?_ hshared
    dsimp [δ, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.restrictedDiagonalLinesConsistencyError,
      _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError]
    ring_nf
    linarith
  rcases hshared' with ⟨hshared'⟩
  constructor
  calc
    _root_.LIDT.MIPStarRE.LDT.sddErrorOp strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.GlobalVariance.PointPairQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductLeft params strategy)
        (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductRight params strategy)
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            _root_.LIDT.MIPStarRE.LDT.qSDDOp strategy.state
              (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLine params strategy q)
              (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLineReversed params strategy q)) := by
            symm
            simpa [_root_.LIDT.MIPStarRE.LDT.sddErrorOp, _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLine,
              _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLineReversed] using
              _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.avgOver_pointPairSharedDiagonalLine_sampled_pair params
                (fun uv =>
                  _root_.LIDT.MIPStarRE.LDT.qSDDOp strategy.state
                    (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductLeft params strategy uv)
                    (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductRight params strategy uv))
    _ = _root_.LIDT.MIPStarRE.LDT.sddErrorOp strategy.state
          (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
          (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLine params strategy)
          (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointMeasurementProductAlongSharedLineReversed params strategy) := by
            rfl
    _ ≤ _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.commutativityPointsError params gamma := hshared'
