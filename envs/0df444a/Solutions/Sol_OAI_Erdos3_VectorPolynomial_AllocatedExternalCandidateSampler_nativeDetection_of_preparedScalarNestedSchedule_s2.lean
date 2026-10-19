-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_preparedScalarNestedSchedule_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:29:07.956991+00:00
-- url     : https://prove2.me/submissions/c6ec7fd1-4cb8-43b6-8082-ff31018b98bd

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateSampler_nativeDetection_of_emptyLayer_sampler_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteScheduleGeometryPrescribedScale_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedEmptyLayerFiniteScheduleCandidateDetection_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedFiniteScheduleGeometryDirectSource_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EmptyCoefficientDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators

theorem canonicalMixedDensity_empty
    {D I : Type*} [Fintype D] [Fintype I] [IsEmpty D] [IsEmpty I]
    {n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W)
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → ℝ) (p : Fin n → PMF ℤ)
    (y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :
    canonicalMixedDensity W b hb o c w p y = 1 := by
  let Q := W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let : Subsingleton Q := ⟨by
    intro x y
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact congrArg QuotientAddGroup.mk (Subsingleton.elim x y)⟩
  let μ : Measure Q := probabilityAddHaar Q
  let : IsProbabilityMeasure μ := probabilityAddHaar_probability Q
  let : μ.IsAddLeftInvariant := probabilityAddHaar_invariant Q
  have hmass := (canonicalMixedDensity_mass W b hb o μ c w
    (fun i => isEmptyElim i) p (fun _ _ i => isEmptyElim i)).2
  have hconst : canonicalMixedDensity W b hb o c w p =
      fun _ => canonicalMixedDensity W b hb o c w p y := by
    funext z
    exact congrArg (canonicalMixedDensity W b hb o c w p) (Subsingleton.elim z y)
  rw [hconst] at hmass
  simpa using hmass

namespace VectorPolynomial

theorem canonicalCoefficientDensity_empty
    {K : Type*} [Fintype K] {m : ℕ}
    {J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
    [∀ j, IsEmpty (J j)] [∀ j, IsEmpty (I j)]
    {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (y : CoefficientTorus (K := K) U) :
    canonicalCoefficientDensity U b hb o c w p y = 1 := by
  unfold canonicalCoefficientDensity
  apply Finset.prod_eq_one
  intro j _
  unfold canonicalArrayDensity
  apply Finset.prod_eq_one
  intro e _
  exact canonicalMixedDensity_empty _ (b j) (hb j) (o j) _ _ _ _

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeCoverMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem latticeQuotient_compact : CompactSpace (E ⧸ Λ.toAddSubgroup) := by
  have hc := IsZLattice.isCompact_range_of_periodic Λ
    (QuotientAddGroup.mk' Λ.toAddSubgroup) QuotientAddGroup.continuous_mk (by
      intro x z hz
      have hz0 : QuotientAddGroup.mk' Λ.toAddSubgroup z = 0 :=
        (QuotientAddGroup.eq_zero_iff z).mpr hz
      rw [map_add, hz0, add_zero])
  rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective _)] at hc
  exact ⟨hc⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem smoothSpatialDisplacementCost_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) :
    0 ≤ smoothSpatialDisplacementCost N s M := by
  unfold smoothSpatialDisplacementCost spatialKernelErrorConstant
    scalarSpatialIndexAllowance scalarSpatialInverseAllowance
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem spatialKernelErrorConstant_le_exp (j e : ℕ) {U P : ℝ} (K : ℝ≥0)
    (hU0 : 0 ≤ U) (hU : U ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp P) :
    spatialKernelErrorConstant j e U 1 K ≤
      Real.exp ((j : ℝ)^2+(j+2)*P+2*e) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold spatialKernelErrorConstant
  norm_num only [mul_one]
  calc
    _ ≤ (Real.exp ((j : ℝ)^2)*(Real.exp P)^j)*(Real.exp 2)^e*Real.exp P*Real.exp P := by
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem smoothSpatialDisplacementCost_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    smoothSpatialDisplacementCost N s M ≤
      Real.exp (spatialDisplacementLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) (Fintype.card (UnselectedColumn s))
        (Fintype.card N) p) := by
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let e := Fintype.card (UnselectedColumn s)
  let P := spatialProfileLog j d p
  obtain ⟨hG, hU, _, hK⟩ := spatialProfileLog_bounds N s hp hM
  have he : (e : ℝ) ≤ d := by
    simp only [d, e, Fintype.card_sum, Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hsmall : ((e+j : ℝ)*probabilityProfileLipschitz) ≤ Real.exp P := by
    apply le_trans _ hK
    gcongr
  have hc := spatialKernelErrorConstant_le_exp j e ((e+j)*probabilityProfileLipschitz)
    (by unfold scalarSpatialInverseAllowance; positivity) hU
    (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast] using hsmall)
  have hn : (Fintype.card N : ℝ) ≤ Real.exp (Fintype.card N : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card N : ℝ)]
  unfold smoothSpatialDisplacementCost
  calc
    _ ≤ Real.exp P * Real.exp ((j : ℝ)^2+(j+2)*P+2*e) * Real.exp (Fintype.card N : ℝ) := by
      apply mul_le_mul _ hn (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul hG hc (by unfold spatialKernelErrorConstant scalarSpatialInverseAllowance; positivity)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [spatialDisplacementLog, P]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, IsEmpty (I j)]
variable {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem emptyLayerSamplerVariables_card :
    Fintype.card (LayerSamplerVariables G I n B) = Fintype.card G := by
  simp only [LayerSamplerVariables, SamplerTupleIndex, Fintype.card_sum]
  have hzero : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) = 0 := by
    let : IsEmpty (PrincipalTupleIndex B (layerSamplerDegree I n)) :=
      ⟨fun a => a.1.2.elim isEmptyElim isEmptyElim⟩
    exact Fintype.card_eq_zero
  rw [hzero, Nat.add_zero]

theorem emptyLayerCoefficientCount_le (j : Fin m) :
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      (j.val + 1)) : ℝ) ≤ allocatedComparisonDimension m (Fintype.card G : ℝ) := by
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      (Fintype.card G : ℝ) := by rw [emptyLayerSamplerVariables_card B]
  exact (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
    (Nat.succ_le_of_lt j.isLt) (Nat.cast_nonneg _) hvars).trans
    (allocatedComparisonDimension_bounds m (Nat.cast_nonneg (Fintype.card G))).2.2.2.2.1

theorem emptyLayerCoefficientCount_le_exp (j : Fin m) :
    4 * ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      (j.val + 1)) : ℝ) + 1) ≤
        Real.exp (allocatedComparisonDimension m (Fintype.card G : ℝ) + 4) := by
  have hcount := emptyLayerCoefficientCount_le (G := G) B j
  have hcountExp : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      (j.val + 1)) : ℝ) + 1 ≤
        Real.exp (allocatedComparisonDimension m (Fintype.card G : ℝ)) := by
    linarith [Real.add_one_le_exp (allocatedComparisonDimension m (Fintype.card G : ℝ))]
  calc
    _ ≤ 4 * Real.exp (allocatedComparisonDimension m (Fintype.card G : ℝ)) := by
      gcongr
    _ ≤ Real.exp 4 * Real.exp (allocatedComparisonDimension m (Fintype.card G : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (4 : ℝ)])
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UnconditionedWidthExponentialBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators

private theorem widthBudget_le_exp (x : ℝ) : x ≤ Real.exp x :=
  (by linarith : x ≤ x + 1).trans (Real.add_one_le_exp x)

theorem unconditionedSpatialTrimFraction_inv_exp_bound {p : ℝ} {d : ℕ}
    (hd : (d : ℝ) ≤ p) :
    (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ ≤ Real.exp (2 * p + 33) := by
  have h32 : (32 : ℝ) ≤ Real.exp 32 := widthBudget_le_exp _
  have hdexp : (d : ℝ) + 1 ≤ Real.exp (p + 1) :=
    (by linarith : (d : ℝ) + 1 ≤ p + 1).trans (widthBudget_le_exp _)
  calc
    (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ =
        32 * ((d : ℝ) + 1) * Real.exp p := by
      simp [unconditionedSpatialTrimFraction, Real.exp_neg]
    _ ≤ Real.exp 32 * Real.exp (p + 1) * Real.exp p := by gcongr
    _ = Real.exp (2 * p + 33) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

theorem normalizedTupleNarrowWidth_pos (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ) (p E : ℝ) :
    0 < normalizedTupleNarrowWidth X N s M p E := by
  have ht : 0 < normalizedTupleTolerance X p E := (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _)
    (Real.exp_nonneg _) (half_pos (Real.exp_pos (-(E + 2))))).1
  exact (twoTermErrorWidth_spec (smoothSpatialDisplacementCost_nonneg N s M) ht).1

end Erdos3

end

section

namespace Erdos3

theorem spatialPrimitiveEnvelope_bounds {p E l : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) :
    let R := spatialPrimitiveEnvelope p E l
    0 ≤ R ∧ p ≤ R ∧ E + 3 ≤ R ∧ p ^ 3 + anisotropicSpatialCapLog p ≤ R ∧
      coefficientErrorVolumeLog p + 4 ≤ R ∧ spatialDisplacementEnvelope p ≤ R ∧
      spatialDiscretizationEnvelope p l ≤ R ∧ spatialLipschitzCostEnvelope p l ≤ R ∧
      spatialThresholdEnvelope p l ≤ R ∧ spatialBoundaryEnvelope p l ≤ R ∧
      spatialMovementEnvelope p l ≤ R := by
  obtain ⟨_, hd, ha, hm, hk⟩ := spatialCostEnvelopes_nonneg hp hl
  have hcap : 0 ≤ p ^ 3 + anisotropicSpatialCapLog p := by
    have := anisotropicSpatialCapLog_nonneg hp
    positivity
  have hvol : 0 ≤ coefficientErrorVolumeLog p + 4 := by
    unfold coefficientErrorVolumeLog
    positivity
  have hK : 0 ≤ spatialLipschitzCostEnvelope p l := by
    unfold spatialLipschitzCostEnvelope
    positivity
  have hT : 0 ≤ spatialThresholdEnvelope p l := by
    unfold spatialThresholdEnvelope
    positivity
  have hQ : 0 ≤ spatialBoundaryEnvelope p l := by
    unfold spatialBoundaryEnvelope
    positivity
  have hD : 0 ≤ spatialMovementEnvelope p l := by
    unfold spatialMovementEnvelope
    positivity
  dsimp only [spatialPrimitiveEnvelope]
  repeat' constructor
  all_goals linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTupleParameterBounds
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem normalizedSpatialShare_half_inv_le (E : ℝ) :
    (normalizedSpatialShare E / 2)⁻¹ ≤ Real.exp (E + 3) := by
  unfold normalizedSpatialShare
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  calc
    _ ≤ Real.exp 1 * Real.exp (E + 2) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem normalizedTupleEarlyParameters_bound {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q M : ℕ} (s : Fin q ↪ G)
    {p E l : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hMp : (M : ℝ) ≤ Real.exp p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) :
    let R := spatialPrimitiveEnvelope p E l
    (normalizedTupleTolerance X p E)⁻¹ ≤ Real.exp (spatialTupleToleranceLog R) ∧
      (normalizedTupleNarrowWidth X N s M p E)⁻¹ ≤
        Real.exp (2 * (R + spatialTupleToleranceLog R) + 4) := by
  obtain ⟨hR, hpR, hER, hcapR, hvolR, hdispR, _⟩ :=
    spatialPrimitiveEnvelope_bounds hp hE hl
  obtain ⟨he, hd, _⟩ := spatialAuxiliaryDimensions (N := N) s hG hN
  have hI : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hB := (smoothSpatialDisplacementCost_le_exp N s hp hMp).trans
    (Real.exp_le_exp.mpr ((spatialDisplacementLog_le_envelope _ _ _ _ hp hI hd he hN).trans hdispR))
  have hε : 0 < normalizedSpatialShare E / 2 := half_pos (Real.exp_pos _)
  have hεR := (normalizedSpatialShare_half_inv_le E).trans (Real.exp_le_exp.mpr hER)
  exact ⟨spatialTupleTolerance_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
    hε hR (hX.trans hpR) (Real.exp_le_exp.mpr hcapR) (Real.exp_le_exp.mpr hvolR) hεR,
    spatialTupleEarlyWidth_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
      (smoothSpatialDisplacementCost_nonneg N s M) hε hR (hX.trans hpR)
      (Real.exp_le_exp.mpr hcapR) (Real.exp_le_exp.mpr hvolR) hB hεR⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3

theorem fixedCenterForecast_source_threshold
    {u p sourceU sourceModel : ℝ}
    (hsource : u + 2 * p + 1 ≤ sourceU) (hmodel : 0 ≤ sourceModel) :
    Real.exp (-(2 * sourceU + 4 * sourceModel + 7)) ≤
      Real.exp (-(2 * u + 4 * p + 8)) / 2 := by
  calc
    _ ≤ Real.exp (-(2 * u + 4 * p + 9)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp 1 := by
      rw [← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
      (by linarith [Real.add_one_le_exp (1 : ℝ)])

theorem fixedCenterForecast_source_threshold_half_le_one
    {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    Real.exp (-(2 * u + 4 * p + 8)) / 2 ≤ 1 := by
  have h := Real.exp_le_one_iff.mpr (show -(2 * u + 4 * p + 8) ≤ 0 by linarith)
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

variable {Slot : Type*} [Fintype Slot]
variable (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
variable (x anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ)

theorem detectorRequired_le_preparedFiniteNestedSourceRequired (slot : Slot) :
    detectorRequired slot ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired := by
  unfold preparedFiniteNestedSourceRequired
  have hdet : max 0 (detectorRequired slot) ≤ ∑ slot, max 0 (detectorRequired slot) :=
    Finset.single_le_sum (fun _ _ => le_max_left _ _) (Finset.mem_univ slot)
  have hcum : 0 ≤ ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  linarith [le_max_left (0 : ℝ) anchorGoodRequired,
    le_max_left (0 : ℝ) conditionalRequired, le_max_right (0 : ℝ) (detectorRequired slot)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardPairedSourcePrecision_model_lower
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
        2 * preparedFiniteForwardWork A stageCountConstant n x + 1 ≤
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n isDirect
        x gainLog stageLog := by
  change preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog ≤ _
  have hsource := (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).2.1
  have hwork := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  cases isDirect with
  | false => simp only [preparedFiniteForwardPairedSourcePrecision_model, le_refl]
  | true =>
    rw [preparedFiniteForwardPairedSourcePrecision_direct]
    exact le_add_of_nonneg_right
      (pow_nonneg (add_nonneg (add_nonneg hsource hwork) (Nat.cast_nonneg Cdirect)) Cdirect)

theorem preparedFiniteForwardFixedCenterThreshold_lower
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    Real.exp (-(2 * preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n
        isDirect x gainLog stageLog + 4 * preparedFiniteForwardWork A stageCountConstant n x + 7)) ≤
      Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 8)) / 2 :=
  fixedCenterForecast_source_threshold
    (preparedFiniteForwardPairedSourcePrecision_model_lower A Cdirect stageCountConstant n isDirect
      hx hg hs)
    (preparedFiniteForwardWork_nonneg A stageCountConstant n hx)

theorem preparedFiniteForwardFixedCenterThreshold_half_le_one
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
      4 * preparedFiniteForwardWork A stageCountConstant n x + 8)) / 2 ≤ 1 :=
  fixedCenterForecast_source_threshold_half_le_one
    (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).1
    (preparedFiniteForwardWork_nonneg A stageCountConstant n hx)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ b, Fintype (B b)]

theorem preparedModularDetector_narrow_width {q Mk nX : ℕ} (selection : Fin q ↪ G)
    {Pphysical coarseTarget : ℝ} (hp : 0 ≤ Pphysical) (htarget : 0 ≤ coarseTarget)
    (hMk : (Mk : ℝ) ≤ Real.exp Pphysical) (hq : ((q + 1 : ℕ) : ℝ) ≤ Pphysical)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical)
    (hnX : (nX : ℝ) ≤ Pphysical) :
    let R := spatialPrimitiveEnvelope Pphysical coarseTarget 0
    let ξLog := 2 * (R + spatialTupleToleranceLog R) + 4
    0 ≤ ξLog ∧
      (normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n))
        selection Mk Pphysical coarseTarget)⁻¹ ≤ Real.exp ξLog := by
  intro R ξLog
  have hG := (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  have hN := (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvars
  have hX : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical := by simpa only [Fintype.card_fin] using hnX
  have hR : 0 ≤ R := (spatialPrimitiveEnvelope_bounds hp htarget (le_refl 0)).1
  have ht := spatialTupleToleranceLog_nonneg hR
  refine ⟨by dsimp only [ξLog]; positivity, ?_⟩
  exact (normalizedTupleEarlyParameters_bound
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := Fin nX)
    selection hp htarget (le_refl 0) hMk hq hG hN hX).2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedWidthPreparedChoice
namespace OAI

section

namespace Erdos3

theorem sharedWidthPreparedChoice {T : Type*} (width : T → ℝ) (Plate : ℝ)
    (hpositive : ∀ t, 0 < width t)
    (hreciprocal : ∀ t, (width t)⁻¹ ≤ Real.exp Plate) :
    let ξ := Real.exp (-Plate)
    0 < ξ ∧ ξ⁻¹ = Real.exp Plate ∧ ∀ t, ξ ≤ width t := by
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · simp only [Real.exp_neg, inv_inv]
  · intro t
    have h := (inv_le_inv₀ (Real.exp_pos Plate) (inv_pos.mpr (hpositive t))).2
      (hreciprocal t)
    simpa only [Real.exp_neg, inv_inv] using h

theorem sharedWidthNormalizedTuplePreparedChoice {T G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X]
    (q M : T → ℕ) (selection : ∀ t, Fin (q t) ↪ G) (p E : T → ℝ) (Plate : ℝ)
    (hreciprocal : ∀ t,
      (normalizedTupleNarrowWidth X N (selection t) (M t) (p t) (E t))⁻¹ ≤
        Real.exp Plate) :
    let ξ := Real.exp (-Plate)
    0 < ξ ∧ ξ⁻¹ = Real.exp Plate ∧ ∀ t,
      ξ ≤ normalizedTupleNarrowWidth X N (selection t) (M t) (p t) (E t) := by
  exact sharedWidthPreparedChoice
    (fun t => normalizedTupleNarrowWidth X N (selection t) (M t) (p t) (E t)) Plate
    (fun t => normalizedTupleNarrowWidth_pos X N (selection t) (M t) (p t) (E t))
    hreciprocal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem preparedUniformDegreeDirectLate_extra
    (Pmaster Pscale Pphysical coarseTarget extraLate : ℝ) :
    extraLate ≤ preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget extraLate :=
  (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleCandidateDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ} (selection : Fin (s + 1) ↪ G) (Pdetect : Polynomial ℕ)

theorem preparedFiniteScheduleDirectWidth_inv
    (Cdetect : ℕ)
    (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant s Pdetect)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice α : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel) pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hα : Real.exp (-(2 * sourceU + 4 * pModel + 7)) ≤ α) :
    (normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog sourceU pModel) (allocatedModelTestLog sourceU pModel) α)
      Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate := by
  rw [hCdetect] at scalar geometryAt
  have hMk := (geometryAt.2 α hα).2.1
  have hCoarse : 0 ≤ coarseTarget := by
    linarith only [scalar.gain_master.1, scalar.coarse_lower]
  have hwidth := preparedModularDetector_narrow_width B selection scalar.physical_master.1
    hCoarse (hMk.trans (Real.exp_le_exp.mpr scalar.kernel_physical))
    scalar.detector_physical scalar.variables_physical scalar.ambient_physical
  exact hwidth.2.trans (Real.exp_le_exp.mpr scalar.xi_late)

theorem preparedFiniteScheduleDirectWidth
    (Cdetect : ℕ)
    (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant s Pdetect)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice α : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel) pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hα : Real.exp (-(2 * sourceU + 4 * pModel + 7)) ≤ α) :
    Real.exp (-Plate) ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog sourceU pModel) (allocatedModelTestLog sourceU pModel) α)
      Pphysical coarseTarget := by
  have h := preparedFiniteScheduleDirectWidth_inv B U basis S selection Pdetect Cdetect
    hCdetect Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical
    coarseTarget pRadius sourceU pModel pSlice α scalar geometryAt hα
  have hchoice := sharedWidthNormalizedTuplePreparedChoice (fun _ : Unit => s + 1)
    (fun _ => allocatedDetectedKernelCutoff s G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect
      (allocatedModelTestLog sourceU pModel) (allocatedModelTestLog sourceU pModel) α)
    (fun _ => selection) (fun _ => Pphysical) (fun _ => coarseTarget) Plate (fun _ => h)
  exact hchoice.2.2 ()

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem preparedFiniteScheduleDirectScalarBounds_explicit
    (m : ℕ) {K : Type*} [Fintype K] (degree Cdetect : K → ℕ)
    (hdegree : ∀ k, degree k ≤ m) (G : Type) [Fintype G]
    (nX count : ℕ) (Pchart D pRadius Qstride Pscale requestedCoarse extraLate : ℝ)
    (u pModel pSlice Prho : K → ℝ)
    (hchart : 0 ≤ Pchart) (hD : 0 ≤ D) (hradius : 0 ≤ pRadius)
    (hu : ∀ k, 0 ≤ u k) (hmodel : ∀ k, 0 ≤ pModel k) (hstride : 0 ≤ Qstride)
    (hrho : ∀ k, 0 ≤ Prho k) (hslice : ∀ k, pSlice k ≤ pModel k)
    (hcount : ∀ k, (count : ℝ) ≤ Real.exp (pModel k)) :
    let pDetect := fun k => allocatedModelTestLog (u k) (pModel k)
    let gainLog := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
      (pDetect k) (pDetect k) (2 * u k + 4 * pModel k + 7)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
      (gainLog k + pDetect k + 4)
    let Pphysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ k, Pk k
    let target := fun k => gainLog k + 40 + coefficientErrorSpatialLog Pphysical
    let Pmaster := preparedFiniteScheduleDirectMaster Pchart D pRadius Qstride
      Pphysical u pModel Prho target gainLog
    let coarseTarget := preparedFiniteScheduleDirectCoarse gainLog requestedCoarse
    let Plate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget extraLate
    (∀ k, Pk k ≤ Pscale) → ∀ k,
      PreparedUniformDegreeDirectScalarBounds m (degree k) nX count (Cdetect k)
        Pchart Pscale D (target k) (Pk k) (Prho k) Qstride Pmaster Plate
        (gainLog k) Pphysical coarseTarget pRadius (u k) (pModel k) (pSlice k) := by
  intro pDetect gainLog Pk Pphysical target Pmaster coarseTarget Plate hkernelScale
  have hp (k) : 0 ≤ pDetect k := by
    dsimp only [pDetect, allocatedModelTestLog]
    have := hu k
    have := hmodel k
    positivity
  have ha (k) : 0 ≤ 2 * u k + 4 * pModel k + 7 := by
    have := hu k
    have := hmodel k
    positivity
  have hg (k) : 0 ≤ gainLog k :=
    slicedDetectionGainLog_nonneg (degree k) (Cdetect k) count (hp k) (hp k) (ha k)
  have hk (k) : 0 ≤ Pk k := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    have := hg k
    have := hp k
    positivity
  have hkSum0 : 0 ≤ ∑ k, Pk k := Finset.sum_nonneg (fun k _ => hk k)
  have hkSum (k) : Pk k ≤ ∑ t, Pk t :=
    Finset.single_le_sum (fun t _ => hk t) (Finset.mem_univ k)
  have hphysEq : Pphysical = (m : ℝ) + 2 + nX + count + Qstride + ∑ k, Pk k := by
    simp only [Pphysical, Nat.cast_add, Nat.cast_ofNat]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg nX
  have hcount0 : (0 : ℝ) ≤ count := Nat.cast_nonneg count
  have hphysical0 : 0 ≤ Pphysical := by
    linarith only [hphysEq, hm0, hnX0, hcount0, hstride, hkSum0]
  have hkernelPhysical (k) : Pk k ≤ Pphysical := by
    linarith only [hphysEq, hm0, hnX0, hcount0, hstride, hkSum k]
  have herror0 := coefficientErrorSpatialLog_nonneg hphysical0
  have ht (k) : 0 ≤ target k := by
    dsimp only [target]
    have := hg k
    positivity
  let total := ∑ k, (u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32)
  have hentry (k) : 0 ≤ u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32 := by
    have := hu k
    have := hmodel k
    have := hp k
    have := hrho k
    have := ht k
    have := hg k
    positivity
  have htotal0 : 0 ≤ total := Finset.sum_nonneg (fun k _ => hentry k)
  have htotal (k) : u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32 ≤ total :=
    Finset.single_le_sum (fun k _ => hentry k) (Finset.mem_univ k)
  have hmasterEq : Pmaster = Pchart + D + pRadius + Qstride + Pphysical + total := rfl
  have hmaster0 : 0 ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, hphysical0, htotal0]
  have hphysicalMaster : Pphysical ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, htotal0]
  have htotalMaster : total ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, hphysical0]
  have hlate : Pmaster ≤ Plate := le_max_left _ _
  have hscaleLate : Pscale ≤ Plate := (le_max_left _ _).trans (le_max_right _ _)
  have hcoarseLate : coarseTarget ≤ Plate :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hxiLate : 2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4
      ≤ Plate :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  intro k
  have hsmReal : (degree k : ℝ) ≤ m := by exact_mod_cast hdegree k
  have hlocalMaster := (htotal k).trans htotalMaster
  have hgainEntry (t : K) : (0 : ℝ) ≤ gainLog t + 32 := by
    have := hg t
    positivity
  have hcoarseSum : gainLog k + 32 ≤ ∑ t, (gainLog t + 32) :=
    Finset.single_le_sum (fun t _ => hgainEntry t) (Finset.mem_univ k)
  refine {
    master_nonneg := hmaster0
    late := hlate
    chart_master := ?_
    dimension_master := ?_
    radius_master := ?_
    scale_late := hscaleLate
    kernel_scale := hkernelScale k
    kernel_master := ⟨hk k, (hkernelPhysical k).trans hphysicalMaster⟩
    stride_master := ⟨hstride, ?_⟩
    detect_master := ⟨hp k, ?_⟩
    ambient_master := le_trans ?_ hphysicalMaster
    u_master := ⟨hu k, ?_⟩
    model_master := ⟨hmodel k, ?_⟩
    slice_model := hslice k
    count_model := hcount k
    rho_master := ⟨hrho k, ?_⟩
    target_master := ⟨ht k, ?_⟩
    gain_master := ⟨hg k, ?_⟩
    coarse_master := ?_
    coarse_lower := hcoarseSum.trans (le_max_left _ _)
    coarse_late := hcoarseLate
    physical_master := ⟨hphysical0, hphysicalMaster⟩
    degree_physical := ?_
    detector_physical := ?_
    variables_physical := ?_
    ambient_physical := ?_
    kernel_physical := hkernelPhysical k
    stride_physical := ?_
    gain_log := le_rfl
    precision := ?_
    xi_late := hxiLate }
  · linarith only [hmasterEq, hD, hradius, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hradius, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hradius, hphysical0, htotal0]
  · linarith only [hlocalMaster, hu k, hmodel k, hrho k, ht k, hg k]
  · linarith only [hphysEq, hm0, hcount0, hstride, hkSum0]
  · linarith only [hlocalMaster, hmodel k, hp k, hrho k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hp k, hrho k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, ht k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, ht k]
  · simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hphysEq, hnX0, hcount0, hstride, hkSum0]
  · simp only [Nat.cast_add, Nat.cast_ofNat]
    linarith only [hphysEq, hsmReal, hnX0, hcount0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hnX0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hcount0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hnX0, hcount0, hkSum0]
  · dsimp only [target]
    linarith only

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem PreparedUniformDegreeDirectScalarBounds.late_mono
    {m s nX nVars Cdetect : ℕ}
    {Pchart Pscale D target Pk Prho Qstride Pmaster Plate Plate' pGain Pphysical
      coarseTarget pRadius u pModel pSlice : ℝ}
    (h : PreparedUniformDegreeDirectScalarBounds m s nX nVars Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical
      coarseTarget pRadius u pModel pSlice)
    (hLate : Plate ≤ Plate') :
    PreparedUniformDegreeDirectScalarBounds m s nX nVars Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate' pGain Pphysical
      coarseTarget pRadius u pModel pSlice := by
  exact { h with
    late := h.late.trans hLate
    scale_late := h.scale_late.trans hLate
    coarse_late := h.coarse_late.trans hLate
    xi_late := h.xi_late.trans hLate }

theorem preparedFiniteScheduleLocalScalarBounds_explicit
    (m degree Cdetect : ℕ) (hdegree : degree ≤ m) (G : Type) [Fintype G]
    (nX count : ℕ) (Pchart D pRadius Qstride Pscale coarseTarget extraLate : ℝ)
    (u pModel pSlice Prho : ℝ)
    (hchart : 0 ≤ Pchart) (hD : 0 ≤ D) (hradius : 0 ≤ pRadius)
    (hu : 0 ≤ u) (hmodel : 0 ≤ pModel) (hstride : 0 ≤ Qstride)
    (hrho : 0 ≤ Prho) (hslice : pSlice ≤ pModel)
    (hcount : (count : ℝ) ≤ Real.exp pModel) :
    let pDetect := allocatedModelTestLog u pModel
    let gainLog := slicedDetectionGainLog degree Cdetect count
      pDetect pDetect (2 * u + 4 * pModel + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
      (gainLog + pDetect + 4)
    let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
    let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
    let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
      Pphysical u pModel Prho target gainLog
    let localLate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical
      coarseTarget extraLate
    Pk ≤ Pscale → gainLog + 32 ≤ coarseTarget →
    ∀ {Plate : ℝ}, localLate ≤ Plate →
      PreparedUniformDegreeDirectScalarBounds m degree nX count Cdetect
        Pchart Pscale D target Pk Prho Qstride Pmaster Plate gainLog
        Pphysical coarseTarget pRadius u pModel pSlice := by
  intro pDetect gainLog Pk Pphysical target Pmaster localLate hkernel hcoarse Plate hLate
  have h := preparedFiniteScheduleDirectScalarBounds_explicit
    m (fun _ : Unit => degree) (fun _ : Unit => Cdetect) (fun _ => hdegree) G
    nX count Pchart D pRadius Qstride Pscale coarseTarget extraLate
    (fun _ => u) (fun _ => pModel) (fun _ => pSlice) (fun _ => Prho)
    hchart hD hradius (fun _ => hu) (fun _ => hmodel) hstride
    (fun _ => hrho) (fun _ => hslice) (fun _ => hcount)
    (fun _ => hkernel) ()
  have hlocal : PreparedUniformDegreeDirectScalarBounds m degree nX count Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster localLate gainLog
      Pphysical coarseTarget pRadius u pModel pSlice := by
    simpa only [preparedFiniteScheduleDirectMaster, preparedFiniteScheduleDirectCoarse,
      Finset.univ_unique, Finset.sum_singleton, max_eq_right hcoarse,
      Pmaster, Pphysical, target, localLate, gainLog, pDetect, Pk,
      preparedFiniteScheduleLocalPhysical, preparedFiniteScheduleLocalMaster] using h
  exact hlocal.late_mono hLate

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedEmptyLayerFiniteScheduleLocalDirectSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedEmptyLayerFiniteScheduleLocalDirectSource
    {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (Vtail : Fin m → ℝ≥0) (τ : ℝ)
    (Q : Fin m → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {K : Type} [Fintype K] (degree : K → ℕ)
    (selection : ∀ k, Fin (degree k + 1) ↪ G)
    (hm : 0 < m) (hsm : s ≤ m) (hdegree : ∀ k, degree k ≤ s)
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G)
    (Bstruct Qstride Qσ requestedCoarse extraLate : ℝ)
    (sourceU modelLog sliceLog : K → ℝ)
    (hB : 0 ≤ Bstruct) (hnum : (Fintype.card G : ℝ) ≤ Bstruct)
    (hsourceU : ∀ k, 0 ≤ sourceU k) (hmodelLog : ∀ k, 0 ≤ modelLog k)
    (hsliceModel : ∀ k, sliceLog k ≤ modelLog k)
    (hcountModel : ∀ k, (Fintype.card G : ℝ) ≤ Real.exp (modelLog k))
    (hQstride : 0 ≤ Qstride) (hQσ : 0 ≤ Qσ) :
    let count := Fintype.card (LayerSamplerVariables G I n B)
    let pnum : ℝ := Fintype.card G
    let Cdetect := fun k => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun k => slicedDetectionGainLog (degree k) (Cdetect k)
      count (pDetect k) (pDetect k) (aDetect k)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
      (detectionGain k + pDetect k + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
    let Prho := fun k => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
    let Ptail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
    let lengthLogs := fun k => allocatedAffineLengthLog m D Pscale (Prho k) (Pk k)
      (target k) (pDetect k + 2) (Tmod k)
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let localLate := fun k : K => preparedUniformDegreeDirectLate
      (Pmaster k) Pscale (Pphysical k) coarseTarget extraLate
    let Plate := ∑ k : K, localLate k
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      ∀ S : LayerSamplerScale (G := G) B U b R (fun _ => σ),
        (∀ k, Real.exp (lengthLogs k) ≤ S.value) →
        (S.value : ℝ) ≤ Real.exp extraLate →
        (∀ k, PreparedUniformDegreeDirectScalarBounds m (degree k) nX count (Cdetect k)
          Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
          (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
        (∀ k, PreparedUniformDegreeGeometryAt B U b S (degree k) (Cdetect k) nX
          Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (pDetect k) pRadius
          (aDetect k) (detectionGain k)) ∧
        (∀ k, PreparedScheduledDirectSourceAvailability
          (B := B) (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := selection k) (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) := by
  intro count pnum Cdetect R pRadius D pDetect aDetect detectionGain Pk Pphysical target E
    Prho Ptail Pscale Tmod lengthLogs Pmaster coarseTarget localLate Plate
  let : ∀ j, CompactSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun j => latticeQuotient_compact _
  let ν := fun j => probabilityAddHaar (euclideanSubspace (U j) ⧸
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup)
  let : ∀ j, (ν j).IsAddLeftInvariant := fun j => probabilityAddHaar_invariant _
  let : ∀ j, IsProbabilityMeasure (ν j) := fun j => probabilityAddHaar_probability _
  let : CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U) :=
    coefficientTorus_compact_of_lattice U
  let : MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U) := borel _
  let : BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U) := ⟨rfl⟩
  let μ := probabilityAddHaar (CoefficientTorus (K := LayerSamplerVariables G I n B) U)
  let : μ.IsAddLeftInvariant := probabilityAddHaar_invariant _
  let : IsProbabilityMeasure μ := probabilityAddHaar_probability _
  have hcount : count = Fintype.card G := emptyLayerVariables_card B
  have hpnum : 0 ≤ pnum := Nat.cast_nonneg _
  have hvars : (count : ℝ) ≤ pnum := by simp only [hcount, pnum, le_refl]
  have hI (j) : (Fintype.card (I j) : ℝ) ≤ pnum := by
    simpa only [Fintype.card_eq_zero, Nat.cast_zero] using hpnum
  have hn (j) : (n j : ℝ) ≤ pnum := by
    have hnzero : n j = 0 := by
      have := Fintype.card_eq_zero (α := Fin (n j))
      simpa only [Fintype.card_fin] using this
    simpa only [hnzero, Nat.cast_zero] using hpnum
  have hblocks (k : K) (a : LayerSamplerAxis I n) :
      (boundedBooleanJetRows (Fin (degree k + 1)) (a.1.val + 1)).card ≤ Fintype.card (B a) := by
    exact Sum.elim isEmptyElim isEmptyElim a.2
  have hpDetect (k) : 0 ≤ pDetect k := by
    dsimp only [pDetect, allocatedModelTestLog]
    linarith only [hsourceU k, hmodelLog k]
  have haDetect (k) : 0 ≤ aDetect k := by
    dsimp only [aDetect]
    linarith only [hsourceU k, hmodelLog k]
  have hgain (k) : 0 ≤ detectionGain k :=
    slicedDetectionGainLog_nonneg (degree k) (Cdetect k) count
      (hpDetect k) (hpDetect k) (haDetect k)
  have hkernel (k) : 0 ≤ Pk k := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    have := hgain k
    have := hpDetect k
    positivity
  have hphysical (k) : 0 ≤ Pphysical k := by
    dsimp only [Pphysical, preparedFiniteScheduleLocalPhysical]
    have := hkernel k
    positivity
  have htarget (k) : 0 ≤ target k := by
    have he := coefficientErrorSpatialLog_nonneg (hphysical k)
    dsimp only [target]
    linarith only [hgain k, he]
  have hgeometry := exists_preparedFiniteScheduleGeometryPrescribedScale_s2 m degree Cdetect B
    nX pDetect aDetect target hm (fun k => (hdegree k).trans hsm)
    hB ⟨hpnum, hnum⟩ hvars hI hn hblocks hpDetect haDetect hQstride htarget
  obtain ⟨hpRadius, hR, hD, hlogs, t, ht, hsamplers⟩ := hgeometry
  obtain ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hDscale, hPkScale, hscales⟩ := hsamplers hQσ
  let σ := preparedUniformDegreeTolerance t Qσ
  refine ⟨(fun j => (hR j).1), σ, hσ, hpRadius.1, (fun j => (hR j).2),
    hσone, hσexp, hσinv, ?_⟩
  intro S hlength hS
  have hGeometryAll := hscales U b S hlength
  have hcoarse (k) : detectionGain k + 32 ≤ coarseTarget :=
    (Finset.single_le_sum (f := fun t : K => detectionGain t + 32)
      (fun t _ => by linarith only [hgain t])
      (Finset.mem_univ k)).trans (le_max_left _ _)
  have scalarLocal (k) := preparedFiniteScheduleLocalScalarBounds_explicit
    m (degree k) (Cdetect k) ((hdegree k).trans hsm) G nX count
    Bstruct D pRadius Qstride Pscale coarseTarget extraLate
    (sourceU k) (modelLog k) (sliceLog k) (Prho k)
    hB hD hpRadius.1 (hsourceU k) (hmodelLog k) hQstride (hlogs k).2.2.1
    (hsliceModel k) (by simpa only [hcount] using hcountModel k)
    (hPkScale k) (hcoarse k) (Plate := localLate k) le_rfl
  have hlocalLate0 (k) : 0 ≤ localLate k :=
    (scalarLocal k).master_nonneg.trans (scalarLocal k).late
  have hLate (k) : localLate k ≤ Plate :=
    Finset.single_le_sum (f := localLate)
      (fun t _ => hlocalLate0 t) (Finset.mem_univ k)
  have scalarAll (k) := (scalarLocal k).late_mono (hLate k)
  refine ⟨scalarAll, hGeometryAll, ?_⟩
  intro k
  exact preparedFiniteScheduleGeometryDirectSource_s2
    (B := B) (U := U) (basis := b) (S := S)
    (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
    (selection := selection k) (stride := stride) (N := N) (Pdetect := Pdetect)
    (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
    (Vtail := Vtail) (τ := τ) (Q := Q) (hb := hb) (o := o)
    (bW := bW) (ν := ν) (μ := μ)
    (Cdetect k) rfl ((hdegree k).trans hsm)
    Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
    (detectionGain k) (Pphysical k) coarseTarget pRadius (scalarAll k) (hGeometryAll k)
    (fun j => (hR j).2.1) (fun j => (hR j).2.2) (fun _ => hσone)
    (hS.trans (Real.exp_le_exp.mpr
      ((preparedUniformDegreeDirectLate_extra (Pmaster k) Pscale
        (Pphysical k) coarseTarget extraLate).trans (hLate k))))
    (fun j i => isEmptyElim i) (fun j i => isEmptyElim i)
    ((Nat.mul_le_mul (Nat.add_le_add_right (hdegree k) 1)
      (Nat.add_le_add_right (hdegree k) 3)).trans hcapacity)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedEmptyLayerLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [Fintype X] in

@[simp] theorem allocatedCenteredJointDensity_empty_layers
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z = 1 := by
  exact canonicalCoefficientDensity_empty U b hb o _ _ _ _

variable (N : X → ℕ) (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

theorem allocatedCenteredJointDensityMass_empty_layers
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hwidth : ∀ z, 0 < allocatedExternalCandidateWidths B U b S N τ ξ z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (allocatedExternalCandidateWidths B U b S N τ ξ) z) :
    selectedJointDensityMass (trimmedIntegerBox N (spatialTrimMargin τ N)) stride cells
      (allocatedExternalCandidateWidths B U b S N τ ξ)
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center) = 1 := by
  rw [← selectedJointReference_densityMass _ hbase _ _ _ hwidth hZ]
  simp only [allocatedCenteredJointDensity_empty_layers, FiniteProbabilityWeights.mean_const]

theorem allocatedExternalCandidateSampler_empty_layers
    (hN : ∀ x, 0 < N x) (hτ : 0 < τ) (hξ : 0 < ξ)
    (hstride : ∀ x, 0 < stride x)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (allocatedExternalCandidateWidths B U b S N τ ξ) z) :
    AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center := by
  refine ⟨hN, hτ, hξ, hstride, hbase, hZ, ?_⟩
  rw [allocatedCenteredJointDensityMass_empty_layers B U b S hb o hR hσ poly hm
    center N τ ξ stride cells hbase
    (narrowTrimmedSpatialWidths_pos (allocatedExternalCandidateRootBudget_nonneg B U b S)
      hτ hξ N hN) hZ]
  norm_num

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedScalarEmptyLayerSampler
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    (τ ξ : ℝ) (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem allocatedExternalCandidateSampler_of_scalarReference_empty_layers
    (hN : ∀ x, 0 < N x) (hτ : 0 < τ) (hξ : 0 < ξ)
    (hbase : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := G) ((Fintype.card G : ℝ) * S.value) τ N) z) :
    AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hm τ ξ (fun _ : X => 1) {0} center := by
  apply allocatedExternalCandidateSampler_empty_layers B U b S hb o hR hσ poly hm
    center N τ ξ (fun _ : X => 1) {0} hN hτ hξ (fun _ => by norm_num) hbase
  rw [allocatedExternalCandidateWidths_empty_layers]
  rw [← selectedResidueSmoothMass_scalarCoordinateEquiv (emptyLayerVariablesEquiv B)
    ((Fintype.card G : ℝ) * S.value) τ N]
  exact hZ

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarFiniteScheduleCandidateDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

namespace AllocatedExternalCandidateSampler
variable {s nX : ℕ}
    {I₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
    {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
    {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
    {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
    {R₀ σ₀ : Fin 0 → ℝ}
    {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
    {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
    {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
    {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
    {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
    {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
    {τ ξ₀ : ℝ}
    {center₀ : CoefficientTorus (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]

theorem nativeDetection_of_preparedScalarFiniteSchedule
    (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
      N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀)
    {K : Type} [Fintype K] (degree : K → ℕ) (hdegree : ∀ k, degree k ≤ s)
    (Pdetect : Polynomial ℕ) (Bstruct extraLate : ℝ)
    (sourceU modelLog sliceLog α : K → ℝ)
    (hB : 0 ≤ Bstruct) (hnum : (scalarNativeDimension s : ℝ) ≤ Bstruct)
    (hsourceU : ∀ k, 0 ≤ sourceU k) (hmodelLog : ∀ k, 0 ≤ modelLog k)
    (hsliceModel : ∀ k, sliceLog k ≤ modelLog k)
    (hcountModel : ∀ k, (scalarNativeDimension s : ℝ) ≤ Real.exp (modelLog k))
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (hdimension : ∀ k, (scalarNativeDimension s : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k))) :
    let q := max s 1
    let count := scalarNativeDimension s
    let Cdetect := fun k => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let pRadius := allocatedCommonProductRadiusLog q Bstruct Bstruct
    let D := allocatedComparisonDimension q (count : ℝ)
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun k => slicedDetectionGainLog (degree k) (Cdetect k)
      count (pDetect k) (pDetect k) (aDetect k)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1))
      (Fin (scalarNativeDimension s)) (detectionGain k + pDetect k + 4)
    let Pphysical := fun k => preparedFiniteScheduleLocalPhysical q nX count 0 (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun k => target k + D * ((q * 2 ^ (q + 1) : ℕ) * Pk k) + 5
    let Prho := fun k => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
    let Ptail := fun k => affineProfileToleranceEnvelope q D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail 0
    let Tmod := fun k => ((q + 1 : ℕ) : ℝ) * Pk k + nX * 0
    let lengthLogs := fun k => allocatedAffineLengthLog q D Pscale (Prho k) (Pk k)
      (target k) (pDetect k + 2) (Tmod k)
    let Pmaster := fun k => preparedFiniteScheduleLocalMaster Bstruct D pRadius 0
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain 0
    let localLate := fun k => preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget extraLate
    let Plate := ∑ k, localLate k
    (∀ k, Real.exp (lengthLogs k) ≤ S₀.value) →
    Real.exp (((probabilityProfileLipschitz : ℝ) + 8) + (D + 4) + pRadius + Pscale) ≤ S₀.value →
    (S₀.value : ℝ) ≤ Real.exp extraLate →
    (∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ)) →
    (∀ k, τ⁻¹ ≤ Real.exp (Pphysical k)) →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    ∀ k, A₀.NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) := by
  intro q count Cdetect pRadius D pDetect aDetect detectionGain Pk Pphysical target E
    Prho Ptail Pscale Tmod lengthLogs Pmaster coarseTarget localLate Plate
    hlength hwidth hSupper hsize hτInv hτHalf hτDim
  let BE := CanonicalEmptyLayerGeometry.B q
  let UE := CanonicalEmptyLayerGeometry.U q
  let bE := CanonicalEmptyLayerGeometry.b q
  let hbE := CanonicalEmptyLayerGeometry.hb q
  let oE := CanonicalEmptyLayerGeometry.o q
  let bWE := CanonicalEmptyLayerGeometry.bW q
  let selection := fun k => scalarNativeSelection (hdegree k)
  have hq : 0 < q := by dsimp only [q]; omega
  have hsq : s ≤ q := le_max_left _ _
  have hsource := exists_preparedEmptyLayerFiniteScheduleLocalDirectSource
    (G := Fin (scalarNativeDimension s)) BE UE bE (fun _ : Fin nX => 1) N Pdetect
    (fun _ => 1) τ (CanonicalEmptyLayerGeometry.Q q) hbE oE bWE
    degree selection hq hsq hdegree
    (by rw [Fintype.card_fin]; exact scalarNativeDimension_capacity (Nat.le_refl s))
    Bstruct 0 0 0 extraLate sourceU modelLog sliceLog hB
    (by simpa only [Fintype.card_fin] using hnum)
    hsourceU hmodelLog hsliceModel
    (fun k => by simpa only [Fintype.card_fin] using hcountModel k)
    (le_refl 0) (le_refl 0)
  simp only [emptyLayerVariables_card, Fintype.card_fin] at hsource
  obtain ⟨hR, σ, hσ, hpRadius, hRadius, hσone, hσexp, hσinv, hscales⟩ := hsource
  have hprofile8 : 8 * (probabilityProfileLipschitz : ℝ) ≤
      Real.exp ((probabilityProfileLipschitz : ℝ) + 8) := by
    have h1 : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (probabilityProfileLipschitz : ℝ) :=
      le_trans (by linarith) (Real.add_one_le_exp _)
    have h8 : (8 : ℝ) ≤ Real.exp (8 : ℝ) :=
      le_trans (by norm_num) (Real.add_one_le_exp _)
    rw [Real.exp_add]
    calc
      _ = (probabilityProfileLipschitz : ℝ) * 8 := by ring
      _ ≤ _ := mul_le_mul h1 h8 (by norm_num) (Real.exp_pos _).le
  have hcount4 : ∀ j : Fin q, 4 * ((Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables (Fin (scalarNativeDimension s)) (CanonicalEmptyLayerGeometry.I q)
        (CanonicalEmptyLayerGeometry.n q) BE) (j.val + 1)) : ℝ) + 1) ≤ Real.exp (D + 4) := by
    intro j
    simpa only [Fintype.card_fin] using emptyLayerCoefficientCount_le_exp (G := Fin (scalarNativeDimension s)) BE j
  let S := emptyLayerSamplerScaleOfExp BE UE bE hR (fun _ => hσ)
    hprofile8 hcount4 (fun j => (hRadius j).2) (fun _ => hσinv)
    S₀.value S₀.positive hwidth
  have hvalue : S.value = S₀.value := rfl
  obtain ⟨scalarAll, geometryAll, availableAll⟩ :=
    hscales S (fun k => hlength k) hSupper
  let poly := CanonicalEmptyLayerGeometry.poly q (Fin nX)
  let hmem := CanonicalEmptyLayerGeometry.poly_mem q (Fin nX)
  let ξ := Real.exp (-Plate)
  let center : CoefficientTorus (K := LayerSamplerVariables (Fin (scalarNativeDimension s))
      (CanonicalEmptyLayerGeometry.I q) (CanonicalEmptyLayerGeometry.n q) BE) UE := 0
  let A : AllocatedExternalCandidateSampler BE UE bE S hbE oE hR (fun _ => hσ)
      N poly hmem τ ξ (fun _ : Fin nX => 1) {0} center :=
    allocatedExternalCandidateSampler_of_scalarReference_empty_layers τ ξ center
      A₀.size_pos A₀.trim_pos (Real.exp_pos _) A₀.bases_nonempty
      A₀.scalarAxesMass_pos_zero_layers
  have hξSmall (k) : ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex BE (layerSamplerDegree (CanonicalEmptyLayerGeometry.I q)
        (CanonicalEmptyLayerGeometry.n q))) (selection k)
      (allocatedDetectedKernelCutoff (degree k) (Fin (scalarNativeDimension s)) count
        Pdetect (pDetect k) (pDetect k) (α k / 2)) (Pphysical k) coarseTarget := by
    have scalarK : PreparedUniformDegreeDirectScalarBounds q (degree k) nX
        (Fintype.card (LayerSamplerVariables (Fin (scalarNativeDimension s))
          (CanonicalEmptyLayerGeometry.I q) (CanonicalEmptyLayerGeometry.n q) BE))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) 0 (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius
        (sourceU k) (modelLog k) (sliceLog k) := by
      simpa only [emptyLayerVariables_card, Fintype.card_fin] using scalarAll k
    have h := preparedFiniteScheduleDirectWidth BE UE bE S (selection k) Pdetect
      (Cdetect k) rfl Bstruct Pscale D (target k) (Pk k) (Prho k) 0 (Pmaster k) Plate
      (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k)
      (sliceLog k) (α k / 2) scalarK (geometryAll k) (hαLower k)
    simpa only [emptyLayerVariables_card, Fintype.card_fin] using h
  have hξLate : ξ⁻¹ ≤ Real.exp Plate := by
    change (Real.exp (-Plate))⁻¹ ≤ Real.exp Plate
    rw [← Real.exp_neg, neg_neg]
  have hdetect := preparedEmptyLayerFiniteScheduleCandidateDetection_s2
    BE UE bE hR (fun _ => hσ) S degree selection (fun _ : Fin nX => 1) N Pdetect
    sourceU modelLog sliceLog α τ ξ hbE oE Bstruct 0 Pmaster Plate Pphysical coarseTarget
    detectionGain availableAll hαLower hαHalfOne
    (fun _ => by simp only [Nat.cast_one, Real.exp_zero, le_refl])
    hprofile hcutoff hτInv hτHalf hτDim
    (fun k => by simpa only [emptyLayerVariables_card, Fintype.card_fin] using hξSmall k)
    hξLate {0} poly hmem hsize
    (fun k => by simpa only [emptyLayerVariables_card, Fintype.card_fin] using hdimension k)
    center A
  have hdec : instDecidableEqFin nX = Classical.decEq (Fin nX) := Subsingleton.elim _ _
  rw [hdec] at hdetect
  intro k
  rw [hdec]
  exact A₀.nativeDetection_of_emptyLayer_sampler_s2 A hvalue (degree k) (sliceLog k)
    (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q (degree k))
      (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) (@hdetect k)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedForwardCanonicalFixedCenterSource
namespace OAI

section

namespace Erdos3

theorem unconditionedSpatialTrimFraction_inv_pow_bound {p : ℝ} {d : ℕ}
    (hp : 2 ≤ p) (hd : (d : ℝ) ≤ p) :
    (unconditionedSpatialTrimFraction d (Real.exp (-p)))⁻¹ ≤
      Real.exp ((p + 2) ^ 3) := by
  apply (unconditionedSpatialTrimFraction_inv_exp_bound hd).trans
  apply Real.exp_le_exp.mpr
  have hs : 16 ≤ (p + 2) ^ 2 := by nlinarith
  have hm := mul_nonneg (sub_nonneg.mpr hs) (by linarith : 0 ≤ p + 2)
  nlinarith

theorem unconditionedSpatialTrimFraction_exp_bounds {p : ℝ} {d : ℕ}
    (hp : 2 ≤ p) (hd : (d : ℝ) ≤ p) :
    let τ := unconditionedSpatialTrimFraction d (Real.exp (-p))
    0 < τ ∧ τ ≤ 1 / 2 ∧ (d : ℝ) * τ ≤ 1 / 2 ∧
      τ⁻¹ ≤ Real.exp ((p + 2) ^ 3) := by
  have hsurplus : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨hτ, hhalf, hdim⟩ :=
    unconditionedSpatialTrimFraction_bounds d (Real.exp_pos _) hsurplus
  refine ⟨hτ, hhalf, ?_, unconditionedSpatialTrimFraction_inv_pow_bound hp hd⟩
  linarith

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators

theorem preparedFiniteSchedule_kernel_input_le
    (I G : Type*) [Fintype I] [Fintype G] {R : ℝ} (hR : 0 ≤ R) :
    R ≤ scalarKernelLogarithmicBudget I G R := by
  let base : ℝ := 10 + (Fintype.card I : ℝ) + Fintype.card G +
    Fintype.card G * (Fintype.card I + 1) + R
  have hI : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hG : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
  have hcross : (0 : ℝ) ≤ Fintype.card G * (Fintype.card I + 1) := by positivity
  have hbase : 1 ≤ base := by dsimp only [base]; linarith only [hI, hG, hcross, hR]
  have hRbase : R ≤ base := by dsimp only [base]; linarith only [hI, hG, hcross]
  have hcube : base ≤ base ^ 3 := le_self_pow₀ hbase (by norm_num)
  have hproduct : (0 : ℝ) ≤ (Fintype.card G : ℝ) *
      (Fintype.card I + 1) * Fintype.card I := by positivity
  have hfactor : (1 : ℝ) ≤ 4 + 3 * ((Fintype.card G : ℝ) *
      (Fintype.card I + 1) * Fintype.card I) := by linarith only [hproduct]
  have hinner : 0 ≤ 16 * base ^ 3 + 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfactor hinner
  rw [scalarKernelLogarithmicBudget_eq]
  change R ≤ 2 * ((4 + 3 * ((Fintype.card G : ℝ) *
    (Fintype.card I + 1) * Fintype.card I)) * (16 * base ^ 3 + 2)) + 8
  linarith only [hRbase, hcube, hmul, hbase]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedScalarFiniteScheduleLocalPhysical_model_add
    (q nX count degree Cdetect : ℕ) (G : Type*) [Fintype G]
    {sourceU modelLog : ℝ} (hsource : 0 ≤ sourceU) (hmodel : 0 ≤ modelLog) :
    let pDetect := allocatedModelTestLog sourceU modelLog
    let pGain := slicedDetectionGainLog degree Cdetect count pDetect pDetect
      (2 * sourceU + 4 * modelLog + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
      (pGain + pDetect + 4)
    modelLog + (nX : ℝ) + 8 ≤ preparedFiniteScheduleLocalPhysical q nX count 0 Pk := by
  intro pDetect pGain Pk
  have hdetect : 0 ≤ pDetect := by
    dsimp only [pDetect, allocatedModelTestLog]
    positivity
  have hgain : 0 ≤ pGain := slicedDetectionGainLog_nonneg degree Cdetect count
    hdetect hdetect (by positivity)
  have hinput : 0 ≤ pGain + pDetect + 4 := by positivity
  have hkernel := preparedFiniteSchedule_kernel_input_le (Fin (degree + 1)) G hinput
  change pGain + pDetect + 4 ≤ Pk at hkernel
  have hq : (0 : ℝ) ≤ (q + 2 : ℕ) := Nat.cast_nonneg _
  have hcount : (0 : ℝ) ≤ count := Nat.cast_nonneg _
  dsimp only [preparedFiniteScheduleLocalPhysical]
  dsimp only [pDetect, allocatedModelTestLog] at hkernel
  linarith only [hkernel, hgain, hq, hcount, hsource, hmodel]

theorem preparedScalarFiniteScheduleLocalPhysical_model
    (q nX count degree Cdetect : ℕ) (G : Type*) [Fintype G]
    {sourceU modelLog : ℝ} (hsource : 0 ≤ sourceU) (hmodel : 0 ≤ modelLog) :
    let pDetect := allocatedModelTestLog sourceU modelLog
    let pGain := slicedDetectionGainLog degree Cdetect count pDetect pDetect
      (2 * sourceU + 4 * modelLog + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
      (pGain + pDetect + 4)
    modelLog ≤ preparedFiniteScheduleLocalPhysical q nX count 0 Pk := by
  intro pDetect pGain Pk
  have h := preparedScalarFiniteScheduleLocalPhysical_model_add
    q nX count degree Cdetect G hsource hmodel
  change modelLog + (nX : ℝ) + 8 ≤
    preparedFiniteScheduleLocalPhysical q nX count 0 Pk at h
  have hnX : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  linarith only [h, hnX]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardWork_cubic_lower
    (A : ℕ) (constants : ℕ → ℕ) (stage : ℕ) {p seed : ℝ}
    (hp : 2 ≤ p) (hA : 3 ≤ A) (hseed : p ≤ seed) :
    (p + 2) ^ 3 ≤ preparedFiniteForwardWork A constants stage seed := by
  have hseed0 : 0 ≤ seed := by linarith
  have hparam := le_preparedFiniteForwardParameter A constants stage hseed0
  have hAreal : (3 : ℝ) ≤ A := by exact_mod_cast hA
  rw [preparedFiniteForwardWork_eq]
  calc
    (p + 2) ^ 3 ≤ (preparedFiniteForwardParameter A constants stage seed + A) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hA

theorem preparedScalarFiniteScheduleLocalPhysical_exp_trim
    (q nX count degree Cdetect A stage : ℕ) (G : Type*) [Fintype G]
    (constants : ℕ → ℕ) {p seed sourceU : ℝ}
    (hp : 2 ≤ p) (hX : (nX : ℝ) ≤ p) (hA : 3 ≤ A)
    (hseed : p ≤ seed) (hsource : 0 ≤ sourceU) :
    let modelLog := preparedFiniteForwardWork A constants stage seed
    let pDetect := allocatedModelTestLog sourceU modelLog
    let gain := slicedDetectionGainLog degree Cdetect count pDetect pDetect
      (2 * sourceU + 4 * modelLog + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G (gain + pDetect + 4)
    let τ := unconditionedSpatialTrimFraction nX (Real.exp (-p))
    τ⁻¹ ≤ Real.exp (preparedFiniteScheduleLocalPhysical q nX count 0 Pk) ∧
      τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 := by
  intro modelLog pDetect gain Pk τ
  obtain ⟨_, hhalf, hdim, hinv⟩ := unconditionedSpatialTrimFraction_exp_bounds hp hX
  have hmodel : 0 ≤ modelLog :=
    preparedFiniteForwardWork_nonneg A constants stage (by linarith)
  have hdom : modelLog ≤ preparedFiniteScheduleLocalPhysical q nX count 0 Pk :=
    preparedScalarFiniteScheduleLocalPhysical_model q nX count degree Cdetect G hsource hmodel
  refine ⟨hinv.trans (Real.exp_le_exp.mpr (?_)), hhalf, hdim⟩
  exact (preparedFiniteForwardWork_cubic_lower A constants stage hp hA hseed).trans hdom

theorem preparedScalarFiniteScheduleLocalPhysical_nested_exp_trim
    (q nX count degree Cdetect A stage innerDepth outer : ℕ)
    (G : Type*) [Fintype G] (constants : ℕ → ℕ)
    {p Bstruct sourceU : ℝ}
    (hp : 2 ≤ p) (hX : (nX : ℝ) ≤ p) (hA : 3 ≤ A)
    (hB : p ≤ Bstruct) (hsource : 0 ≤ sourceU) :
    let seed := candidateNestedForwardSeed A constants innerDepth outer Bstruct
    let modelLog := preparedFiniteForwardWork A constants stage seed
    let pDetect := allocatedModelTestLog sourceU modelLog
    let gain := slicedDetectionGainLog degree Cdetect count pDetect pDetect
      (2 * sourceU + 4 * modelLog + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G (gain + pDetect + 4)
    let τ := unconditionedSpatialTrimFraction nX (Real.exp (-p))
    τ⁻¹ ≤ Real.exp (preparedFiniteScheduleLocalPhysical q nX count 0 Pk) ∧
      τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 := by
  apply preparedScalarFiniteScheduleLocalPhysical_exp_trim
    q nX count degree Cdetect A stage G constants hp hX hA
  · exact hB.trans (le_candidateNestedForwardSeed A constants innerDepth outer
      (by omega) (by linarith))
  · exact hsource

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarNestedPowerDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteNestedForwardFixedCenterThreshold_bounds
    {outerDepth innerDepth cutoff : ℕ} (A Cdirect : ℕ) (constants : ℕ → ℕ)
    {x gainLog stageLog : ℝ} (hA : 2 ≤ A) (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
    let seed := preparedFiniteNestedForwardAllDegreeSeed A constants x k
    let sourceU := preparedFiniteForwardPairedSourcePrecision A Cdirect constants k.2.1.val
      k.2.2.2 seed gainLog stageLog
    let work := preparedFiniteForwardWork A constants k.2.1.val seed
    let α := preparedFiniteNestedForwardFixedCenterThreshold A constants x gainLog stageLog k
    0 < α ∧ Real.exp (-(2 * sourceU + 4 * work + 7)) ≤ α / 2 ∧
      α / 2 ≤ 1 ∧ α ≤ Real.exp (-gainLog) / 2 := by
  intro seed sourceU work α
  have hseed : x ≤ seed := le_preparedFiniteNestedForwardAllDegreeSeed A constants hA hx k
  have hseed0 : 0 ≤ seed := hx.trans hseed
  have hg' : gainLog ∈ Set.Icc 0 seed := ⟨hg.1, hg.2.trans hseed⟩
  have hs' : stageLog ∈ Set.Icc 0 seed := ⟨hs.1, hs.2.trans hseed⟩
  exact ⟨Real.exp_pos _,
    preparedFiniteForwardFixedCenterThreshold_lower A Cdirect constants k.2.1.val k.2.2.2
      hseed0 hg' hs',
    preparedFiniteForwardFixedCenterThreshold_half_le_one A constants k.2.1.val hseed0 hg' hs',
    preparedFiniteForwardInnerDetectionThreshold_bound A constants k.2.1.val hseed0 hg' hs'⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteNestedForwardScalarBounds
    {outerDepth innerDepth cutoff : ℕ} (A Cdirect Cslice : ℕ)
    (constants : ℕ → ℕ) (count : ℕ) {x gainLog stageLog : ℝ}
    (hA : 2 ≤ A) (hSlice : Cslice + 1 ≤ A)
    (hx : 0 ≤ x) (hcount : (count : ℝ) ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    ∀ k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff,
    let seed := preparedFiniteNestedForwardAllDegreeSeed A constants x k
    let sourceU := preparedFiniteForwardPairedSourcePrecision A Cdirect constants k.2.1.val
      k.2.2.2 seed gainLog stageLog
    let work := preparedFiniteForwardWork A constants k.2.1.val seed
    let sliceLog := (preparedFiniteForwardParameter A constants k.2.1.val seed + Cslice) ^ Cslice
    let α := preparedFiniteNestedForwardFixedCenterThreshold A constants x gainLog stageLog k
    0 ≤ sourceU ∧ 0 ≤ work ∧ sliceLog ≤ work ∧ (count : ℝ) ≤ Real.exp work ∧
      Real.exp (-(2 * sourceU + 4 * work + 7)) ≤ α / 2 ∧ α / 2 ≤ 1 ∧
      (count : ℝ) ≤ (preparedFiniteForwardDetectorPolynomial cutoff).eval₂
        (Nat.castRingHom ℝ) (allocatedModelTestLog sourceU work) := by
  intro k seed sourceU work sliceLog α
  have hseed : x ≤ seed := le_preparedFiniteNestedForwardAllDegreeSeed A constants hA hx k
  have hseed0 : 0 ≤ seed := hx.trans hseed
  have hg' : gainLog ∈ Set.Icc 0 seed := ⟨hg.1, hg.2.trans hseed⟩
  have hs' : stageLog ∈ Set.Icc 0 seed := ⟨hs.1, hs.2.trans hseed⟩
  have hcountSeed : (count : ℝ) ≤ seed := hcount.trans hseed
  have hu : 0 ≤ sourceU := preparedFiniteForwardPairedSourcePrecision_nonneg
    A Cdirect constants k.2.1.val k.2.2.2 hseed0 hg' hs'
  have hscalar := preparedFiniteForward_model_scalar_bounds A constants k.2.1.val count
    hA hseed0 hcountSeed
  have hslice := preparedFiniteForward_controlled_slice_bounds A Cslice constants k.2.1.val
    count hA hSlice hseed0 hcountSeed
  have hthreshold := preparedFiniteNestedForwardFixedCenterThreshold_bounds
    A Cdirect constants hA hx hg hs k
  have hcountWork : (count : ℝ) ≤ work :=
    hcountSeed.trans ((le_preparedFiniteForwardParameter A constants k.2.1.val hseed0).trans
      hscalar.2.1)
  exact ⟨hu, hscalar.1, hslice.2.1, hscalar.2.2.1,
    hthreshold.2.1, hthreshold.2.2.1,
    hcountWork.trans (preparedFiniteForwardDetectorPolynomial_bounds cutoff hu hscalar.1).1⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

namespace AllocatedExternalCandidateSampler
variable {s nX : ℕ}
    {I₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
    {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
    {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
    {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
    {R₀ σ₀ : Fin 0 → ℝ}
    {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
    {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
    {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
    {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
    {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
    {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
    {τ ξ₀ : ℝ}
    {center₀ : CoefficientTorus (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]

theorem nativeDetection_of_preparedScalarNestedSchedule_s2_oai
    (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
      N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀)
    (outerDepth innerDepth exponent Cslice Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct gainLog stageLog extraLate p : ℝ)
    (hA : 3 ≤ exponent) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hnum : (scalarNativeDimension s : ℝ) ≤ Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (hp : 2 ≤ p) (hX : (nX : ℝ) ≤ p) (hpB : p ≤ Bstruct)
    (htrim : τ = unconditionedSpatialTrimFraction nX (Real.exp (-p))) :
    let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s
    let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
    let stage : K → ℕ := fun k => (preparedFiniteNestedForwardAllDegreeStage k).val
    let direct : K → Bool := preparedFiniteNestedForwardAllDegreeIsDirect
    let seed : K → ℝ := preparedFiniteNestedForwardAllDegreeSeed exponent constants Bstruct
    let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision exponent Cdirect
      constants (stage k) (direct k) (seed k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork exponent constants (stage k) (seed k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter exponent constants (stage k) (seed k) + Cslice) ^ Cslice
    let α := preparedFiniteNestedForwardFixedCenterThreshold exponent constants Bstruct gainLog stageLog
    let Pdetect := preparedFiniteForwardDetectorPolynomial s
    let q := max s 1
    let count := scalarNativeDimension s
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let pRadius := allocatedCommonProductRadiusLog q Bstruct Bstruct
    let D := allocatedComparisonDimension q (count : ℝ)
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun k => slicedDetectionGainLog (degree k) (Cdetect k)
      count (pDetect k) (pDetect k) (aDetect k)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1))
      (Fin (scalarNativeDimension s)) (detectionGain k + pDetect k + 4)
    let Pphysical := fun k => preparedFiniteScheduleLocalPhysical q nX count 0 (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun k => target k + D * ((q * 2 ^ (q + 1) : ℕ) * Pk k) + 5
    let Prho := fun k => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
    let Ptail := fun k => affineProfileToleranceEnvelope q D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail 0
    let Tmod := fun k => ((q + 1 : ℕ) : ℝ) * Pk k + nX * 0
    let lengthLogs := fun k => allocatedAffineLengthLog q D Pscale (Prho k) (Pk k)
      (target k) (pDetect k + 2) (Tmod k)
    let Pmaster := fun k => preparedFiniteScheduleLocalMaster Bstruct D pRadius 0
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain 0
    let localLate := fun k => preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget extraLate
    let Plate := ∑ k, localLate k
    let detectorRequired := fun k : K =>
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q (degree k))
        (degree k + 1) (Pmaster k) Plate).required
    let scaleFloor := max (((probabilityProfileLipschitz : ℝ) + 8) + (D + 4) + pRadius + Pscale)
      (∑ k : K, max 0 (lengthLogs k))
    let spatialFloor := preparedFiniteNestedSourceRequired exponent constants innerDepth outerDepth s
      Bstruct 0 0 detectorRequired
    Real.exp scaleFloor ≤ S₀.value →
    (S₀.value : ℝ) ≤ Real.exp extraLate →
    (∀ i, Real.exp spatialFloor ≤ (N i : ℝ)) →
    ∀ k : K, A₀.NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedFiniteNestedSourceNative q (Fin (scalarNativeDimension s)) count nX Pdetect
        exponent Cdirect constants Bstruct count 0 gainLog stageLog Plate k) (α k) := by
  intro K degree stage direct seed sourceU modelLog sliceLog α Pdetect q count Cdetect
    pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pmaster coarseTarget localLate Plate detectorRequired scaleFloor spatialFloor
    hscale hSupper hsize
  have hB : 0 ≤ Bstruct := by linarith
  have hA2 : 2 ≤ exponent := by omega
  have hscalar := preparedFiniteNestedForwardScalarBounds
    (outerDepth := outerDepth) (innerDepth := innerDepth) (cutoff := s) exponent Cdirect Cslice constants
    count hA2 hSliceExponent hB hnum hg hs
  have hu (k : K) : 0 ≤ sourceU k := (hscalar k).1
  have hw (k : K) : 0 ≤ modelLog k := (hscalar k).2.1
  have hslice (k : K) : sliceLog k ≤ modelLog k := (hscalar k).2.2.1
  have hcount (k : K) : (count : ℝ) ≤ Real.exp (modelLog k) := (hscalar k).2.2.2.1
  have hαLower (k : K) : Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2 :=
    (hscalar k).2.2.2.2.1
  have hαHalf (k : K) : α k / 2 ≤ 1 := (hscalar k).2.2.2.2.2.1
  have hdimension (k : K) : (count : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)) :=
    (hscalar k).2.2.2.2.2.2
  have hlength (k : K) : Real.exp (lengthLogs k) ≤ S₀.value := by
    apply le_trans (Real.exp_le_exp.mpr (?_)) hscale
    exact (le_max_right 0 (lengthLogs k)).trans
      ((Finset.single_le_sum (fun _ _ => le_max_left (0 : ℝ) _) (Finset.mem_univ k)).trans
        (le_max_right _ _))
  have hwidth : Real.exp (((probabilityProfileLipschitz : ℝ) + 8) + (D + 4) + pRadius + Pscale) ≤
      S₀.value := (Real.exp_le_exp.mpr (le_max_left _ _)).trans hscale
  have hsizeEach (k : K) (i) : Real.exp (detectorRequired k) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (detectorRequired_le_preparedFiniteNestedSourceRequired exponent
      constants innerDepth outerDepth s Bstruct 0 0 detectorRequired k)).trans (hsize i)
  have htrimBounds (k : K) : τ⁻¹ ≤ Real.exp (Pphysical k) ∧
      τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 := by
    rw [htrim]
    exact preparedScalarFiniteScheduleLocalPhysical_nested_exp_trim q nX count (degree k)
      (Cdetect k) exponent (stage k) innerDepth k.1.val (Fin (scalarNativeDimension s))
      constants hp hX hA hpB (hu k)
  let anchor : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth s
  have hdetect : ∀ k : K, A₀.NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) :=
    A₀.nativeDetection_of_preparedScalarFiniteSchedule degree
      (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_refl s))
      Pdetect Bstruct extraLate sourceU modelLog sliceLog α hB hnum hu hw hslice hcount
      hαLower hαHalf hprofile hcutoff hdimension hlength hwidth hSupper hsizeEach
      (fun k => (htrimBounds k).1) (htrimBounds anchor).2.1 (htrimBounds anchor).2.2
  intro k
  exact @hdetect k

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_preparedScalarNestedSchedule_s2_oai := @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_preparedScalarNestedSchedule_s2_oai
