-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleProductiveFixedCenterSource_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T08:34:34.898171+00:00
-- url     : https://prove2.me/submissions/8eb5982e-a1d9-46bd-b9b4-05f4455bc2a0

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285
import Definitions.Def_OAIE3v2B290

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.JointProductiveMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ x, Measurable (fun c => (law c).weight x))

include hweight

omit μ law hweight in
theorem centeredFinite_finite_event_measurable (F : C → Finset Ω)
    (hF : ∀ x, MeasurableSet {c | x ∈ F c}) :
    MeasurableSet {z : C × Ω | z.2 ∈ F z.1} := by
  have hm : Measurable (fun z : C × Ω => if z.2 ∈ F z.1 then (1 : ℝ) else 0) :=
    measurable_from_prod_countable_left
      (fun x => measurable_const.ite (hF x) measurable_const)
  have he : {z : C × Ω | z.2 ∈ F z.1} =
      (fun z : C × Ω => if z.2 ∈ F z.1 then (1 : ℝ) else 0) ⁻¹' {1} := by
    ext z
    by_cases hz : z.2 ∈ F z.1 <;> simp [hz]
  rw [he]
  exact hm (measurableSet_singleton 1)

theorem centeredFiniteProbabilityMeasure_real_finite_events [IsProbabilityMeasure μ]
    (F : C → Finset Ω) (hevent : MeasurableSet {z : C × Ω | z.2 ∈ F z.1}) :
    (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ F z.1} =
      ∫ c, (law c).mass (F c) ∂μ := by
  have h := centeredFiniteProbabilityMeasure_real_event μ law hweight _ hevent
  refine h.trans (integral_congr_ae (ae_of_all μ (fun c => ?_)))
  calc
    _ = (law c).mean (fun x => if x ∈ F c then 1 else 0) := by
      apply congrArg (law c).mean
      funext x
      by_cases hx : x ∈ F c <;> simp [hx]
    _ = _ := (law c).mean_indicator (F c)

theorem centeredFiniteProbabilityMeasure_real_finite_events_of_measurable_membership
    [IsProbabilityMeasure μ] (F : C → Finset Ω)
    (hF : ∀ x, MeasurableSet {c | x ∈ F c}) :
    (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ F z.1} =
      ∫ c, (law c).mass (F c) ∂μ :=
  centeredFiniteProbabilityMeasure_real_finite_events μ law hweight F
    (centeredFinite_finite_event_measurable F hF)

omit μ [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_mass_measurable (F : C → Finset Ω)
    (hF : ∀ x, MeasurableSet {c | x ∈ F c}) :
    Measurable (fun c => (law c).mass (F c)) := by
  have h := centeredFinite_mean_measurable law hweight
    (fun c x => if x ∈ F c then 1 else 0)
    (fun x => measurable_const.ite (hF x) measurable_const)
  simpa only [FiniteProbabilityWeights.mean_indicator] using h

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_mass_integrable [IsFiniteMeasure μ] (F : C → Finset Ω)
    (hF : ∀ x, MeasurableSet {c | x ∈ F c}) :
    Integrable (fun c => (law c).mass (F c)) μ := by
  apply Integrable.of_bound (centeredFinite_mass_measurable law hweight F hF).aestronglyMeasurable 1
  exact ae_of_all μ (fun c => by
    rw [Real.norm_of_nonneg ((law c).mass_nonneg (F c))]
    exact (law c).mass_le_one (F c))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

omit [Fintype X] [∀ j, Fintype (J j)] in
theorem preparedModularGeneralCentered_degree
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) (c : ∀ j, U j) :
    ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (subtractConstant (c j).val (poly j)) :=
  fun j => (hp j).subtractConstant (c j).val

omit [Fintype X] in
theorem preparedModularGeneralCentered_rank (T : X → ℝ) (rank : ℝ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) T rank (U j) (poly j)) (c : ∀ j, U j) :
    ∀ j, HasLayerSamplingRank (j.val + 1) T rank (U j)
      (subtractConstant (c j).val (poly j)) :=
  fun j => (hasLayerSamplingRank_subtractConstant_iff (Nat.succ_pos j.val)
    T rank (U j) (c j).val (poly j)).mpr (hrank j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllSiteLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

omit [Fintype X] in

theorem allocatedExternalCandidateWidths_eq (N : X → ℕ) (τ ξ : ℝ) :
    allocatedExternalCandidateWidths B U b S N τ ξ =
      narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N := by
  rw [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSamplerFamily

variable (A : AllocatedExternalCandidateSamplerFamily B U b S hb o hR hσ N poly hm τ ξ stride cells)

private theorem good_of_parameters
    (Good : ∀ (V : (Option (LayerSamplerVariables G I n B) × X → ℝ)) (bases : Finset (X → ℤ)),
      ((CoefficientTorus (K := LayerSamplerVariables G I n B) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 V 1)) → Prop)
    (V : (Option (LayerSamplerVariables G I n B) × X → ℝ)) (bases : Finset (X → ℤ))
    (hV : (allocatedExternalCandidateWidths B U b S N τ ξ) = V) (hBases : (A 0).bases = bases)
    (hbases : bases.Nonempty) (hwidth : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (hcenter : ∀ center : (CoefficientTorus (K := LayerSamplerVariables G I n B) U), 0 < selectedJointDensityMass bases stride cells V ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center))
    (hGood : Good V bases (fun center => selectedJointFiniteLaw bases hbases stride cells V hwidth hmass
      ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center) ((allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) center) (hcenter center))) :
    Good (allocatedExternalCandidateWidths B U b S N τ ξ) (A 0).bases A.law := by
  subst V
  subst bases
  exact hGood

variable [sourceDecidableEq : DecidableEq X]

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in

theorem bases_eq_prepared : (A 0).bases = trimmedIntegerBox N (spatialTrimMargin τ N) := by
  change @trimmedIntegerBox X _ (Classical.decEq X) N (spatialTrimMargin τ N) = _
  rw [show Classical.decEq X = sourceDecidableEq from Subsingleton.elim _ _]

variable
    (hbases : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty)
    (hwidth : ∀ z, 0 < (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) z)
    (hcenter : ∀ center : (CoefficientTorus (K := LayerSamplerVariables G I n B) U),
      0 < selectedJointDensityMass (trimmedIntegerBox N (spatialTrimMargin τ N))
        stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center))

theorem good_of_prepared
    (Good : ∀ (V : (Option (LayerSamplerVariables G I n B) × X → ℝ)) (bases : Finset (X → ℤ)),
      ((CoefficientTorus (K := LayerSamplerVariables G I n B) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 V 1)) → Prop)
    (hGood : Good (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) (trimmedIntegerBox N (spatialTrimMargin τ N)) (fun center => selectedJointFiniteLaw
  (trimmedIntegerBox N (spatialTrimMargin τ N)) hbases stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) hwidth hmass
  ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center) ((allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) center) (hcenter center))) :
    Good (allocatedExternalCandidateWidths B U b S N τ ξ) (A 0).bases A.law :=
  A.good_of_parameters Good _ _ (allocatedExternalCandidateWidths_eq B U b S N τ ξ)
    A.bases_eq_prepared hbases hwidth hmass hcenter hGood

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem measurable_good_of_prepared
    (Good : ∀ (V : (Option (LayerSamplerVariables G I n B) × X → ℝ)) (bases : Finset (X → ℤ)),
      ((CoefficientTorus (K := LayerSamplerVariables G I n B) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 V 1)) → Prop)
    (hweight : ∀ z, Measurable (fun center => ((fun center => selectedJointFiniteLaw
  (trimmedIntegerBox N (spatialTrimMargin τ N)) hbases stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) hwidth hmass
  ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center) ((allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) center) (hcenter center)) center).weight z))
    (hGood : Good (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) (trimmedIntegerBox N (spatialTrimMargin τ N)) (fun center => selectedJointFiniteLaw
  (trimmedIntegerBox N (spatialTrimMargin τ N)) hbases stride cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) hwidth hmass
  ((allocatedCenteredJointDensity B U b hb o hR hσ S poly hm) center) ((allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) center) (hcenter center))) :
    (∀ z, Measurable (fun center => (A.law center).weight z)) ∧
      Good (allocatedExternalCandidateWidths B U b S N τ ξ) (A 0).bases A.law := by
  exact A.good_of_prepared hbases hwidth hmass hcenter
    (fun V bases law => (∀ z, Measurable (fun center => (law center).weight z)) ∧ Good V bases law)
    ⟨hweight, hGood⟩

end AllocatedExternalCandidateSamplerFamily
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem allocatedExternalConditionalExcessExponent_spec (m : ℕ) :
    2 ≤ allocatedExternalConditionalExcessExponent m ∧
      AllocatedCenteredNarrowPrescribedMarginalPointwiseStatement.{0,0,0,0,0,0}
        m (allocatedExternalConditionalExcessExponent m) :=
  (exists_allocated_centered_narrow_prescribed_marginal_pointwise.{0,0,0,0,0,0} m).choose_spec

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateFixedCenterExcess
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
    {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}

namespace AllocatedExternalCandidateSampler

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem fixedCenter_excess
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (A : AllocatedExternalCandidateSampler B U basis S hb o hR hσ N poly hm τ ξ stride cells center)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hσ1 : ∀ j, σ j ≤ 1) (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (hP : 0 ≤ P) (hmSize : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hsP : ∀ x, (stride x : ℝ) ≤ Real.exp P)
    (hWP : allocatedExternalCandidateRootBudget B U basis S ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) (hτhalf : τ ≤ 1 / 2)
    (hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (hsize : ∀ x, Real.exp ((max P E + allocatedExternalConditionalExcessExponent m) ^
      allocatedExternalConditionalExcessExponent m) ≤ (N x : ℝ))
    {rank : ℝ}
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) rank (U j) (poly j))
    (hRank : Real.exp ((max P E + allocatedExternalConditionalExcessExponent m) ^
      allocatedExternalConditionalExcessExponent m) ≤ rank)
    (hCells : cells.Nonempty)
    (hbox : (integerBox N).Nonempty)
    (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x) :
      letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        (A.law.siteLaw (A.physicalBox hξ1 hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy E := by
  obtain ⟨_hN, _hbases, _hbox', _hmass, _hmargin', _hnormalizer, hsite⟩ :=
    (allocatedExternalConditionalExcessExponent_spec m).2 B U basis S hb o μ ν
      hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall hP hmSize hK hX hdim
      hRP hσP hcount hI hn hJ hAP hLP hCP hVP poly hp hm stride A.stride_pos hsP
      (allocatedExternalCandidateRootBudget_nonneg B U basis S) hWP
      A.trim_pos hτP hτhalf hτdim A.narrow_pos hξ1 hξP N hsize hrank hRank cells hCells
  let : Nonempty A.Site := A.site_nonempty
  exact hsite (fun t : A.Site => t.val)
    (fun t k => (allocatedParameterSite_bound B U basis S t k).trans hLP)
    (fun t => (allocatedParameterSite_sum_bound B U basis S t).trans_eq
      (allocatedExternalCandidateRootBudget_eq B U basis S).symm) center

end AllocatedExternalCandidateSampler

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))

include hweight

theorem centeredFiniteProbabilityMeasure_ae_centers [SFinite μ]
    (P : C × Ω → Prop)
    (hP : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, P z) :
    ∀ᵐ c ∂μ, ∀ x, 0 < (law c).weight x → P (c, x) := by
  have hprod := (ae_withDensity_iff
    (centeredFiniteWeightDensity_measurable law hweight).ennreal_ofReal).mp hP
  apply (Measure.ae_ae_of_ae_prod hprod).mono
  intro c hc x hx
  exact (Measure.ae_count_iff.mp hc) x (ne_of_gt (ENNReal.ofReal_pos.mpr hx))

theorem exists_center_with_good_mass [IsProbabilityMeasure μ]
    (F : C → Finset Ω) (hF : ∀ x, MeasurableSet {c | x ∈ F c})
    (P : C × Ω → Prop)
    (hP : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, P z)
    {δ : ℝ} (hδ : 0 < δ)
    (hmass : δ ≤ (centeredFiniteProbabilityMeasure μ law).real {z | z.2 ∈ F z.1}) :
    ∃ c, δ / 2 < (law c).mass (F c) ∧
      ∀ x, 0 < (law c).weight x → P (c, x) := by
  have hPc := centeredFiniteProbabilityMeasure_ae_centers μ law hweight P hP
  have hint := centeredFinite_mass_integrable μ law hweight F hF
  rw [centeredFiniteProbabilityMeasure_real_finite_events_of_measurable_membership
    μ law hweight F hF] at hmass
  by_contra h
  have hbound : ∀ᵐ c ∂μ, (law c).mass (F c) ≤ δ / 2 := by
    filter_upwards [hPc] with c hc
    by_contra hgt
    exact h ⟨c, lt_of_not_ge hgt, hc⟩
  have hi := integral_mono_ae hint (integrable_const (δ / 2)) hbound
  rw [integral_const] at hi
  simp only [probReal_univ, smul_eq_mul, one_mul] at hi
  linarith

theorem exists_center_finite_good_event [IsProbabilityMeasure μ]
    (event : Set (C × Ω)) (hevent : MeasurableSet event)
    (P : C × Ω → Prop)
    (hP : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, P z)
    {δ : ℝ} (hδ : 0 < δ)
    (hmass : δ ≤ (centeredFiniteProbabilityMeasure μ law).real event) :
    ∃ (c : C) (G : Finset Ω), δ / 2 < (law c).mass G ∧
      ∀ x ∈ G, (c, x) ∈ event ∧ 0 < (law c).weight x ∧ P (c, x) := by
  classical
  let F : C → Finset Ω := fun c => Finset.univ.filter (fun x => (c, x) ∈ event)
  have hF (x : Ω) : MeasurableSet {c | x ∈ F c} := by
    simpa only [F, Finset.mem_filter, Finset.mem_univ, true_and, Set.preimage, id_eq] using
      hevent.preimage (measurable_id.prodMk (measurable_const (a := x)))
  have heq : {z : C × Ω | z.2 ∈ F z.1} = event := by
    ext z
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Prod.mk.eta]
  obtain ⟨c, hc, hPc⟩ := exists_center_with_good_mass μ law hweight F hF P hP hδ
    (by simpa only [heq] using hmass)
  let G := (F c).filter (fun x => 0 < (law c).weight x)
  have hG : (law c).mass G = (law c).mass (F c) := by
    unfold FiniteProbabilityWeights.mass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hw : 0 < (law c).weight x
    · simp only [hw, ite_true]
    · simp only [hw, ite_false]
      exact (le_antisymm (le_of_not_gt hw) ((law c).nonneg x)).symm
  refine ⟨c, G, by rwa [hG], ?_⟩
  intro x hx
  obtain ⟨hxF, hxpos⟩ := Finset.mem_filter.mp hx
  exact ⟨(Finset.mem_filter.mp hxF).2, hxpos, hPc x hxpos⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem exists_center_finite_productive_good_event_avoiding_residual
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (A : Set (C × Ω)) (hA : MeasurableSet A)
    (bad : Set (C × Ω)) (hbad : MeasurableSet bad)
    (residual : Set (C × Ω)) (hResidual : MeasurableSet residual)
    (P : C × Ω → Prop)
    (hP : ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, P z)
    {gain : ℝ} (hgain : 0 < gain)
    (hAmass : gain / 4 ≤ (centeredFiniteProbabilityMeasure μ law).real A)
    (hbadmass : (centeredFiniteProbabilityMeasure μ law).real bad ≤ gain / 16)
    (hResidualMass : (centeredFiniteProbabilityMeasure μ law).real residual ≤ gain / 32) :
    ∃ (c : C) (G : Finset Ω), gain / 16 < (law c).mass G ∧
      ∀ x ∈ G, (c, x) ∈ A ∧ (c, x) ∉ bad ∧ (c, x) ∉ residual ∧
        0 < (law c).weight x ∧ P (c, x) := by
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  have hunion : (centeredFiniteProbabilityMeasure μ law).real (bad ∪ residual) ≤
      gain / 16 + gain / 32 :=
    (measureReal_union_le bad residual).trans (add_le_add hbadmass hResidualMass)
  have hdiff := le_measureReal_sdiff
    (μ := centeredFiniteProbabilityMeasure μ law) (s₁ := A) (s₂ := bad ∪ residual)
  have hmass : 5 * gain / 32 ≤
      (centeredFiniteProbabilityMeasure μ law).real (A \ (bad ∪ residual)) := by
    linarith only [hAmass, hunion, hdiff]
  obtain ⟨c, G, hG, hgood⟩ := exists_center_finite_good_event μ law hweight
    (A \ (bad ∪ residual)) (hA.diff (hbad.union hResidual)) P hP
    (by positivity : 0 < 5 * gain / 32) hmass
  refine ⟨c, G, by linarith only [hG, hgain], ?_⟩
  intro x hx
  obtain ⟨⟨hAx, hnotunion⟩, hpos, hPx⟩ := hgood x hx
  exact ⟨hAx, (fun hb => hnotunion (Or.inl hb)),
    (fun hr => hnotunion (Or.inr hr)), hpos, hPx⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredStagedModelProductiveGood
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem preparedCenteredProductive_event
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    {nX : ℕ} (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j)
    (N : Fin nX → ℕ)
    (widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)) (gainLog : ℝ)
    (law : CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 widths 1))
    (hproductive : PreparedCenteredForecastProductiveConclusion B U basis S hb o hR hσ
      μ poly hm N widths bases gainLog law)
    (test : (Fin nX → ℝ) → ℝ) (htest : ∀ x, |test x| ≤ 1)
    (gain : ℝ) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) |
        AllocatedPathProductivity B U basis S N widths bases test gain z.2} ∧
      gain / 4 ≤ joint.real {z | AllocatedPathProductivity B U basis S N widths bases test gain z.2} ∧
      ∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun a => c a.1))) ∧
        allocatedAffineDensity B U basis hb o hR hσ S poly hm c
          (fun k v => (jointIntegerFrame (z.2.1.val, z.2.2.val) k v : ℝ)) ≠ 0 := by
  intro joint
  obtain ⟨hprob, hmeas, hmass, hnonzero, hphysical⟩ :=
    hproductive test htest gain hgain hmean
  let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
  let Sites := integerBox sides
  let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
    Function.Injective (fun q : Sites => jointIntegerPhysicalSite q.val (z.1.val, z.2.val)) ∧
      gain / 2 ≤ 𝔼 q : Sites, test
        (fun i => (jointIntegerPhysicalSite q.val (z.1.val, z.2.val) i : ℝ)))
  have hevent :
      {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
          (bases × rectangularWeightIndices 0 widths 1) |
        AllocatedPathProductivity B U basis S N widths bases test gain z.2} =
      {z | z.2 ∈ productive} := by
    ext z
    simp only [Set.mem_ofPred_eq, AllocatedPathProductivity, productive,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hinj, hscore, _⟩
      exact ⟨hinj, hscore⟩
    · rintro ⟨hinj, hscore⟩
      exact ⟨hinj, hscore, hphysical z.2⟩
  exact ⟨hprob, hevent.symm ▸ hmeas, hevent.symm ▸ hmass, hnonzero⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem preparedCenteredFiniteProductiveGood
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    [IsProbabilityMeasure μ]
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law)
    (hproductive : PreparedCenteredForecastProductiveConclusion (nX := nX) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S
      hb o hR hσ μ poly hm N width bases gainLog law)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    PreparedCenteredFiniteProductiveGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test := by
  classical
  unfold PreparedCenteredFiniteProductiveGoodConclusion
  obtain ⟨c, hc, hcenter, sample, read, hread, hbad⟩ := hgood
  refine ⟨c, hc, hcenter, sample, read, hread, ?_⟩
  intro primes hprime depth hdepth residual hResidual hResidualMass Extra hExtra
  obtain ⟨bad, hbadMeas, hbadMass, hgoodAE⟩ := hbad primes hprime depth hdepth
  obtain ⟨hprob, hproductiveMeas, hproductiveMass, hnonzero⟩ :=
    preparedCenteredProductive_event (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hb o hR hσ
      μ poly hm N width bases gainLog law hproductive test htest gain hgain hmean
  have hgainPos : 0 < gain := (Real.exp_pos _).trans_le hgain
  have hbadMass' : (centeredFiniteProbabilityMeasure μ law).real bad ≤ gain / 16 := by
    linarith only [hbadMass]
  have hAE := hgoodAE.and (hnonzero.and hExtra)
  have hsel := exists_center_finite_productive_good_event_avoiding_residual μ law hweight
  have hsel := hsel _ hproductiveMeas bad hbadMeas residual hResidual
  have hsel := hsel _ hAE hgainPos
  obtain ⟨center, F, hmass, hF⟩ := hsel hproductiveMass hbadMass' hResidualMass
  refine ⟨center, F, hmass, ?_⟩
  intro z hz
  obtain ⟨hzprod, hzbad, hzresidual, hzweight, hzgood, hzdensity, hzextra⟩ := hF z hz
  have hRecovered := hzgood hzbad
  exact ⟨hzweight, hzresidual, hzextra, hzprod, hzdensity, hRecovered⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem preparedCenteredProductiveGoodCenter
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    [IsProbabilityMeasure μ]
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law)
    (hproductive : PreparedCenteredForecastProductiveConclusion (nX := nX) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S
      hb o hR hσ μ poly hm N width bases gainLog law)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    PreparedCenteredProductiveGoodCenterConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test := by
  classical
  have hselected := preparedCenteredFiniteProductiveGood (m := m) (nX := nX) (M := M)
    prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test
    hweight hgood hproductive htest hgain hmean
  unfold PreparedCenteredProductiveGoodCenterConclusion
  obtain ⟨c, hc, hcenter, sample, read, hread, hfinite⟩ := hselected
  refine ⟨c, hc, hcenter, sample, read, hread, ?_⟩
  intro primes hprime depth hdepth
  have hgainNonneg : 0 ≤ gain := (Real.exp_nonneg _).trans hgain
  obtain ⟨center, F, hmass, hF⟩ :=
    hfinite primes hprime depth hdepth ∅ MeasurableSet.empty
      (by simpa using (div_nonneg hgainNonneg (by norm_num : (0 : ℝ) ≤ 32)))
      (fun _ => True) (ae_of_all _ (fun _ => True.intro))
  refine ⟨center, F, hmass, ?_⟩
  intro z hz
  obtain ⟨hpos, _, _, hprod, hdensity, hrec, hmod, hdet⟩ := hF z hz
  exact ⟨hpos, hprod, hdensity, hrec, hmod, hdet⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedFullChartConditionalNativeDetectionSharedWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (α τ : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

include hR hσ hb o in

theorem preparedModularGeneralConditionalDetectionFreeTrimSharedWidth_of_direct
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    PreparedModularGeneralConditionalDetectionFreeTrimSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff hτSpatial hτInv hτHalf hτDim
    r W ξn hξn hξn_le hξLate hW cells poly hp hmem Rrank hsize hrank hRank V hCells bases Z
  have hprimitive := hDirect hstride hstrideBound C hC hCbound hchart Cforward hforward
    hForward hVtail hVactual hprofile hcutoff hτSpatial hτInv hτHalf hτDim
      hξn hξn_le hξLate
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, _⟩ :=
    hprimitive cells poly hp hmem hsize hrank hRank hCells
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path
  have hcenter (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
      let Zc := selectedJointDensityMass bases stride cells V
        (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      |Zc - 1| ≤ Real.exp (-r.E) ∧ Zc ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
        0 < Zc ∧ Zc⁻¹ ≤ 2 := by
    obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
    let pc := fun j => subtractConstant (c j).val (poly j)
    let hmc := fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)
    obtain ⟨_, _, _, _, hnormc, _, _⟩ := hprimitive cells pc
      (preparedModularGeneralCentered_degree U poly hp c) hmc hsize
      (preparedModularGeneralCentered_rank U poly (fun i => (N i : ℝ)) Rrank hrank c)
      hRank hCells
    have hdensity := allocatedJointBaseDensity_subtractConstant_centered
      B U basis hb o hR hσ S poly hmem center c hc
    change (fun Zc : ℝ => |Zc - 1| ≤ Real.exp (-r.E) ∧
      Zc ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Zc ∧ Zc⁻¹ ≤ 2)
      (selectedJointDensityMass bases stride cells V
        (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) pc hmc)) at hnormc
    rw [hdensity] at hnormc
    exact hnormc
  refine ⟨hcenter, ?_⟩
  intro centeredLaw
  have hweight (z : Path) : Measurable (fun center => (centeredLaw center).weight z) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem)
      (allocatedCenteredJointDensity_measurable_center B U basis hb o hR hσ S poly hmem)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem) (fun center => (hcenter center).2.2.1) z
  refine ⟨hweight, ?_⟩
  intro center pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices
    cdetect stepdetect Hdetect hstep hboxDetect hdense hdimension hcomplexity hcap budget
    signal hα hsignal hzero hlarge
  have hlargeCenter : α / 2 ≤ sampledSliceSeminorm pathLaw
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((Vdetect z j).eval
        (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal :=
    (by linarith only [hα] : α / 2 ≤ α).trans hlarge
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
  let pc := fun j => subtractConstant (c j).val (poly j)
  let hmc := fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)
  obtain ⟨hNc, hbasesc, hboxc, hmassc, hnormc, hmargin, hdetector⟩ :=
    hprimitive cells pc (preparedModularGeneralCentered_degree U poly hp c) hmc hsize
      (preparedModularGeneralCentered_rank U poly (fun i => (N i : ℝ)) Rrank hrank c)
      hRank hCells
  have hlaw := allocatedOriginalPathLaw_subtractConstant_eq_centered
    B U basis hb o hR hσ S poly hmem N hN hW hτSpatial hξn stride cells hmass bases hbases
    center c hc hnormc.2.2.1 ((hcenter center).2.2.1)
  change α / 2 ≤ sampledSliceSeminorm
    (selectedJointFiniteLaw bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center)
      ((hcenter center).2.2.1))
    (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
    (fun z j t => star ((Vdetect z j).eval
      (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal at hlargeCenter
  rw [← hlaw] at hlargeCenter
  obtain ⟨twistData, Fnative, hNative, hcorrelation⟩ :=
    hdetector Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense
      hdimension hcomplexity hcap signal hsignal hzero hlargeCenter
  refine ⟨twistData.shiftConstant (fun j => (c j).val), Fnative, hNative, ?_⟩
  have heval (t : integerBox N) :
      (twistData.shiftConstant (fun j => (c j).val)).eval N poly t.val =
        twistData.eval N pc t.val :=
    NormalizedPolynomialTwist.eval_shiftConstant twistData (fun j => (c j).val) N poly t.val
  simp_rw [heval]
  exact hcorrelation

end Consumer
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

variable {m s nX : ℕ} {G : Type} [Fintype G] [decG : DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
    (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
    (α τ : ℝ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

local notation "pTest" => Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog u pModel)

theorem exists_allocatedExternalCandidateSamplerFamily_nativeDetection
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hPrepared : PreparedModularGeneralConditionalDetectionFreeTrimSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτ : 0 < τ) (hτInv : τ⁻¹ ≤ Real.exp Pphysical)
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog u pModel) (allocatedModelTestLog u pModel) (α / 2))
      Pphysical coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s)
        (s + 1) Pmaster Plate).required ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s)
        (s + 1) Pmaster Plate).required ≤ Rrank)
    (hCells : cells.Nonempty) (hα : 0 < α)
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pTest) :
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s)
      (s + 1) Pmaster Plate
    ∃ A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells,
      (∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
        let Zc := selectedJointDensityMass
          (trimmedIntegerBox N (spatialTrimMargin τ N)) stride cells
          (allocatedExternalCandidateWidths B U basis S N τ ξ)
          (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
        |Zc - 1| ≤ Real.exp (-r.E) ∧ Zc ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
          0 < Zc ∧ Zc⁻¹ ≤ 2) ∧
      ∀ center, (A center).NativeDetection s pSlice pTest r.nativeBudget α := by
  intro r
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hcenter, hweight, hdetect⟩ :=
    hPrepared hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff hτ hτInv hτHalf hτDim hξ hξSmall hξLate
      cells poly hp hmem hsize hrank hRank hCells
  have hV := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ N hN
  have hD : ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      AllocatedNativeSliceDetection (degree := s) J N hbox poly
        (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S))
        (selectedJointFiniteLaw (trimmedIntegerBox N (spatialTrimMargin τ N)) hbases stride cells
          (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
            (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ N)
          hV hmass
          (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
          (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center)
          (hcenter center).2.2.1)
        (fun z t => jointIntegerPhysicalSite t.val (z.1.val, z.2.val))
        pSlice pTest r.nativeBudget α := by
    intro center Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices origin step length
      hstep hshape hdense hcomplex hnorm signal hsignal hsupp hlarge
    exact hdetect center Ddetect Vdetect slices origin step length hstep hshape hdense
      hdimension hcomplex hnorm signal hα hsignal hsupp hlarge
  clear hdetect hweight hnormalizer
  have hwidth : allocatedExternalCandidateWidths B U basis S N τ ξ =
      narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ N := by
    exact allocatedExternalCandidateWidths_eq B U basis S N τ ξ
  have hdec : (fun a b : Fin nX => Classical.propDecidable (a = b)) =
      instDecidableEqFin nX := Subsingleton.elim _ _
  have hdecG : (fun a b : G => Classical.propDecidable (a = b)) = decG :=
    Subsingleton.elim _ _
  revert hV hbases hbox hmass hcenter hD
  rw [← hdec, ← hdecG, ← hwidth]
  intro hbases hbox hmass hcenter hV hD
  let A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells :=
    fun center => ⟨hN, hτ, hξ, hstride, hbases, hmass, (hcenter center).2.2.1⟩
  refine ⟨A, hcenter, ?_⟩
  exact hD

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedReadyPaddedRelativeInitialization
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem preparedCenteredProductiveGoodCenter_with_ready
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    (Ready : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → Prop)
    (hselected : PreparedCenteredProductiveGoodCenterConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test)
    (hReady : ∀ center, Ready center) :
    PreparedCenteredProductiveGoodCenterReadyConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test Ready := by
  unfold PreparedCenteredProductiveGoodCenterConclusion at hselected
  unfold PreparedCenteredProductiveGoodCenterReadyConclusion
  obtain ⟨c, hc, hcenter, sample, read, hread, hfinite⟩ := hselected
  refine ⟨c, hc, hcenter, sample, read, hread, ?_⟩
  intro primes hprime depth hdepth
  obtain ⟨center, F, hmass, hF⟩ := hfinite primes hprime depth hdepth
  exact ⟨center, F, hReady center, hmass, hF⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedGeometryConditionalExcess
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m nX s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
    {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : Fin nX → ℕ} {poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : Fin nX → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride)}

namespace AllocatedExternalCandidateSamplerFamily

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSamplerFamily.preparedConditionalExcessFinDecidableEq
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem prepared_conditional_excess
    (A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hm τ ξ stride cells)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Cdetect : ℕ}
    {Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice E : ℝ}
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel)
      pRadius (2 * sourceU + 4 * pModel + 7) pGain)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (Cforward Vtail : Fin m → ℝ≥0)
    (hforward : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cforward j * ‖z‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ C j * ‖z‖)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hstrideBound : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hτInv : τ⁻¹ ≤ Real.exp Pphysical) (hτHalf : τ ≤ 1 / 2)
    (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    (hξone : ξ ≤ 1) (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (hsize : ∀ x, Real.exp ((max (4 * (Plate + 8) ^ 2) E +
      allocatedExternalConditionalExcessExponent m) ^ allocatedExternalConditionalExcessExponent m) ≤ (N x : ℝ))
    {rank : ℝ}
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) rank (U j) (poly j))
    (hRank : Real.exp ((max (4 * (Plate + 8) ^ 2) E +
      allocatedExternalConditionalExcessExponent m) ^ allocatedExternalConditionalExcessExponent m) ≤ rank)
    (hCells : cells.Nonempty) (hbox : (integerBox N).Nonempty)
    (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x) :
    ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      letI : Nonempty (A center).Site := (A center).site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        ((A center).law.siteLaw ((A center).physicalBox hξone hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)) ≤
          6 * positiveProjectionAccuracy E := by
  classical
  obtain ⟨⟨geometry⟩, _⟩ := geometryAt
  have hRi (j) : (R j)⁻¹ ≤ Real.exp pRadius := by
    have h := geometry.hK j
    simpa only [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos pRadius).le] using h
  have hbnd := preparedCenteredMarginalProjectionBounds B U basis S o
    scalar.master_nonneg scalar.late geometry.hdimensions scalar.dimension_master
    scalar.ambient_master
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr scalar.radius_master))
    (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr scalar.scale_late)) hSLate
  have hChart := scalar.chart_master.trans hbnd.master_projection
  have hStride := scalar.stride_master.2.trans hbnd.master_projection
  have hPhysical := scalar.physical_master.2.trans hbnd.master_projection
  intro center
  exact (A center).fixedCenter_excess μ ν
    (fun j => (geometry.hσsmall j).trans geometry.htone)
    Cforward Vtail hforward hVactual C hC hchart
    (geometry.hbudgets C hC hCbound).1
    hbnd.Pproj_nonneg hbnd.m_projection hbnd.variables_projection hbnd.X_projection
    hbnd.frame_projection hbnd.Rinv_projection hbnd.σinv_projection
    hbnd.coefficient_projection hbnd.I_projection hbnd.n_projection hbnd.J_projection
    hbnd.profile_projection hbnd.S_projection
    (fun j => (hForward j).trans (Real.exp_le_exp.mpr hChart))
    (fun j => (hVtail j).trans (Real.exp_le_exp.mpr hChart)) hp
    (fun x => (hstrideBound x).trans (Real.exp_le_exp.mpr hStride))
    (by simpa only [allocatedExternalCandidateRootBudget_eq] using hbnd.root_projection)
    (hτInv.trans (Real.exp_le_exp.mpr hPhysical)) hτHalf
    (by simpa only [Fintype.card_fin] using hτDim) hξone
    (hξLate.trans (Real.exp_le_exp.mpr hbnd.late_projection)) hsize hrank hRank
    hCells hbox hmargin

end AllocatedExternalCandidateSamplerFamily
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

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ G)
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem preparedFiniteScheduleLocalCandidateDetection
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget : ℝ) (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτ : 0 < τ) (hτInv : ∀ k, τ⁻¹ ≤ Real.exp (Pphysical k))
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      (Pphysical k) coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : ∀ k, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ Rrank)
    (hCells : cells.Nonempty)
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    (A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells) :
    ∀ k center, (A center).NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) := by
  intro k
  have hDirect := hAvailable k (α k / 2) (hαLower k) (hαHalfOne k)
  have hconditional := preparedModularGeneralConditionalDetectionFreeTrimSharedWidth_of_direct
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection k) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
    (Vtail := Vtail) (α := α k) (τ := τ) (hb := hb) (o := o)
    Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget hDirect
  have hα : 0 < α k := by
    have hhalf := (Real.exp_pos _).trans_le (hαLower k)
    linarith only [hhalf]
  obtain ⟨Ak, _hcenter, hdetect⟩ :=
    exists_allocatedExternalCandidateSamplerFamily_nativeDetection
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (α := α k) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget hconditional
      hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual
      hprofile hcutoff hτ (hτInv k) hτHalf hτDim hξ (hξSmall k) hξLate
      cells poly hp hmem (hsize k) hrank (hRank k) hCells hα (hdimension k)
  have hsame : Ak = A := Subsingleton.elim _ _
  rw [hsame] at hdetect
  exact hdetect

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX : ℕ}
attribute [local instance] OAI.Erdos3.VectorPolynomial.fixedSourceFinDecidableEq
variable {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ G)
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem exists_preparedFiniteScheduleFixedCenterSource
    (kAnchor : Stage)
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget : ℝ) (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Pscale D target Pk Prho pRadius E : ℝ}
    (scalar : PreparedUniformDegreeDirectScalarBounds m (degree kAnchor) nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant (degree kAnchor) Pdetect)
      Pchart Pscale D target Pk Prho Qstride (Pmaster kAnchor) Plate (pGain kAnchor)
      (Pphysical kAnchor) coarseTarget pRadius (sourceU kAnchor) (modelLog kAnchor) (sliceLog kAnchor))
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S (degree kAnchor)
      (sampledSupportedSlicedDetectionConstant (degree kAnchor) Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog (sourceU kAnchor) (modelLog kAnchor))
      pRadius (2 * sourceU kAnchor + 4 * modelLog kAnchor + 7) (pGain kAnchor))
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτ : 0 < τ) (hτInv : ∀ k, τ⁻¹ ≤ Real.exp (Pphysical k))
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      (Pphysical k) coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : ∀ k, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ Rrank)
    (hsizeConditional : ∀ i, Real.exp (preparedConditionalExcessRequired m Plate E) ≤ (N i : ℝ))
    (hRankConditional : Real.exp (preparedConditionalExcessRequired m Plate E) ≤ Rrank)
    (hCells : cells.Nonempty)
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    : ∃ hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i,
    ∃ A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells,
    (∀ k center, (A center).NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
    ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      letI : Nonempty (A center).Site := (A center).site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) (A center).integerBox_nonempty).excessMass
        ((A center).law.siteLaw ((A center).physicalBox
          ((hξSmall kAnchor).trans (min_le_left _ _)) hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)) ≤
          6 * positiveProjectionAccuracy E := by
  have hDirect := hAvailable kAnchor (α kAnchor / 2) (hαLower kAnchor) (hαHalfOne kAnchor)
  have hconditional := preparedModularGeneralConditionalDetectionFreeTrimSharedWidth_of_direct
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection kAnchor) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := sourceU kAnchor) (pModel := modelLog kAnchor) (pSlice := sliceLog kAnchor)
    (Vtail := Vtail) (α := α kAnchor) (τ := τ) (hb := hb) (o := o)
    Pchart Qstride (Pmaster kAnchor) Plate (pGain kAnchor) (Pphysical kAnchor) coarseTarget hDirect
  obtain ⟨_hN, _hbases, _hbox, _hmass, _hnormalizer, hmargin, _hcenter, _hweight, _hdetect⟩ :=
    hconditional hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff hτ (hτInv kAnchor) hτHalf hτDim hξ (hξSmall kAnchor) hξLate
      cells poly hp hmem (hsize kAnchor) hrank (hRank kAnchor) hCells
  have hα : 0 < α kAnchor := by
    have hhalf := (Real.exp_pos _).trans_le (hαLower kAnchor)
    linarith only [hhalf]
  obtain ⟨A, _hcenter, _hdetect⟩ :=
    exists_allocatedExternalCandidateSamplerFamily_nativeDetection
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection kAnchor) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := sourceU kAnchor) (pModel := modelLog kAnchor) (pSlice := sliceLog kAnchor)
      (Vtail := Vtail) (α := α kAnchor) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster kAnchor) Plate (pGain kAnchor) (Pphysical kAnchor) coarseTarget hconditional
      hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual
      hprofile hcutoff hτ (hτInv kAnchor) hτHalf hτDim hξ (hξSmall kAnchor) hξLate
      cells poly hp hmem (hsize kAnchor) hrank (hRank kAnchor) hCells hα (hdimension kAnchor)
  refine ⟨hmargin, A, ?_, ?_⟩
  · have hdec : instDecidableEqFin nX = Classical.decEq (Fin nX) := Subsingleton.elim _ _
    have hdet := preparedFiniteScheduleLocalCandidateDetection B U basis hR hσ S degree selection stride N
      Pdetect sourceU modelLog sliceLog α Vtail τ hb o
      Pchart Qstride Pmaster Plate Pphysical coarseTarget pGain hAvailable hαLower hαHalfOne
      hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual
      hprofile hcutoff hτ hτInv hτHalf hτDim hξ hξSmall hξLate
      cells poly hp hmem hsize hrank hRank hCells hdimension A
    rw [hdec] at hdet
    exact hdet
  · exact A.prepared_conditional_excess μ ν scalar geometryAt hSLate
      Cforward Vtail hforward hForward hVactual hVtail C hC hCbound hchart hp
      hstrideBound (hτInv kAnchor) hτHalf hτDim
      ((hξSmall kAnchor).trans (min_le_left _ _)) hξLate
      hsizeConditional hrank hRankConditional hCells (A 0).integerBox_nonempty hmargin

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedForwardCanonicalFixedCenterSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ} (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ u p forecastCap : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]

variable (Good : ∀ (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)),
  (∀ j ex, coefficients (poly j) ex ∈ U j) →
  ∀ (width : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)),
    (CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) → Prop)

variable (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget extraRequired : ℝ)
local notation "r" => preparedModularGeneralDetectorResources
  (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate
local notation "Ctail" =>
  (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap

theorem allocatedExternalCandidatePreparedGood_of_model
    (hGoodModel : SharedWidthPreparedCenteredForecastModelExtensionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ) (Good := Good)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget extraRequired)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    {E : ℝ}
    (hτ : 0 < τ) (hτInv : τ⁻¹ ≤ Real.exp Pphysical)
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff 0 G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) (α / 2))
      Pphysical coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ i, Real.exp (max
      (max (r).required ((max (r).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) extraRequired) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : Real.exp (max
      (max (r).required ((max (r).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) extraRequired) ≤ Rrank)
    (hCells : cells.Nonempty)
    (A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells) :
    (∀ z, Measurable (fun center => (A.law center).weight z)) ∧
      Good poly hmem (allocatedExternalCandidateWidths B U basis S N τ ξ) (A 0).bases A.law := by
  obtain ⟨hN, hbases, _hbox, hmass, _hnormalizer, _hmargin,
      hnormalizerCenter, hweight, hGood, _hmodel⟩ :=
    hGoodModel hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff hτ hτInv hτHalf hτDim hξ hξSmall hξLate
      cells poly hp hmem hsize hrank hRank hCells
  exact A.measurable_good_of_prepared hbases
    (narrowTrimmedSpatialWidths_pos (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
      hτ hξ N hN)
    hmass (fun center => (hnormalizerCenter center).2.2.1) (Good poly hmem) hweight hGood

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}

theorem allocatedExternalPreparedProductiveCenter_of_model
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 gainLog gain Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (Pprod : ℝ)
    (hGoodModel : SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface
      prep U b hR hσ S selection stride N Pdetect uSource pModel pSlice
      Vtail τ u p forecastCap hb o bW μ
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding Pprod)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    {E : ℝ}
    (hτ : 0 < τ) (hτInv : τ⁻¹ ≤ Real.exp Pphysical)
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) (forecastAugmentedUnitThreshold u p (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap / 2))
      Pphysical coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ i, Real.exp (max
      (max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate)).required ((max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate)).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m))) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : Real.exp (max
      (max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate)).required ((max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate)).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m))) ≤ Rrank)
    (hCells : cells.Nonempty)
    (A : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hb o hR hσ
      N poly hmem τ ξ stride cells)
    (test : (Fin nX → ℝ) → ℝ)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    PreparedCenteredProductiveGoodCenterConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hmem stride
      (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N τ ξ) (A 0).bases
      gainLog gain Qgood spatialEmbedding A.law N test := by
  obtain ⟨hweight, hgood, hproductive⟩ :=
    allocatedExternalCandidatePreparedGood_of_model
      (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ) (Good := _)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m)) hGoodModel
      hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff hτ hτInv hτHalf hτDim hξ hξSmall hξLate
      cells poly hp hmem hsize hrank hRank hCells A
  exact preparedCenteredProductiveGoodCenter (m := m) (nX := nX) (M := M)
    prep U b S bW hb o hR hσ μ poly hmem stride
    (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N τ ξ) (A 0).bases
    gainLog gain Qgood spatialEmbedding A.law N test hweight hgood hproductive htest hgain hmean

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m)
attribute [local instance] OAI.Erdos3.VectorPolynomial.productiveFixedSourceFinDecidableEq
variable (U : ∀ j, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
variable (basis : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis R σ)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]

theorem exists_preparedFiniteScheduleProductiveFixedCenterSource_s2_oai
    (kAnchor : Stage)
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget : ℝ) (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Pscale D target Pk Prho pRadius E : ℝ}
    (scalar : PreparedUniformDegreeDirectScalarBounds m (degree kAnchor) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      (sampledSupportedSlicedDetectionConstant (degree kAnchor) Pdetect)
      Pchart Pscale D target Pk Prho Qstride (Pmaster kAnchor) Plate (pGain kAnchor)
      (Pphysical kAnchor) coarseTarget pRadius (sourceU kAnchor) (modelLog kAnchor) (sliceLog kAnchor))
    (geometryAt : PreparedUniformDegreeGeometryAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis S (degree kAnchor)
      (sampledSupportedSlicedDetectionConstant (degree kAnchor) Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog (sourceU kAnchor) (modelLog kAnchor))
      pRadius (2 * sourceU kAnchor + 4 * modelLog kAnchor + 7) (pGain kAnchor))
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτ : 0 < τ) (hτInv : ∀ k, τ⁻¹ ≤ Real.exp (Pphysical k))
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (selection k)
      (allocatedDetectedKernelCutoff (degree k) (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      (Pphysical k) coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : ∀ k, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ Rrank)
    (hsizeConditional : ∀ i, Real.exp (preparedConditionalExcessRequired m Plate E) ≤ (N i : ℝ))
    (hRankConditional : Real.exp (preparedConditionalExcessRequired m Plate E) ≤ Rrank)
    (hCells : cells.Nonempty)
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    (selectionProductive : Fin (0 + 1) ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    (sourceProductive modelProductive sliceProductive uProductive pProductive forecastProductive : ℝ)
    (PmasterProductive pGainProductive PphysicalProductive : ℝ)
    (B0 gainLog gain Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (Pprod : ℝ)
    (hProductiveSource : SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface
      prep U basis hR hσ S selectionProductive stride N Pdetect sourceProductive modelProductive sliceProductive
      Vtail τ uProductive pProductive forecastProductive hb o bW μ
      Pchart Qstride PmasterProductive Plate pGainProductive PphysicalProductive coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding Pprod)
    (hτInvProductive : τ⁻¹ ≤ Real.exp PphysicalProductive)
    (hξSmallProductive : ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selectionProductive
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog sourceProductive modelProductive) (allocatedModelTestLog sourceProductive modelProductive) (forecastAugmentedUnitThreshold uProductive pProductive (Real.exp (sliceProductive * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastProductive / 2))
      PphysicalProductive coarseTarget)
    (hsizeProductive : ∀ i, Real.exp (max
      (max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).required ((max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m))) ≤ (N i : ℝ))
    (hRankProductive : Real.exp (max
      (max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).required ((max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m))) ≤ Rrank)
    (test : (Fin nX → ℝ) → ℝ)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)))
    : ∃ hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i,
    ∃ A : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis S hb o hR hσ N poly hmem τ ξ stride cells,
      PreparedCenteredProductiveGoodCenterReadyConclusion (m := m) (nX := nX) (M := M)
        prep U basis S bW hb o hR hσ μ poly hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis S N τ ξ) (A 0).bases
        gainLog gain Qgood spatialEmbedding A.law N test (fun center =>
    (∀ k, (A center).NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
      letI : Nonempty (A center).Site := (A center).site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) (A center).integerBox_nonempty).excessMass
        ((A center).law.siteLaw ((A center).physicalBox
          ((hξSmall kAnchor).trans (min_le_left _ _)) hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤
          6 * positiveProjectionAccuracy E) := by
  obtain ⟨hmargin, A, hdetect, hexcess⟩ :=
    exists_preparedFiniteScheduleFixedCenterSource
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
      (degree := degree) (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU) (modelLog := modelLog) (sliceLog := sliceLog)
      (α := α) (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      kAnchor Pchart Qstride Pmaster Plate Pphysical coarseTarget pGain hAvailable μ ν
      scalar geometryAt hSLate hαLower hαHalfOne hstride hstrideBound
      C hC hCbound hchart Cforward hforward hForward hVtail hVactual hprofile hcutoff
      hτ hτInv hτHalf hτDim hξ hξSmall hξLate cells poly hp hmem hsize hrank hRank
      hsizeConditional hRankConditional hCells hdimension
  have hdec : productiveFixedSourceFinDecidableEq = instDecidableEqFin nX := Subsingleton.elim _ _
  have hmeanProductive := hmean
  rw [hdec] at hmeanProductive
  have hselected := allocatedExternalPreparedProductiveCenter_of_model
    (m := m) (nX := nX) (M := M) prep U basis hR hσ S selectionProductive stride N Pdetect
    sourceProductive modelProductive sliceProductive Vtail τ uProductive pProductive forecastProductive
    hb o bW μ Pchart Qstride PmasterProductive Plate pGainProductive PphysicalProductive coarseTarget
    B0 gainLog gain Pgood Qgood spatialEmbedding Pprod hProductiveSource
    hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual hprofile hcutoff
    hτ hτInvProductive hτHalf hτDim hξ hξSmallProductive hξLate cells poly hp hmem
    hsizeProductive hrank hRankProductive hCells A test htest hgain hmeanProductive
  refine ⟨hmargin, A, ?_⟩
  apply preparedCenteredProductiveGoodCenter_with_ready
    (m := m) (nX := nX) (M := M) prep U basis S bW hb o hR hσ μ poly hmem stride
    (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis S N τ ξ) (A 0).bases
    gainLog gain Qgood spatialEmbedding A.law N test _ hselected
  intro center
  exact ⟨fun k => hdetect k center, hexcess center⟩

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleProductiveFixedCenterSource_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleProductiveFixedCenterSource_s2_oai
