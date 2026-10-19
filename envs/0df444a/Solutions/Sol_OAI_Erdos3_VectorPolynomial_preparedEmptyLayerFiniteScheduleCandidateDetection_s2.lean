-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedEmptyLayerFiniteScheduleCandidateDetection_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:30:55.891664+00:00
-- url     : https://prove2.me/submissions/29abcd18-2e22-4da0-9e19-66f2a95f8beb

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeSheetHaar
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lattice_covolume_of_finrank_zero (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hd : Module.finrank ℝ E = 0) : ZLattice.covolume Λ = 1 := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = 0 := by
    rw [← Module.finrank_eq_card_basis b, ZLattice.rank ℝ Λ, hd]
  let : IsEmpty (Module.Free.ChooseBasisIndex ℤ Λ) := Fintype.card_eq_zero_iff.mp hcard
  have h := lattice_covolume_sq_eq_gram Λ b
  rw [Matrix.det_isEmpty] at h
  nlinarith [ZLattice.covolume_pos Λ MeasureTheory.volume]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmptyLayerDetectionGeometry
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

theorem latticeSection_covolume_eq_one_of_isEmpty
    {D : Type*} [Fintype D] [IsEmpty D]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) :
    ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) = 1 := by
  let : IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W) := by
    constructor
    apply eq_top_iff.mpr
    intro x _
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    exact Submodule.zero_mem _
  exact lattice_covolume_of_finrank_zero _ (Module.finrank_zero_of_subsingleton)

theorem mixedDensityCovolumeRatio_eq_one_of_isEmpty
    {D : Type*} [Fintype D] [IsEmpty D] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ) :
    mixedDensityCovolumeRatio W b = 1 := by
  have hn : Fintype.card (Fin n) = 0 :=
    (Module.finrank_eq_card_basis b).symm.trans Module.finrank_zero_of_subsingleton
  let : IsEmpty (Fin n) := Fintype.card_eq_zero_iff.mp hn
  simp [mixedDensityCovolumeRatio, latticeSection_covolume_eq_one_of_isEmpty W]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarStructuralBasePower
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem normalizedSiteCutoffBound_one_le : 1 ≤ normalizedSiteCutoffBound :=
  (Classical.choose_spec exists_smooth_scalar_cutoff).1

end Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarFiniteScheduleCandidateDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedEmptyLayerFiniteScheduleCandidateDetection_s2_oai
    {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)
    {K : Type} (degree : K → ℕ) (selection : ∀ k, Fin (degree k + 1) ↪ G)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (sourceU modelLog sliceLog α : K → ℝ) (τ ξ : ℝ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (Pchart Qstride : ℝ) (Pmaster : K → ℝ) (Plate : ℝ)
    (Pphysical : K → ℝ) (coarseTarget : ℝ) (pGain : K → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N) (Pdetect := Pdetect)
      (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := fun _ => 1) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτInv : ∀ k, τ⁻¹ ≤ Real.exp (Pphysical k))
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      (Pphysical k) coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ))
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hmem τ ξ stride cells center) :
    ∀ k, A.NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) := by
  let : MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U) := borel _
  let : BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U) := ⟨rfl⟩
  have hCells : cells.Nonempty := by
    by_contra h
    have hz : cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hmass := A.smooth_mass_pos
    simp only [hz, selectedResidueSmoothWeight, Finset.notMem_empty, ↓reduceIte,
      tsum_zero, lt_self_iff_false] at hmass
  have hone : (1 : ℝ) ≤ Real.exp Pchart :=
    (show (1 : ℝ) ≤ normalizedSiteCutoffBound by
      exact_mod_cast normalizedSiteCutoffBound_one_le).trans hcutoff
  have hp (j) : DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j) := by
    intro e he
    exact Subsingleton.elim _ _
  have hrank (j) (rank : ℝ) :
      HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) rank (U j) (poly j) := by
    intro a ha hw
    obtain ⟨w, hw⟩ := hw
    exact (hw (Finset.sum_eq_zero (fun i _ => isEmptyElim i))).elim
  have hchart (j) (v) :
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤
        (0 : ℝ) * ‖v‖ := by
    have hz : (normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v = 0 :=
      Subsingleton.elim _ _
    simp only [hz, norm_zero, zero_mul, le_refl]
  have hforward (j) (v) :
      ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤
        ((0 : ℝ≥0) : ℝ) * ‖v‖ := by
    have hz : v = 0 := Subsingleton.elim _ _
    simp only [hz, map_zero, norm_zero, mul_zero, le_refl]
  have hratio (j) :
      0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ (1 : ℝ≥0) := by
    rw [mixedDensityCovolumeRatio_eq_one_of_isEmpty]
    norm_num
  intro k
  have hDirect := hAvailable k (α k / 2) (hαLower k) (hαHalfOne k)
  have hconditional := preparedModularGeneralConditionalDetectionFreeTrimSharedWidth_of_direct
    (B := B) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection k) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
    (Vtail := fun _ => 1) (α := α k) (τ := τ) (hb := hb) (o := o)
    Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget hDirect
  have hα : 0 < α k := by
    have hhalf := (Real.exp_pos _).trans_le (hαLower k)
    linarith only [hhalf]
  obtain ⟨Ak, _, hdetect⟩ :=
    exists_allocatedExternalCandidateSamplerFamily_nativeDetection
      (B := B) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := fun _ => 1) (α := α k) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget hconditional
      A.stride_pos hstrideBound (fun _ => 0) (fun _ => le_refl 0)
      (fun _ => (Real.exp_pos _).le) hchart (fun _ => 0) hforward
      (fun _ => (Real.exp_pos _).le) (fun _ => hone) hratio
      hprofile hcutoff A.trim_pos (hτInv k) hτHalf hτDim A.narrow_pos (hξSmall k) hξLate
      cells poly hp hmem (hsize k) (fun j => hrank j _) (le_refl _) hCells hα (hdimension k)
  have hsame : Ak center = A := Subsingleton.elim _ _
  have hd : (Ak center).NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) := hdetect center
  rw [hsame] at hd
  exact @hd

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedEmptyLayerFiniteScheduleCandidateDetection_s2_oai := @OAI.Erdos3.VectorPolynomial.preparedEmptyLayerFiniteScheduleCandidateDetection_s2_oai
