-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T08:31:34.281259+00:00
-- url     : https://prove2.me/submissions/b9f00512-7bf8-4ed1-81af-492f0b89a184

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B290
import Definitions.Def_OAIE3v2B291

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

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (N : X → ℕ) (hN : ∀ i, 0 < N i)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

omit [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
theorem preparedModularGeneralCenteredLaw
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (hcenter : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)) :
    ∃ htotal : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))),
      allocatedOriginalPathLaw B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))
        N hN hW hτ hξ stride cells hmass bases hbases htotal =
      selectedJointFiniteLaw bases hbases stride cells widths
        (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
        (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
        (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) hcenter := by
  have htotal : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))) := by
    rw [allocatedJointBaseDensity_subtractConstant_centered B U b hb o hR hσ S poly hmem center c hc]
    exact hcenter
  exact ⟨htotal, allocatedOriginalPathLaw_subtractConstant_eq_centered B U b hb o hR hσ S
    poly hmem N hN hW hτ hξ stride cells hmass bases hbases center c hc htotal hcenter⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorProductive
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem preparedModularGeneral_productivity_bounds
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {Pmaster Plate Pprod D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hProd : 4 * (Plate + 8) ^ 2 ≤ Pprod)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hD : D ≤ Pmaster) {nX : ℕ} (hnXpos : 0 < nX) (hnX : (nX : ℝ) ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp Pmaster)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp Pmaster)
    (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : Fin nX → ℕ) (hs : ∀ d, 0 < stride d)
    (hsP : ∀ d, (stride d : ℝ) ≤ Real.exp Pmaster)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp Pmaster)
    (hτhalf : τ ≤ 1 / 2)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (N : Fin nX → ℕ) {rank : ℝ}
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (hCells : cells.Nonempty) :
    (∀ d, Real.exp ((Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m) ≤ (N d : ℝ)) →
    Real.exp ((Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m) ≤ rank →
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    ∃ (_hN : ∀ i, 0 < N i) (hwidths : ∀ z, 0 < widths z)
      (hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
      (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells widths (density center)),
    let law := fun center => selectedJointFiniteLaw bases
      (trimmedIntegerBox_nonempty N _ hmargin) stride cells widths hwidths hmass
      (density center) (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      (hD center)
    (∀ center,
      let Z := selectedJointDensityMass bases stride cells widths (density center)
      |Z - 1| ≤ Real.exp (-Pprod) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
    ∀ (test : (Fin nX → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, 0 < gain → Real.exp (-Pprod) ≤ gain / 16 →
      12 * positiveProjectionAccuracy Pprod + 2 * (nX : ℝ) * τ ≤ gain / 8 →
      gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
      Function.Injective (fun q : Sites => jointIntegerPhysicalSite q.val (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : Sites, test
          (fun i => (jointIntegerPhysicalSite q.val (z.1.val,z.2.val) i : ℝ)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U basis hb o hR hσ S p hm c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) ∧
      ∀ z : bases × rectangularWeightIndices 0 widths 1, ∀ q : Sites,
        jointIntegerPhysicalSite q.val (z.1.val,z.2.val) ∈ integerBox N := by
  intro hSize hRank W widths bases density sides Sites
  let : Nonempty (Fin nX) := ⟨⟨0, hnXpos⟩⟩
  have hPlate : 0 ≤ Plate := hMaster.trans hLate
  have hLproj : Plate ≤ Pprod := by
    nlinarith only [hProd, hPlate, sq_nonneg Plate]
  have hExpLate := Real.exp_le_exp.mpr hLproj
  have hPproj : Pmaster ≤ Pprod := by
    nlinarith only [hProd, hPlate, hLate, sq_nonneg Plate]
  have h2Pproj : 2 * Pmaster ≤ Pprod := by
    nlinarith only [hProd, hPlate, hLate, sq_nonneg Plate]
  have hframeProj : (2 * Pmaster + 1) * Pmaster ≤ Pprod := by
    have hsq : Pmaster^2 ≤ Plate^2 := pow_le_pow_left₀ hMaster hLate 2
    nlinarith only [hProd, hPlate, hLate, hsq, sq_nonneg Plate]
  have hExp := Real.exp_le_exp.mpr hPproj
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * Pmaster :=
    (preparedModularGeneralDetector_variable_count B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd).trans (by linarith only [hD])
  have hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pprod := by
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact (mul_le_mul (add_le_add_left hvars 1) hnX (Nat.cast_nonneg _) (by positivity)).trans
      (by simpa only [add_comm] using hframeProj)
  obtain ⟨hI, hn⟩ := preparedModularGeneralDetector_layer_axes B
    (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd
  have hJ (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ Pprod :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U basis o j)).trans
      (hd.axes.trans (hD.trans hPproj))
  have hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
  have hWproj : W ≤ Real.exp Pprod :=
    (preparedModularGeneralDetector_physical_root B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) U basis S hd (hD.trans hLate) hLLate).trans
        (Real.exp_le_exp.mpr (by nlinarith only [hProd, hPlate, hLate, sq_nonneg Plate]))
  have hProductive := (Classical.choose_spec
    (exists_allocated_fixedScale_productive_joint_measure.{0,0,0,0,0,0} m)).2
    (X := Fin nX) (G := G) B U basis S hb o μ ν hR hσ hσ1
    C V hC hV Cinv hCinv hchart hsmall
    (P := Pprod) (hMaster.trans hPproj) (hd.degree.trans (hD.trans hPproj))
    (hvars.trans h2Pproj) (by simpa only [Fintype.card_fin] using hnX.trans hPproj) hframe
    (fun j => (hRP j).trans hExp) (fun j => (hσLate j).trans hExpLate)
    (fun j => (hd.coefficients j).trans (hD.trans hPproj))
    (fun j => (hI j).trans (hD.trans hPproj)) (fun j => (hn j).trans (hD.trans hPproj)) hJ
    ((hd.profile.trans (hD.trans hPproj)).trans (by linarith [Real.add_one_le_exp Pprod]))
    (hLLate.trans hExpLate) (fun j => (hCP j).trans hExp) (fun j => (hVP j).trans hExp)
    p hp hm stride hs (fun d => (hsP d).trans hExp) hW hWproj
    hτ (hτP.trans hExp) hτhalf hξ hξ1 (hξLate.trans hExpLate) N hSize hrank hRank cells hCells
  obtain ⟨hN, hwidths, hmargin, hmass, hDens, hnormal, htest⟩ := hProductive
  refine ⟨hN, hwidths, hmargin, hmass, hDens, ?_⟩
  intro law
  refine ⟨hnormal, ?_⟩
  have hsides (k : LayerSamplerVariables G I n B) : 0 < sides k := by
    cases k with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U basis S j
  let : ∀ k, NeZero (sides k) := fun k => ⟨(hsides k).ne'⟩
  let : Nonempty Sites := (integerBox_nonempty sides).to_subtype
  intro test htestBound gain hgain hcollision hprecision hscore
  exact htest (Sites := Sites) Subtype.val Subtype.val_injective
    (fun q => allocatedParameterBox_root_bound B U basis S q)
    test htestBound gain hgain hcollision (by simpa only [Fintype.card_fin] using hprecision) hscore

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularGeneralProductivityFreeSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem preparedModularGeneral_productivity_early_spatial_bounds
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {Pmaster Plate Pprod D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hProd : 4 * (Plate + 8) ^ 2 ≤ Pprod)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hD : D ≤ Pmaster) {nX : ℕ} (hnXpos : 0 < nX) (hnX : (nX : ℝ) ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp Pmaster)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp Pmaster)
    (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : Fin nX → ℕ) (hs : ∀ d, 0 < stride d)
    (hsP : ∀ d, (stride d : ℝ) ≤ Real.exp Pmaster)
    {gainLog ξ : ℝ} (hg : 0 ≤ gainLog)
    (hGainMaster : gainLog + (nX : ℝ) + 8 ≤ Pmaster)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (N : Fin nX → ℕ) {rank : ℝ}
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (hCells : cells.Nonempty) :
    (∀ d, Real.exp ((Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m) ≤ (N d : ℝ)) →
    Real.exp ((Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m) ≤ rank →
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    ∃ (hN : ∀ i, 0 < N i) (hwidths : ∀ z, 0 < widths z)
      (hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
      (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells widths (density center)),
    let law := fun center => selectedJointFiniteLaw bases
      (trimmedIntegerBox_nonempty N _ hmargin) stride cells widths hwidths hmass
      (density center) (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      (hD center)
    (∀ center,
      let Z := selectedJointDensityMass bases stride cells widths (density center)
      |Z - 1| ≤ Real.exp (-Pprod) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
    (∀ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (c : ∀ j, U j),
      coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun a => c a.1))) →
      ∃ htotal : 0 < selectedJointDensityMass bases stride cells widths
          (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX)
            (fun j => subtractConstant (c j).val (p j))
            (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j))),
        allocatedOriginalPathLaw B U basis hb o hR hσ S (Fin nX)
          (fun j => subtractConstant (c j).val (p j))
          (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j))
          N hN (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
          (Real.exp_pos _) hξ stride cells hmass bases
          (trimmedIntegerBox_nonempty N _ hmargin) htotal = law center) ∧
    ∀ (test : (Fin nX → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, Real.exp (-gainLog) ≤ gain →
      gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
      Function.Injective (fun q : Sites => jointIntegerPhysicalSite q.val (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : Sites, test
          (fun i => (jointIntegerPhysicalSite q.val (z.1.val,z.2.val) i : ℝ)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U basis hb o hR hσ S p hm c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) ∧
      ∀ z : bases × rectangularWeightIndices 0 widths 1, ∀ q : Sites,
        jointIntegerPhysicalSite q.val (z.1.val,z.2.val) ∈ integerBox N := by
  intro hSize hRank τ W widths bases density sides Sites
  obtain ⟨hPτ, hτ, hτhalf, hτdim, hτeq, hτcap, hprecision⟩ :=
    preparedEarlySpatialWidth nX hg
  have hτP : τ⁻¹ ≤ Real.exp Pmaster := hτcap Pmaster hGainMaster
  have hPlate : 0 ≤ Plate := hMaster.trans hLate
  have hGainProd : gainLog + 8 ≤ Pprod := by
    have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
    nlinarith only [hGainMaster, hLate, hProd, hPlate, hnX0, sq_nonneg Plate]
  obtain ⟨hN, hwidths, hmargin, hmass, hDens, hnormal, htests⟩ :=
    preparedModularGeneral_productivity_bounds B U basis S hb o μ ν hR hσ hσ1
      C V hC hV Cinv hCinv hchart hsmall hMaster hLate hProd hd hD hnXpos hnX
      hRP hσLate hLLate hCP hVP p hp hm stride hs hsP
      hτ hτP hτhalf hξ hξ1 hξLate N hrank cells hCells hSize hRank
  refine ⟨hN, hwidths, hmargin, hmass, hDens, ?_⟩
  intro law
  refine ⟨hnormal, ?_, ?_⟩
  · intro center c hc
    exact preparedModularGeneralCenteredLaw B U basis hb o hR hσ S p hm N hN
      (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ
      stride cells hmass bases (trimmedIntegerBox_nonempty N _ hmargin)
      center c hc (hDens center)
  · intro test htest gain hgain hscore
    obtain ⟨hcollision, herr⟩ := hprecision Pprod gain hGainProd hgain
    exact htests test htest gain ((Real.exp_pos _).trans_le hgain) hcollision herr hscore

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SharedWidthPreparedShortForecastSourceModelAttachment
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
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
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ u p forecastCap : ℝ)
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
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]

variable (Good Extra : ∀ (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)),
  (∀ j ex, coefficients (poly j) ex ∈ U j) →
  ∀ (width : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)),
    (CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) → Prop)

theorem sharedWidthPreparedCenteredForecastModelExtension_and
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget extra₁ extra₂ : ℝ)
    (hModel : SharedWidthPreparedCenteredForecastModelExtensionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ) (Good := Good)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget extra₁)
    (hExtra : SharedWidthPreparedCenteredForecastModelExtraDataInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (Good := Extra)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget (max extra₁ extra₂)) :
    SharedWidthPreparedCenteredForecastModelExtensionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ) (Good := fun poly hm width bases law =>
        Good poly hm width bases law ∧ Extra poly hm width bases law)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget (max extra₁ extra₂) := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff E hτSpatial hτInv hτHalf hτDim
    r W ξn hξn hξle hξLate hW hξone Pmarginal modelRequired required cells poly hpoly hmem Rrank
    hsize hrank hRank V hCells bases Z
  have hcutoffPrevious : max modelRequired extra₁ ≤ required :=
    max_le (le_max_left _ _) ((le_max_left extra₁ extra₂).trans (le_max_right _ _))
  have hsizeModel (i) : Real.exp (max modelRequired extra₁) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hcutoffPrevious).trans (hsize i)
  have hRankModel : Real.exp (max modelRequired extra₁) ≤ Rrank :=
    (Real.exp_le_exp.mpr hcutoffPrevious).trans hRank
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hnormalizerCenter, hweight, hgood, hrest⟩ :=
    hModel hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff (E := E) hτSpatial hτInv hτHalf hτDim
      hξn hξle hξLate cells poly hpoly hmem hsizeModel hrank hRankModel hCells
  have hextra := hExtra hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff (E := E) hτSpatial hτInv hτHalf hτDim
    hξn hξle hξLate cells poly hpoly hmem hsize hrank hRank hCells
    hN hbases hbox hmass hnormalizer hmargin hnormalizerCenter
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path Zcenter
  refine ⟨hnormalizerCenter, ?_⟩
  intro centeredLaw
  exact ⟨hweight, ⟨hgood, hextra⟩, hrest⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SharedWidthPreparedShortForecastProductiveModelAttachment
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite

theorem sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel_s2_oai
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
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)] [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [μ.IsAddLeftInvariant]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 gainLog gain Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (Pprod : ℝ)
    {D : ℝ}
    (hBounds : PreparedCenteredForecastProductiveBounds (m := m) (nX := nX) (M := M)
      (prep := prep) (U := U) (b := b) (S := S) (selection := selection)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      Pchart Qstride Pmaster Plate Pphysical coarseTarget gainLog Pprod D)
    (hModel : SharedWidthPreparedCenteredShortForecastGoodModelInterface (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀) (Q := Q)
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding) :
    SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀) (Q := Q)
      (prep := prep) (U := U) (b := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (bW := bW) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding Pprod := by
  rcases hBounds with ⟨hnX, hσ1, hsmall, hMaster, hLate, hd, hD, hnMaster, hRi, hσi,
    hS, hchartMaster, hstrideMaster, hProd, hg, hGainMaster, hτeq, _hξCanonical⟩
  subst τ
  apply sharedWidthPreparedCenteredForecastModelExtension_and
    (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := Real.exp (-(gainLog + (nX : ℝ) + 8))) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (μ := μ)
    (Good := fun (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (V : Option (LayerSamplerVariables
        (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
      (bases : Finset (Fin nX → ℤ))
      (law : CoefficientTorus (K := LayerSamplerVariables
        (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U →
        FiniteProbabilityWeights (bases × rectangularWeightIndices 0 V 1)) =>
      PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M) prep U b S bW hb o hR hσ μ poly hmem
        stride V bases gainLog gain Qgood spatialEmbedding law)
    (Extra := fun (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (V : Option (LayerSamplerVariables
        (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
      (bases : Finset (Fin nX → ℤ))
      (law : CoefficientTorus (K := LayerSamplerVariables
        (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U →
        FiniteProbabilityWeights (bases × rectangularWeightIndices 0 V 1)) =>
      PreparedCenteredForecastProductiveConclusion (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hb o hR hσ μ poly hmem
        N V bases gainLog law)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    (preparedCenteredShortForecastGoodRequired m B0 Pgood)
    ((Pprod + preparedModularGeneralProductivityExponent m) ^ preparedModularGeneralProductivityExponent m)
    hModel
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff Eforecast hτSpatial hτInv hτHalf hτDim
    r W ξn hξn hξle hξLate hW hξone Pmarginal modelRequired required cells poly hpoly hmem Rrank
    hsize hrank hRank V hCells bases Z hN hbases hbox hmass hnormalizer hmargin
    Path Zcenter hnormalizerCenter centeredLaw
  have hsizeProd (i) : Real.exp ((Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr ((le_max_right _ _).trans (le_max_right _ _))).trans (hsize i)
  have hRankProd : Real.exp ((Pprod + preparedModularGeneralProductivityExponent m) ^
      preparedModularGeneralProductivityExponent m) ≤ Rrank :=
    (Real.exp_le_exp.mpr ((le_max_right _ _).trans (le_max_right _ _))).trans hRank
  obtain ⟨hN', hwidths', hmargin', hmass', hD', hnormal', hshift', hproductive⟩ :=
    preparedModularGeneral_productivity_early_spatial_bounds (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hb o μ ν
      hR hσ hσ1 Cforward Vtail hforward hVactual C hC hchart (hsmall C hC hCbound)
      hMaster hLate hProd hd hD hnX hnMaster hRi hσi hS
      (fun j => (hForward j).trans (Real.exp_le_exp.mpr hchartMaster))
      (fun j => (hVtail j).trans (Real.exp_le_exp.mpr hchartMaster))
      poly hpoly hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr hstrideMaster))
      hg hGainMaster hξn hξone hξLate N hrank cells hCells hsizeProd hRankProd
  exact hproductive

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel_s2_oai := @OAI.Erdos3.VectorPolynomial.sharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface_of_goodModel_s2_oai
