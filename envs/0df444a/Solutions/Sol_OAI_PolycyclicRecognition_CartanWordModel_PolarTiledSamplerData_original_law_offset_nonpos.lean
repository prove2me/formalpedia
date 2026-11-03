-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.original_law_offset_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:42:07.825688+00:00
-- url     : https://prove2.me/submissions/6ef56329-d912-4993-99d0-e1aeec49dc4b

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_MeasuredCone_action_preserves_sectionMeasure
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_MeasuredCone_dilation_preserves_sectionMeasure
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_MeasuredCone_sectionMeasure_isHaar
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_PolarTiledSamplerData_count_le_offset_rate
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_PolarTiledSamplerData_source_probability_data
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_PolarTiledSamplerData_source_section_rightInverse
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_original_neighbor_offset_nonpos

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarOriginalOffset
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-law trace comparison for the counted polar source -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter MeasureTheory TopologicalSpace
open scoped Manifold Pointwise Topology BigOperators NNReal

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))

local notation "C" => heightConePreimage T eW K

variable (D : M.MeasuredCone F (heightConePreimage T eW K))
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  {ε : ℝ} (β : M.ConeIdealBases (heightConePreimage T eW K)) (Rbox : ℝ) (scale : ℕ → ℝ)
  (φ : ℕ → D.I.carrier ≃ₜ* D.I.carrier)
  (P : M.PolarTiledSamplerData (EG := EG) (G := G) (W := W) (I := D.I.carrier) T F hunimod eW K
    (fun v : M.coneWordIdeal (heightConePreimage T eW K) => D.maps.expI (D.I.equiv v)) D.maps.inclusion bN ε β Rbox scale φ)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)

local notation "ZQ" => TiledProbeChainData.sourceQuotientCell
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
  (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
  (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
  (scale := scale) (φ := φ) (ι := D.maps.inclusion)
  (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
  (Q := D.Q) (chartQ := D.maps.chartQ)
local notation "J" => fun n => TiledProbeChainData.sourceKernelCell
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (E := normalizedPolarTemplates K ε)
  (β := fun _ => β) (scale := scale) (ι := D.maps.inclusion)
  (Q := D.Q) (πQ := D.maps.quotient) (hι := D.maps.inclusion_closed)
  (hrange := D.maps.inclusion_range) n
local notation "Y" => fun n : ℕ => {p : D.Q.carrier × D.maps.quotient.ker // p ∈ Set.prod ZQ (J n)}
local notation "ψ" => fun n => TiledProbeChainData.sourceCoordinates
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
  (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
  (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
  (scale := scale) (φ := φ) (ι := D.maps.inclusion)
  (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
  (Q := D.Q) (chartQ := D.maps.chartQ) (πQ := D.maps.quotient)
  (hι := D.maps.inclusion_closed) (hrange := D.maps.inclusion_range) n
local notation "σ" => TiledProbeChainData.sourceSection
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
  (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
  (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
  (scale := scale) (φ := φ) (ι := D.maps.inclusion)
  (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
  (Q := D.Q) (chartQ := D.maps.chartQ) (chartN := chartN)

variable (Eall : Set W) (γ : M.Bases) (δ : ℝ) (w : W)
  (S : ℕ → F.N.carrier ≃ₜ* F.N.carrier) (base step : ℕ → F.N.carrier)

local notation "Ep" => fun k => (fun z => z + w) '' normalizedPolarTemplates K ε k
local notation "probe" => fun k n (y : Y n) => S n (P.chain.probe n k (ψ n y))


variable {I QT : Type} [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [IsTopologicalGroup F.N.carrier] [MeasurableMul F.D.carrier]
  [Group QT] [TopologicalSpace QT] [IsTopologicalGroup QT]
  [SecondCountableTopology QT] [MeasurableSpace QT] [BorelSpace QT]

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable (A : templateSymmetryGroup (M.supportIn T hunimod eW))
  (βtarget : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
local notation "P₁" => SupportDatum.templateSupport (M.supportIn T hunimod eW) (normalizedPolarTemplates K ε 0)
local notation "P₂" => Finset.sum Finset.univ (fun j => M.coneIdealWordCost
  (heightConePreimage T eW (transformedPolarCone K A.val))
  (SupportDatum.weightSupport (M.supportIn T hunimod eW) (A.val '' normalizedPolarTemplates K ε 2))
  (βtarget.val j))

set_option maxHeartbeats 1000000 in
/-- The counted source supplies its probability, Haar invariance, exact
volume, tile count, and all three endpoints to the original-law comparison. -/
theorem PolarTiledSamplerData.original_law_offset_nonpos_oai
    [Nonempty (Fin M.letterCount)]
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (hE : IsCompact Eall) (hne : Eall.Nonempty) (γaux : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport Eall i)
    {c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW Eall w ∧ M.boxCost T hunimod eW Eall w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale)
    (hscale1 : ∀ n, 1 ≤ scale n)
    (L : P.LinkedSource T M F hunimod eW K D bN β Rbox scale φ chartN
      Eall γ δ w S base step)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
    (hEc : ∀ k, IsCompact (Ep k)) (hEconv : ∀ k, Convex ℝ (Ep k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Ep k)
    (hEV : ∀ k, Ep k ⊆ V)
    (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' Eall)
    (σchamber : Fin M.letterCount → Bool)
    (hσchamber : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σchamber).Nonempty)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
    (profile : ℕ → F.N.carrier → Profiles) (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * base n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1 ∪
      (fun v => v * base n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z)
    (law : ProbabilityMeasure (Profiles × Profiles))
    (hlaw : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN bN
        Eall γ (scale n) (base n)) (f := (fun q => (profile n q, profile n (q * step n)))) (((hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable))
      atTop (𝓝 law))
    (bval : Bool → W) (f : Profiles × Profiles)
    (hf : f ∈ (law : Measure (Profiles × Profiles)).support)
    (haffine : ∀ s z,
      eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V →
      (if s then f.2 else f.1).val z = A.val (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s)
    (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (hε : 0 < ε) (hRbox : 0 ≤ Rbox)
    (hβsource : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    (bItarget : Basis (Fin (finrank ℝ
      (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))))
      ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val))))
    (hβtarget : M.IsMaximizingConeIdealBasis
      (heightConePreimage T eW (transformedPolarCone K A.val)) bItarget
      ((M.supportIn T hunimod eW).weightSupport (A.val '' normalizedPolarTemplates K ε 2))
      βtarget)
    (hS : ∀ n v, S n (F.ExpN (F.N.equiv v)) = F.ExpN (F.N.equiv
      (cartanIdealWeightDilation T H (scale n • cartanHeightSection T H (eW.symm w)) v)))
    (Dbridge δtarget : ℝ) (hδtarget : 0 < δtarget)
    (hDb : (Λ : ℝ) * Dbridge ≤ δtarget)
    (hbridge : ∀ᶠ n in atTop, ∀ y : Y n,
      dist (F.inclusionN (coneProbeSecond (S n).toMulEquiv (base n)
          (y.val.2 : F.N.carrier) ((S n).symm (step n))) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (base n * S n ((y.val.2 : F.N.carrier) * σ y.val.1)) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ Dbridge * scale n)
    (πT : F.N.carrier →* QT) (hπT : Continuous πT)
    (μT : Measure QT) (μTI : Measure πT.ker)
    (μ : Measure F.N.carrier) (νD : Measure F.D.carrier)
    [SFinite μT] [SFinite μTI] [SFinite μ] [SFinite νD]
    [μT.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [νD.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (F.action d) μ μ)
    (actionQ : F.D.carrier →* MulAut QT) (act : G →* Equiv.Perm QT)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = πT u * actionQ d q)
    (cell : Set (F.N.carrier × F.D.carrier)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod νD) cell ≠ 0) (hcelltop : (μ.prod νD) cell ≠ ⊤)
    (hsmall : ∀ z ∈ cell, dist (1 : G) (F.inclusionN z.1 * F.inclusionD z.2) < 1 / 2)
    (regionFactory : ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ Cp : ℝ, 0 ≤ Cp → ∃ R : MeasuredProbeRegions πT μT μTI νD scale P₂,
        μ = Measure.map (quotientSectionHomeomorph πT hπT
          R.sectionMap R.section_rightInverse).symm (μT.prod μTI) ∧
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          π cell
          ((fun z => A.val (z - eW (heightProjection T.character pivot))) '' Ep 0)
          ((fun z => A.val (z - eW (heightProjection T.character pivot))) '' Ep 2)
          (fun n => 2 * η n) Cp Cp δtarget n)
    (ell : W →L[ℝ] ℝ)
    (hHaar : ∀ (g : G) (E : Set QT), μT (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (π g).toAdd)) * μT E) :
    ell (bval true - bval false) ≤ 0 := by
  let : SecondCountableTopology F.N.carrier := F.closedN.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  let bQ := (finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)).map D.Q.equiv.toLinearEquiv
  let coordQ := bQ.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartQ
  let : SecondCountableTopology D.Q.carrier := coordQ.symm.secondCountableTopology
  let : LocallyCompactSpace D.Q.carrier := coordQ.symm.isOpenEmbedding.locallyCompactSpace
  let : IsTopologicalGroup D.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.Q.modelSpace)) ⊤
  let bI' := (finBasis ℝ (M.coneWordIdeal C)).map D.I.equiv.toLinearEquiv
  let coordI := bI'.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartI
  let : SecondCountableTopology D.I.carrier := coordI.symm.secondCountableTopology
  let ke := kernelRealization D.maps.quotient D.maps.inclusion
    D.maps.inclusion_closed D.maps.inclusion_range
  let : SecondCountableTopology D.maps.quotient.ker :=
    (coordI.trans ke.toHomeomorph).symm.secondCountableTopology
  let : LocallyCompactSpace D.maps.quotient.ker :=
    (coordI.trans ke.toHomeomorph).symm.isOpenEmbedding.locallyCompactSpace
  let : IsTopologicalGroup D.I.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.I.modelSpace)) ⊤
  let : D.measures.measureI.IsHaarMeasure := D.measures.haarI
  let : D.measures.measureQ.IsHaarMeasure := D.measures.haarQ
  let : (D.kernelMeasure M F C).IsHaarMeasure := D.measures.haarKernel
  let : (D.kernelMeasure M F C).IsMulRightInvariant := D.measures.kernel_rightInvariant
  have hσ : ∀ q, D.maps.quotient (σ q) = q :=
    PolarTiledSamplerData.source_section_rightInverse T M F hunimod eW K D bN
      β Rbox scale φ P chartN hchartN
  let μS := D.sectionMeasure M F C σ hσ
  let : μS.IsHaarMeasure := D.sectionMeasure_isHaar M F C σ hσ
  have hφS (d) : MeasurePreserving (F.action d) μS μS :=
    D.action_preserves_sectionMeasure M F C T hunimod hExp realize haarN haarD dynkinN σ hσ d
  have hflow (n) : MeasurePreserving (S n) μS μS :=
    D.dilation_preserves_sectionMeasure M F C T hunimod haarN dynkinN
      (funext hchartN ▸ chartN.bijective) σ hσ
      (scale n • cartanHeightSection T H (eW.symm w)) (S n) (hS n)
  obtain ⟨hZm, hJm, hZ0, hZt, hJ0, hJt, h0, htprod,
      hZ, hJ, hneY, hregular, v, hv, hvol⟩ :=
    PolarTiledSamplerData.source_probability_data T M F hunimod eW K D haarI bN bI
      hε.le β hβsource Rbox scale φ P
  let : ∀ n, CompactSpace (Y n) := fun n => isCompact_iff_compactSpace.mp (hZ.prod (hJ n))
  let : ∀ n, Nonempty (Y n) := hneY
  have htiles (n) : (P.tiles n : ℝ) ≤ Rbox ^ finrank ℝ (M.coneWordIdeal C) *
      Real.exp (scale n * (P₁ - P₂)) :=
    PolarTiledSamplerData.count_le_offset_rate T M F hunimod eW K
      (fun v : M.coneWordIdeal C => D.maps.expI (D.I.equiv v)) D.maps.inclusion bN bI hε β hβsource
      Rbox scale φ P A bItarget βtarget hβtarget n
  exact M.original_neighbor_offset_nonpos (EG := EG) (G := G) (W := W)
    (I := I) (QS := D.Q.carrier) (QT := QT) (Λ := Λ) (Kπ := Kπ)
    (E := Eall) (δ := δ) (c := c) (lo := lo) (hi := hi) (v := v) T F hunimod eW
    D.maps.quotient ZQ J hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan
    hΛ hπ hpath bN hE hne γ γaux hβ hweights hδ hc hhi ht hcost hgap
    X hDnil hDletters bD₀ βD hβD aN hmN aD hmD scale hscale hmono hscale1
    L.error L.error_nonneg L.error_tendsto Ep probe L.chains L.origin L.finish L.linked
    rem hdim p x hN hD pivot V hV hVconv hEc hEconv hpivot hEV hVheight σchamber hσchamber
    chartN hchartN base step L.origin_eq L.finish_eq Profiles profile hp hactual
    law hlaw A.val.toLinearMap bval f hf haffine
    D.maps.quotient_continuous σ hσ D.measures.measureQ (D.kernelMeasure M F C) μS hφS rfl
    (fun n => (S n).toHomeomorph) hflow hZm hJm hZ0 hZt hJ0 hJt hregular
    P₁ P₂ hv (fun n => (hvol n).ge) P.tiles
    (fun n y => P.chain.index n (ψ n y).2)
    (fun n j => coneProbeSecond (S n).toMulEquiv (base n)
      (D.maps.inclusion (P.anchor n j)) ((S n).symm (step n)))
    (fun n y => coneProbeSecond (S n).toMulEquiv (base n)
      (y.val.2 : F.N.carrier) ((S n).symm (step n)))
    L.first_endpoint L.anchor_endpoint L.second_endpoint Dbridge δtarget hδtarget hDb hbridge
    πT hπT μT μTI μ νD hφ actionQ act hact cell hcell hcell0 hcelltop hsmall
    regionFactory ell (fun _ => Rbox ^ finrank ℝ (M.coneWordIdeal C))
    (sequence_subexponential_upper_const hscale _) (Eventually.of_forall (fun _ => by positivity))
    hHaar (Eventually.of_forall htiles)


end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.original_law_offset_nonpos_oai := @OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.original_law_offset_nonpos_oai
