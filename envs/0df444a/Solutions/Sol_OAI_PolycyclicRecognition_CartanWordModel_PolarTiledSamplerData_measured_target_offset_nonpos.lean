-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.measured_target_offset_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T22:40:18.471479+00:00
-- url     : https://prove2.me/submissions/2966e8b8-086f-4084-8e12-8416340cc13a

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Definitions.Def_OAIQ093D020
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_MeasuredCone_action_preserves_sectionMeasure
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_MeasuredCone_sectionMeasure_isHaar
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_PolarTiledSamplerData_original_box_law_offset_nonpos

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarMeasuredOffset
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.unitaryCentralFixed_complete _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original neighboring boxes supply the counted source comparison -/

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


variable {I : Type} [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [IsTopologicalGroup F.N.carrier] [MeasurableMul F.D.carrier]

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable (A : templateSymmetryGroup (M.supportIn T hunimod eW))
  (βtarget : M.ConeIdealBases (heightConePreimage T eW (transformedPolarCone K A.val)))
local notation "CT" => heightConePreimage T eW (transformedPolarCone K A.val)
variable (Dt : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A.val)))
  [IsTopologicalGroup Dt.Q.carrier]
local notation "μN" => Dt.sectionMeasure M F CT Dt.maps.sectionMap Dt.maps.section_rightInverse
local notation "μQ" => Dt.measures.measureQ
local notation "μI" => Dt.kernelMeasure M F CT
local notation "P₂" => Finset.sum Finset.univ (fun j => M.coneIdealWordCost
  (heightConePreimage T eW (transformedPolarCone K A.val))
  (SupportDatum.weightSupport (M.supportIn T hunimod eW) (A.val '' normalizedPolarTemplates K ε 2))
  (βtarget.val j))

set_option maxHeartbeats 1000000 in
/-- Construct the source chains and their endpoints from the original
neighboring boxes before applying the measured trace comparison. -/
theorem PolarTiledSamplerData.measured_target_offset_nonpos_oai
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
    (hBE : (fun z => z + w) '' normalizedPolarTemplates K ε 1 ⊆ Eall)
    (radius : ℕ → ℝ) (hradius0 : ∀ n, 0 ≤ radius n)
    (hradius : HasSubexponentialUpperBoundSeq scale radius)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun z => (1 + δ) • z) '' Eall) γ (scale n) (radius n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun z => (1 + δ) • z) '' Eall) γ (scale n) (radius n))
    (hφsource : ∀ n z, D.maps.inclusion (φ n z) =
      (S n).symm (step n) * D.maps.inclusion z * ((S n).symm (step n))⁻¹)
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
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SFinite νD]
    (actionQ : F.D.carrier →* MulAut Dt.Q.carrier) (act : G →* Equiv.Perm Dt.Q.carrier)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q =
      Dt.maps.quotient u * actionQ d q)
    (cell : Set (F.N.carrier × F.D.carrier)) (hcell : MeasurableSet cell)
    (hcell0 : ((μN).prod νD) cell ≠ 0) (hcelltop : ((μN).prod νD) cell ≠ ⊤)
    (hsmall : ∀ z ∈ cell, dist (1 : G) (F.inclusionN z.1 * F.inclusionD z.2) < 1 / 2)
    (regionFactory : ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ Cp : ℝ, 0 ≤ Cp → ∃ R : MeasuredProbeRegions Dt.maps.quotient μQ μI νD scale P₂,
        μN = Measure.map (quotientSectionHomeomorph Dt.maps.quotient Dt.maps.quotient_continuous
          R.sectionMap R.section_rightInverse).symm ((μQ).prod μI) ∧
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          π cell
          ((fun z => A.val (z - eW (heightProjection T.character pivot))) '' Ep 0)
          ((fun z => A.val (z - eW (heightProjection T.character pivot))) '' Ep 2)
          (fun n => 2 * η n) Cp Cp δtarget n)
    (ell : W →L[ℝ] ℝ)
    (hHaar : ∀ (g : G) (E : Set Dt.Q.carrier), μQ (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (π g).toAdd)) * μQ E) :
    ell (bval true - bval false) ≤ 0 := by
  let : SecondCountableTopology F.N.carrier := F.closedN.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  let bQt := (finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal CT)).map Dt.Q.equiv.toLinearEquiv
  let coordQt := bQt.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans Dt.maps.chartQ
  let : SecondCountableTopology Dt.Q.carrier := coordQt.symm.secondCountableTopology
  let : LocallyCompactSpace Dt.Q.carrier := coordQt.symm.isOpenEmbedding.locallyCompactSpace
  let bIt := (finBasis ℝ (M.coneWordIdeal CT)).map Dt.I.equiv.toLinearEquiv
  let coordIt := bIt.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans Dt.maps.chartI
  let ke := kernelRealization Dt.maps.quotient Dt.maps.inclusion
    Dt.maps.inclusion_closed Dt.maps.inclusion_range
  let : SecondCountableTopology Dt.maps.quotient.ker :=
    (coordIt.trans ke.toHomeomorph).symm.secondCountableTopology
  let : LocallyCompactSpace Dt.maps.quotient.ker :=
    (coordIt.trans ke.toHomeomorph).symm.isOpenEmbedding.locallyCompactSpace
  let : (μQ).IsHaarMeasure := Dt.measures.haarQ
  let : (μI).IsHaarMeasure := Dt.measures.haarKernel
  let : (μN).IsHaarMeasure := Dt.sectionMeasure_isHaar M F CT
    Dt.maps.sectionMap Dt.maps.section_rightInverse
  have hφ : ∀ d, MeasurePreserving (F.action d) μN μN := fun d =>
    Dt.action_preserves_sectionMeasure M F CT T hunimod hExp realize haarN haarD dynkinN
      Dt.maps.sectionMap Dt.maps.section_rightInverse d
  exact PolarTiledSamplerData.original_box_law_offset_nonpos
    (T := T) (M := M) (F := F) (hunimod := hunimod)
    (eW := eW) (K := K) (D := D) (bN := bN)
    (β := β) (Rbox := Rbox) (scale := scale) (φ := φ)
    («P» := P) (chartN := chartN) (Eall := Eall) (γ := γ)
    (δ := δ) (w := w) («S» := S) (base := base)
    (step := step) (A := A) (βtarget := βtarget) (hExp := hExp)
    (realize := realize) (haarN := haarN) (haarD := haarD) (dynkinN := dynkinN)
    (dynkinD := dynkinD) (m := m) (π := π) (hπExp := hπExp)
    (hdec := hdec) (hvan := hvan) (hΛ := hΛ) (Kπ := Kπ)
    (hπ := hπ) (hpath := hpath) (hE := hE) (hne := hne)
    (γaux := γaux) (hβ := hβ) (hweights := hweights) (c := c)
    (lo := lo) (hi := hi) (hδ := hδ) (hc := hc)
    (hhi := hhi) (ht := ht) (hcost := hcost) (hgap := hgap)
    (X := X) (d := d) (hDnil := hDnil) (hDletters := hDletters)
    (bD₀ := bD₀) (βD := βD) (hβD := hβD) (c₀ := c₀)
    (aN := aN) (hmN := hmN) (cD := cD) (aD := aD)
    (hmD := hmD) (hscale := hscale) (hmono := hmono) (hscale1 := hscale1)
    (hBE := hBE) (radius := radius) (hradius0 := hradius0) (hradius := hradius)
    (hbase := hbase) (hstep := hstep) (hφsource := hφsource) (rem := rem) (hdim := hdim) (p := p)
    (x := x) (hN := hN) (hD := hD) (pivot := pivot)
    (V := V) (hV := hV) (hVconv := hVconv) (hEc := hEc)
    (hEconv := hEconv) (hpivot := hpivot) (hEV := hEV) (hVheight := hVheight)
    (σchamber := σchamber) (hσchamber := hσchamber) (hchartN := hchartN) (Profiles := Profiles)
    (profile := profile) (hp := hp) (hactual := hactual) (law := law)
    (hlaw := hlaw) (bval := bval) (f := f) (hf := hf)
    (haffine := haffine) (haarI := haarI) (bI := bI) (hε := hε)
    (hRbox := hRbox) (hβsource := hβsource) (bItarget := bItarget) (hβtarget := hβtarget)
    (hS := hS) (Dbridge := Dbridge) (δtarget := δtarget) (hδtarget := hδtarget)
    (hDb := hDb) (hbridge := hbridge) (πT := Dt.maps.quotient) (hπT := Dt.maps.quotient_continuous)
    (μT := μQ) (μTI := μI) (μ := μN) (νD := νD)
    (hφ := hφ) (actionQ := actionQ) (act := act) (hact := hact)
    (cell := cell) (hcell := hcell) (hcell0 := hcell0) (hcelltop := hcelltop)
    (hsmall := hsmall) (regionFactory := regionFactory) (ell := ell) (hHaar := hHaar)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.measured_target_offset_nonpos_oai := @OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.measured_target_offset_nonpos_oai
