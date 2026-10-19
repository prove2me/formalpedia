-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDegreeGeometryModel_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:31:23.458946+00:00
-- url     : https://prove2.me/submissions/16e87457-8ba8-4886-bda4-f2b8c56c82bd

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B284
import Definitions.Def_OAIE3v2B285
import Definitions.Def_OAIE3v2B287
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeDirectSource_of_geometry_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

theorem centeredFiniteMarginal_sampledSliceSeminorm
    {T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (f : X → ℂ) :
    sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests f =
      ∫ c, sampledSliceSeminorm (law c) physical slices tests f ∂μ :=
  centeredFiniteMarginal_mean μ law hweight _

theorem exists_center_of_sampledSliceSeminorm
    {T X : Type*} [Fintype T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) (f : X → ℂ)
    {α : ℝ} (hα : 0 < α)
    (hlarge : α ≤ sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
      physical slices tests f) :
    ∃ c, α / 2 ≤ sampledSliceSeminorm (law c) physical slices tests f := by
  by_contra! hn
  have hi : Integrable (fun c => sampledSliceSeminorm (law c) physical slices tests f) μ :=
    centeredFinite_mean_integrable μ law hweight _ (fun _ => integrable_const _)
  rw [centeredFiniteMarginal_sampledSliceSeminorm] at hlarge
  have hle := integral_mono hi (integrable_const (α / 2)) (fun c => (hn c).le)
  simp only [integral_const, probReal_univ, one_smul] at hle
  linarith

section Joint
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem integral_norm_le_centeredFiniteMarginal
    (f : C × Ω → ℂ) (hf : Measurable f) (envelope : Ω → ℝ)
    (hbound : ∀ c z, ‖f (c, z)‖ ≤ envelope z) :
    Integrable f (centeredFiniteProbabilityMeasure μ law) ∧
      (∫ y, ‖f y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤
        (centeredFiniteMarginal μ law hweight).mean envelope := by
  classical
  let := centeredFiniteProbabilityMeasure_probability μ law hweight
  have henv (y : C × Ω) : ‖envelope y.2‖ ≤ ∑ z, ‖envelope z‖ :=
    Finset.single_le_sum (fun z _ => norm_nonneg _) (Finset.mem_univ y.2)
  have henvMeas : Measurable (fun y : C × Ω => envelope y.2) :=
    measurable_from_prod_countable_left
      (fun z => (measurable_const : Measurable (fun _ : C => envelope z)))
  have hi : Integrable f (centeredFiniteProbabilityMeasure μ law) :=
    Integrable.of_bound hf.aestronglyMeasurable _ (Filter.Eventually.of_forall (fun y =>
      (hbound y.1 y.2).trans ((le_abs_self _).trans (henv y))))
  have hei : Integrable (fun y : C × Ω => envelope y.2)
      (centeredFiniteProbabilityMeasure μ law) :=
    Integrable.of_bound henvMeas.aestronglyMeasurable _ (Filter.Eventually.of_forall henv)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y, envelope y.2 ∂centeredFiniteProbabilityMeasure μ law :=
      integral_mono hi.norm hei (fun y => hbound y.1 y.2)
    _ = ∫ c, (law c).mean envelope ∂μ :=
      centeredFiniteProbabilityMeasure_integral μ law hweight _ hei
    _ = _ := (centeredFiniteMarginal_mean μ law hweight envelope).symm

theorem integral_selected_slice_residual_le
    {T X : Type*} [Fintype T] [Nonempty T] {J : Ω → Type*}
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (tests : ∀ z, J z → T → ℂ) {K : ℝ}
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (signal : X → ℂ) (err : C × Ω → ℂ) (hmeas : Measurable err)
    (hselected : ∀ c z, ∃ j, err (c, z) =
      𝔼 t ∈ slices z j, signal (physical z t) * tests z j t) :
    Integrable err (centeredFiniteProbabilityMeasure μ law) ∧
      (∫ y, ‖err y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
          physical slices tests signal := by
  let W := fun z j => normalizedSliceTest (slices z j) (tests z j)
  have hW (z) (j) (t) : ‖W z j t‖ ≤ K :=
    normalizedSliceTest_norm_le _ _ (hsize z j) (htests z j) t
  apply integral_norm_le_centeredFiniteMarginal μ law hweight err hmeas
    (fun z => (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal)
  intro c z
  obtain ⟨j, hj⟩ := hselected c z
  rw [hj, Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove physical W hW z)]
  have he : sampledSingleTestSeminorm (physical z) (W z j) signal =
      ‖𝔼 t ∈ slices z j, signal (physical z t) * tests z j t‖ := by
    change ‖𝔼 t, signal (physical z t) * W z j t‖ = _
    rw [normalizedSliceTest_mean _ (hslices z j)]
  rw [← he]
  exact le_ciSup (Seminorm.bddAbove_range_iff.mp
    (sampledSingleTestSeminorm_bddAbove physical W hW z) signal) j

end Joint
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3

theorem forecastAugmentedUnitThreshold_half_source_precision {u p K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p) :
    Real.exp (-(2 * (u + 1) + 4 * p + 7)) ≤
      forecastAugmentedUnitThreshold u p K C Fcap / 2 := by
  calc
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp 1 := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(2 * u + 4 * p + 8)) / 2 :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
        (by linarith [Real.add_one_le_exp (1 : ℝ)])
    _ ≤ _ := div_le_div_of_nonneg_right
      (forecastAugmentedUnitThreshold_bounds hu hp hK hC hKp hCp hFp).2.2 (by norm_num)

end Erdos3

end

section

namespace Erdos3

theorem forecastAugmented_separate_source_precision {u p pSource K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hSource : 0 ≤ pSource)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hFp : Fcap ≤ Real.exp p) :
    0 ≤ u + 2 * p + 1 ∧
      Real.exp (-(2 * (u + 2 * p + 1) + 4 * pSource + 7)) ≤
        forecastAugmentedUnitThreshold u p K C Fcap / 2 := by
  refine ⟨by positivity, ?_⟩
  apply (Real.exp_le_exp.mpr
    (show -(2 * (u + 2 * p + 1) + 4 * pSource + 7) ≤
      -(2 * (u + 1) + 4 * p + 7) by linarith)).trans
  exact forecastAugmentedUnitThreshold_half_source_precision hu hp hK hC hKp hCp hFp

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_averaged_normalizedTwist_forecast_joint_model
    {Center Ω T X Forecast : Type*} [MeasurableSpace Center] [Nonempty Forecast] [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {periodCap coverCap : ℝ} {lip : ℝ≥0}
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : Measure Center) [IsProbabilityMeasure μ]
    (law : Center → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (w : X → ℕ) (degree : ℕ) (complexity : ℝ)
    (forecast : Forecast → integerBox N → ℂ)
    {u p Q P q K C forecastCap εtail M : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q) (hq : 0 ≤ q)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hforecastCapP : forecastCap ≤ Real.exp p)
    (hQlarge : 2 * u + 4 * p + q + 20 ≤ Q)
    (hP : u + 2 * p + Q + 32 ≤ P)
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f u, ‖forecast f u‖ ≤ forecastCap)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        Real.exp (-Q) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (Term : Forecast → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ) (atom : ∀ f, Term f → integerBox N → ℂ)
    (hexpansionAtoms : ∀ f i, atom f i ∈ twistedNativeSampleFunctions w degree complexity
      (fun u : integerBox N => u.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (u : integerBox N) => W.eval N poly u.val))
    (hM : 0 ≤ M) (hMq : M ≤ Real.exp q) (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ M)
    (happrox : ∀ f v, ‖forecast f v - ∑ i, coefficient f i * atom f i v‖ ≤
      (forecastAugmentedUnitThreshold u p K C forecastCap) / 8)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass ((centeredFiniteMarginal μ law hweight).siteLaw physical) C ≤ εtail)
    (htail : εtail ≤ 6 * positiveProjectionAccuracy P)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (models : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, models i ∈ twistedNativeSampleFunctions w degree complexity
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • models i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (Q + 2) ∧
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests err ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).correlation err (forecast f)‖ ≤
        Real.exp (-u)) ∧
      (nterms : ℝ) ≤ Real.exp (2 * Q + 2 * u + 4 * p + 34) ∧
      ∀ errLocal : Center × Ω → ℂ, Measurable errLocal →
        (∀ center z, ∃ j, errLocal (center, z) =
          𝔼 t ∈ slices z j, err (physical z t) * tests z j t) →
        Integrable errLocal (centeredFiniteProbabilityMeasure μ law) ∧
          (∫ y, ‖errLocal y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤ Real.exp (-u) := by
  obtain ⟨nterms, hn, models, coeff, err, hmodels, heq, hcoeff, herr, hforecasts, hterms⟩ :=
    exists_normalizedTwist_forecast_model N poly (centeredFiniteMarginal μ law hweight)
      physical site hphysical slices tests w degree complexity forecast hu hp hQ hq
      hK hC hforecastCap hKp hCp hforecastCapP hQlarge hP hsize htests hforecast
      hdetect Term coefficient atom hexpansionAtoms hM hMq hmass happrox hexcess htail input hinput
  refine ⟨nterms, hn, models, coeff, err, hmodels, heq, hcoeff, herr, hforecasts, hterms, ?_⟩
  intro errLocal hmeas hselected
  obtain ⟨hintegrable, hbound⟩ := integral_selected_slice_residual_le μ law hweight
    physical slices tests hslices hsize htests err errLocal hmeas hselected
  exact ⟨hintegrable, hbound.trans herr⟩

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredModelMarginalData
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedCenteredMarginalExponent_spec (m : ℕ) :
    2 ≤ preparedCenteredMarginalExponent m ∧
      AllocatedCenteredNarrowPrescribedMarginalStatement.{0, 0, 0, 0, 0, 0} m (preparedCenteredMarginalExponent m) :=
  (exists_allocated_centered_narrow_prescribed_marginal.{0, 0, 0, 0, 0, 0} m).choose_spec

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedWidthPreparedLateToleranceFreeTrimSource
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
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]

include μ hR hσ hb o in

theorem preparedModularGeneralCenteredDetectionFreeTrimSharedWidth_of_direct
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    PreparedModularGeneralCenteredDetectionFreeTrimSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
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
      0 < selectedJointDensityMass bases stride cells V
        (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center) := by
    obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
    let pc := fun j => subtractConstant (c j).val (poly j)
    let hmc := fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)
    obtain ⟨_, _, _, _, hnormc, _, _⟩ := hprimitive cells pc
      (preparedModularGeneralCentered_degree U poly hp c) hmc hsize
      (preparedModularGeneralCentered_rank U poly (fun i => (N i : ℝ)) Rrank hrank c)
      hRank hCells
    have hdensity := allocatedJointBaseDensity_subtractConstant_centered
      B U basis hb o hR hσ S poly hmem center c hc
    have hpos := hnormc.2.2.1
    change 0 < selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) pc hmc) at hpos
    rw [hdensity] at hpos
    exact hpos
  refine ⟨hcenter, ?_⟩
  intro centeredLaw
  have hweight (z : Path) : Measurable (fun center => (centeredLaw center).weight z) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem)
      (allocatedCenteredJointDensity_measurable_center B U basis hb o hR hσ S poly hmem)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem) hcenter z
  refine ⟨hweight, ?_⟩
  intro pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices
    cdetect stepdetect Hdetect hstep hboxDetect hdense hdimension hcomplexity hcap budget
    signal hα hsignal hzero hlarge
  obtain ⟨center, hlargeCenter⟩ := exists_center_of_sampledSliceSeminorm μ centeredLaw hweight
    (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
    (fun z j t => star ((Vdetect z j).eval
      (commonStrideIndex (cdetect z j) (stepdetect z j) (e t)))) signal hα hlarge
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
  let pc := fun j => subtractConstant (c j).val (poly j)
  let hmc := fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)
  obtain ⟨hNc, hbasesc, hboxc, hmassc, hnormc, hmargin, hdetector⟩ :=
    hprimitive cells pc (preparedModularGeneralCentered_degree U poly hp c) hmc hsize
      (preparedModularGeneralCentered_rank U poly (fun i => (N i : ℝ)) Rrank hrank c)
      hRank hCells
  have hlaw := allocatedOriginalPathLaw_subtractConstant_eq_centered
    B U basis hb o hR hσ S poly hmem N hN hW hτSpatial hξn stride cells hmass bases hbases
    center c hc hnormc.2.2.1 (hcenter center)
  change α / 2 ≤ sampledSliceSeminorm
    (selectedJointFiniteLaw bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center)
      (hcenter center))
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedWidthPreparedPerturbativeCertifiedSource
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
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
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
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

include μ ν hR hσ hb o in

theorem sharedWidthPreparedCenteredModelMarginalData_of_direct
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    SharedWidthPreparedCenteredModelMarginalDataInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff Pmarginal E hPm hmSize hK hX hdim
    hChartPm hStridePm hPhysicalPm hRP hσP hcount hI hn hJ hLP hσone hsmall
    hτSpatial hτInv hτHalf hτDim r W ξn hξn hξle hξLate hW hWP hξone hξInv required
    cells poly hp hmem Rrank hsize hrank hRank V hCells bases Z
  have hsizeDirect (i) : Real.exp r.required ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans (hsize i)
  have hRankDirect : Real.exp r.required ≤ Rrank :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans hRank
  have hsizeMarginal (i) :
      Real.exp ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans (hsize i)
  have hRankMarginal :
      Real.exp ((max Pmarginal E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m) ≤ Rrank :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans hRank
  have hCentered := preparedModularGeneralCenteredDetectionFreeTrimSharedWidth_of_direct
    B U basis hR hσ S selection stride N Pdetect u pModel pSlice Vtail α τ hb o μ
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hDirect
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hcenter, hweight, hdetect⟩ :=
    hCentered hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff hτSpatial hτInv hτHalf hτDim
      hξn hξle hξLate cells poly hp hmem hsizeDirect hrank hRankDirect hCells
  have hchartExp := Real.exp_le_exp.mpr hChartPm
  obtain ⟨_, _, _, _, _, hnormalizerCenter, hweightMarginal, hsite⟩ :=
    (preparedCenteredMarginalExponent_spec m).2 B U basis S hb o μ ν hR hσ hσone
      Cforward Vtail hforward hVactual C hC hchart hsmall
      hPm hmSize hK hX hdim hRP hσP hcount hI hn hJ
      (hprofile.trans hchartExp) hLP (fun j => (hForward j).trans hchartExp)
      (fun j => (hVtail j).trans hchartExp) poly hp hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr hStridePm))
      hW hWP hτSpatial (hτInv.trans (Real.exp_le_exp.mpr hPhysicalPm)) hτHalf
      (by simpa only [Fintype.card_fin] using hτDim) hξn hξone hξInv
      N hsizeMarginal hrank hRankMarginal cells hCells
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path Zcenter
  refine ⟨hnormalizerCenter, ?_⟩
  intro centeredLaw
  refine ⟨hweight, ?_⟩
  intro pathLaw sides Sites e hrootSum physical
  let : Nonempty Sites := by
    have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
      cases k with
      | inl g => exact S.positive
      | inr j => exact allocatedPrincipalSides_pos B U basis S j
    let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
    exact (integerBox_nonempty sides).to_subtype
  constructor
  · exact hsite e (fun t k => (allocatedParameterBox_coordinate_bound B U basis S t k).trans hLP)
      (fun t => allocatedParameterBox_root_bound B U basis S t)
  · exact hdetect

include μ ν hR hσ hb o in

theorem sharedWidthPreparedCenteredModelMarginalProjectionData_of_direct
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    {D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hD : D ≤ Pmaster) (hnX : (nX : ℝ) ≤ Pmaster)
    (hChartMaster : Pchart ≤ Pmaster) (hStrideMaster : Qstride ≤ Pmaster)
    (hPhysicalMaster : Pphysical ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate) (hσone : ∀ j, σ j ≤ 1) :
    SharedWidthPreparedCenteredModelMarginalProjectionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff E hsmall hτSpatial hτInv hτHalf hτDim
    r W ξn hξn hξle hξLate hW hξone Pmarginal required
  have hbnd := preparedCenteredMarginalProjectionBounds B U basis S o hMaster hLate hd hD
    hnX hRP hσLate hLLate
  have h := sharedWidthPreparedCenteredModelMarginalData_of_direct
    B U basis hR hσ S selection stride N Pdetect u pModel pSlice Vtail α τ hb o ν μ
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hDirect
  exact h hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff hbnd.Pproj_nonneg hbnd.m_projection
    hbnd.variables_projection hbnd.X_projection hbnd.frame_projection
    (hChartMaster.trans hbnd.master_projection) (hStrideMaster.trans hbnd.master_projection)
    (hPhysicalMaster.trans hbnd.master_projection) hbnd.Rinv_projection hbnd.σinv_projection
    hbnd.coefficient_projection hbnd.I_projection hbnd.n_projection hbnd.J_projection
    hbnd.S_projection hσone hsmall hτSpatial hτInv hτHalf hτDim
    hξn hξle hξLate hbnd.root_projection hξone (hξLate.trans (Real.exp_le_exp.mpr hbnd.late_projection))

omit [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [μ.IsAddLeftInvariant] in

theorem sharedWidthPreparedCenteredModelMarginalRadiusInterface_of_projection
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hProjection : SharedWidthPreparedCenteredModelMarginalProjectionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    (hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Pchart) →
      ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) :
    SharedWidthPreparedCenteredModelMarginalRadiusInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff E
  exact hProjection hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff (E := E) (hsmall C hC hCbound)

end Consumer
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteForwardDegreeModelAttachment
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_centered_forecast_twist_model_degree (s : ℕ)
    {Center Ω T X Forecast : Type*} [MeasurableSpace Center] [Nonempty Forecast] [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (localBudget Pnative : ℝ) (hlocalBudget : 0 ≤ localBudget) (hPnative : 0 ≤ Pnative)
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : Measure Center) [IsProbabilityMeasure μ]
    (law : Center → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (forecast : Forecast → integerBox N → ℂ)
    {u p P massLog K C forecastCap εtail : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hmassLog : 0 ≤ massLog)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hforecastCapP : forecastCap ≤ Real.exp p)
    (hP : u + 2 * p +
      max (max localBudget (3 * Pnative + 3)) (2 * u + 4 * p + massLog + 20) + 32 ≤ P)
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f u, ‖forecast f u‖ ≤ forecastCap)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp localBudget) (Real.exp localBudget)
          ⟨Real.exp localBudget, Real.exp_nonneg _⟩)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (1 : X → ℕ) s localBudget
          (fun u : integerBox N => u.val) G) ∧
        Real.exp (-localBudget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (Term : Forecast → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ)
    (centerConstant : Forecast → ∀ j, J j → ℝ)
    (twists : ∀ f, Term f → NormalizedPolynomialTwist X (Σ j, J j)
      (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩)
    (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ Real.exp massLog)
    (happrox : ∀ f v, ‖forecast f v - ∑ i, coefficient f i *
      (twists f i).eval N (fun j => subtractConstant (centerConstant f j) (poly j)) v.val‖ ≤
        Real.exp (-(2 * u + 4 * p + 12)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass ((centeredFiniteMarginal μ law hweight).siteLaw physical) C ≤ εtail)
    (htail : εtail ≤ 6 * positiveProjectionAccuracy P)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Q := max commonBudget (2 * u + 4 * p + massLog + 20)
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (models : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, models i ∈ twistedNativeSampleFunctions (1 : X → ℕ) s commonBudget
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • models i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (Q + 2) ∧
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests err ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).correlation err (forecast f)‖ ≤
        Real.exp (-u)) ∧
      (nterms : ℝ) ≤ Real.exp (2 * Q + 2 * u + 4 * p + 34) ∧
      ∀ errLocal : Center × Ω → ℂ, Measurable errLocal →
        (∀ center z, ∃ j, errLocal (center, z) =
          𝔼 t ∈ slices z j, err (physical z t) * tests z j t) →
        Integrable errLocal (centeredFiniteProbabilityMeasure μ law) ∧
          (∫ y, ‖errLocal y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤ Real.exp (-u) := by
  intro commonBudget Q
  have hlocalCommon : localBudget ≤ commonBudget := le_max_left _ _
  have hcommon : 0 ≤ commonBudget := hlocalBudget.trans hlocalCommon
  obtain ⟨hQ, _, hcommonQ, hthreshold, hgain, _⟩ :=
    forecastAugmented_model_parameters hu hp hmassLog hcommon
  let shifted := fun f i => (twists f i).shiftConstant (centerConstant f)
  let atom := fun f i (v : integerBox N) => (shifted f i).eval N poly v.val
  have hatom (f) (i) : atom f i ∈
      twistedNativeSampleFunctions (1 : X → ℕ) s commonBudget
        (fun v : integerBox N => v.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩) v => W.eval N poly v.val) :=
    centeredForecastTwist_mem_common_family localBudget Pnative hPnative
      twists N poly centerConstant f i
  have happrox' (f) (v : integerBox N) :
      ‖forecast f v - ∑ i, coefficient f i * atom f i v‖ ≤
        forecastAugmentedUnitThreshold u p K C forecastCap / 8 := by
    have he := (happrox f v).trans (forecastAugmented_approximation_precision
      hu hp hK (zero_le_one.trans hC) hKp hCp hforecastCapP)
    change ‖forecast f v - ∑ i, coefficient f i *
      ((twists f i).shiftConstant (centerConstant f)).eval N poly v.val‖ ≤ _
    rw [centeredForecastTwist_sum_eq twists coefficient N poly centerConstant f v.val]
    exact he
  have hdetectCommon (signal : (X → ℤ) → ℂ)
      (hsignal : ∀ v, ‖signal v‖ ≤ 1)
      (hzero : ∀ v, v ∉ integerBox N → signal v = 0)
      (hlarge : forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) site slices tests signal) :
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩) (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (1 : X → ℕ) s commonBudget
          (fun v : integerBox N => v.val) G) ∧
        Real.exp (-Q) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun v => signal v.val)
          (fun v => star (W.eval N poly v.val) * G v)‖ := by
    obtain ⟨W, G, hG, hc⟩ := hdetect signal hsignal hzero hlarge
    have he : Real.exp localBudget ≤ Real.exp commonBudget := Real.exp_le_exp.mpr hlocalCommon
    let W' := W.mono he he
      (show (⟨Real.exp localBudget, Real.exp_nonneg _⟩ : ℝ≥0) ≤
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩ from he)
    refine ⟨W', G, hG.map (fun model => model.mono hlocalCommon), ?_⟩
    exact hgain.trans ((Real.exp_le_exp.mpr (neg_le_neg hlocalCommon)).trans hc)
  exact exists_averaged_normalizedTwist_forecast_joint_model N poly μ law hweight
    physical site hphysical slices tests (1 : X → ℕ) s commonBudget forecast
    hu hp hQ hmassLog hK hC hforecastCap hKp hCp hforecastCapP hthreshold hP
    hslices hsize htests hforecast hdetectCommon Term coefficient atom hatom
    (Real.exp_nonneg massLog) le_rfl hmass happrox' hexcess htail input hinput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

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
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ u p forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap
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
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

omit [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [μ.IsAddLeftInvariant] in

theorem sharedWidthPreparedCenteredForecastModelDegreeInterface_of_radius
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hCtail : Ctail ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p)
    (hSource : SharedWidthPreparedCenteredModelMarginalRadiusInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) («α» := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    SharedWidthPreparedCenteredForecastModelDegreeInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff E hτSpatial hτInv hτHalf hτDim
    r W ξn hξn hξle hξLate hW hξone Pmarginal required cells poly hpoly hmem Rrank
    hsize hrank hRank V hCells bases Z
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hnormalizerCenter, hweight,
      hexcess, hdetect⟩ :=
    hSource hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff (E := E) hτSpatial hτInv hτHalf hτDim
      hξn hξle hξLate cells poly hpoly hmem hsize hrank hRank hCells
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path Zcenter
  refine ⟨hnormalizerCenter, ?_⟩
  intro centeredLaw
  refine ⟨hweight, ?_⟩
  intro pathLaw sides Sites e hrootSum physical
  let : Nonempty Sites := by
    have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
      cases k with
      | inl g => exact S.positive
      | inr j => exact allocatedPrincipalSides_pos B U basis S j
    let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
    exact (integerBox_nonempty sides).to_subtype
  refine ⟨hexcess, ?_⟩
  intro Tests instTests Ldetect instLie instAlg dims instTopo instAdd instSmul instT2
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hSlices hDense
    hnum hcomplex hcap budget tests Forecast instForecast forecast PforecastNative massLog
    hForecastNative hMassLog hModelPrecision Term instTerm coefficient centerConstant twists
    hCoeffMass hApprox hForecast input hinput
  let : ∀ i, NeZero (N i) := fun i => ⟨(hN i).ne'⟩
  have hKp : Kslice ≤ Real.exp p := Real.exp_le_exp.mpr hSliceLog
  have hCap := marginalCap_max_one_exp_bound hp hCtail
  have hα : 0 < α := (forecastAugmentedUnitThreshold_bounds hu hp
    (Real.exp_nonneg _) (zero_le_one.trans hCap.1) hKp hCap.2 hForecastCapP).1
  have hbudget : 0 ≤ budget :=
    (((Classical.choose_spec (exists_preparedModularGeneralDetector_resource_budget
      (preparedModularGeneralDetectorConstants m s) (s + 1))).2 hMaster hLate).1).nativeBudget.1
  have hslices := preparedCenteredForecast_slice_family_bounds B U basis S slices hDense
  have htests (z) (j) (t : Sites) : ‖tests z j t‖ ≤ 1 :=
    preparedCenteredForecast_niltest_star_eval_bound (Vdetect z j) (hcap z j)
      (commonStrideIndex (cdetect z j) (stepdetect z j) (e t))
  have hmodelDetect (signal : (Fin nX → ℤ) → ℂ)
      (hsignal : ∀ t, ‖signal t‖ ≤ 1)
      (hzero : ∀ t, t ∉ integerBox N → signal t = 0)
      (hlarge : α ≤ sampledSliceSeminorm pathLaw
        (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices tests signal) :=
    hdetect Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hSlices hDense
      hnum hcomplex hcap signal hα hsignal hzero hlarge
  have hExcessCap := (FiniteProbabilityWeights.excessMass_max_one_le
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox)
    (pathLaw.siteLaw physical) Ctail).trans hexcess
  exact exists_centered_forecast_twist_model_degree s N poly budget PforecastNative hbudget hForecastNative
    μ centeredLaw hweight physical
    (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val))
    (fun _ _ => rfl) slices tests forecast hu hp hMassLog (Real.exp_nonneg _)
    hCap.1 hForecastCap hKp hCap.2 hForecastCapP hModelPrecision
    hslices.1 hslices.2 htests hForecast hmodelDetect Term coefficient centerConstant twists
    hCoeffMass hApprox hExcessCap le_rfl input hinput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Chain

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ u p forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

include ν in

theorem preparedUniformDegreeModelChainDegree
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) («α» := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    {D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hD : D ≤ Pmaster) (hnX : (nX : ℝ) ≤ Pmaster)
    (hChartMaster : Pchart ≤ Pmaster) (hStrideMaster : Qstride ≤ Pmaster)
    (hPhysicalMaster : Pphysical ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate) (hσone : ∀ j, σ j ≤ 1)
    (hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Pchart) →
      ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hCtail : Ctail ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p) :
    SharedWidthPreparedCenteredForecastModelDegreeInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  have hProjection := sharedWidthPreparedCenteredModelMarginalProjectionData_of_direct
    B U basis hR hσ S selection stride N Pdetect uSource pModel pSlice Vtail α τ hb o ν μ
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hDirect hMaster hLate
    hd hD hnX hChartMaster hStrideMaster hPhysicalMaster hRP hσLate hLLate hσone
  have hRadius := sharedWidthPreparedCenteredModelMarginalRadiusInterface_of_projection
    B U basis hR hσ S selection stride N Pdetect uSource pModel pSlice Vtail α τ hb o μ
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hProjection hsmall
  exact sharedWidthPreparedCenteredForecastModelDegreeInterface_of_radius
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (μ := μ)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hMaster hLate
    hu hp hSliceLog hCtail hForecastCap hForecastCapP hRadius

end Chain

section Geometry

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
variable (u p : ℝ)
local notation "uSource" => u + 2 * p + 1
variable (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog uSource pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
include ν bW in

theorem preparedUniformDegreeGeometryModelDegree (hsm : s ≤ m)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant s Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius uSource pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s
      (sampledSupportedSlicedDetectionConstant s Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * uSource + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hCtail : Ctail ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p) :
    SharedWidthPreparedCenteredForecastModelDegreeInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) («uSource» := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget ∧
    (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect pDetect pDetect (α / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate := by
  let : CompactSpace (CoefficientTorus (K := Fin (s + 1)) U) :=
    coefficientTorus_compact_of_lattice U
  let : MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U) := borel _
  let : BorelSpace (CoefficientTorus (K := Fin (s + 1)) U) := ⟨rfl⟩
  let : MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U) := borel _
  let : BorelSpace (SiteTorus (Finset (Fin (s + 1))) U) := ⟨rfl⟩
  have hKp : Kslice ≤ Real.exp p := Real.exp_le_exp.mpr hSliceLog
  have hCap := marginalCap_max_one_exp_bound hp hCtail
  have hC : 0 ≤ max 1 Ctail := zero_le_one.trans hCap.1
  have hαlower := (forecastAugmented_separate_source_precision hu hp scalar.model_master.1
    (Real.exp_nonneg _) hC hKp hCap.2 hForecastCapP).2
  have hαone : α / 2 ≤ 1 := by
    have h := (forecastAugmentedUnitThreshold_bounds hu hp
      (Real.exp_nonneg _) hC hKp hCap.2 hForecastCapP).2.1
    linarith only [h]
  have hDirect := preparedUniformDegreeDirectSource_of_geometry_s2
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) («α» := α / 2) (τ := τ)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := probabilityAddHaar (CoefficientTorus (K := Fin (s + 1)) U))
    hsm Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain
    Pphysical coarseTarget pRadius scalar geometryAt hRone hRinv hσone hSLate
    hBa hBi hcapacity hαlower hαone
  obtain ⟨⟨geometry⟩, hgainKernel⟩ := geometryAt
  constructor
  · exact preparedUniformDegreeModelChainDegree
      (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) («uSource» := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (ν := ν) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hDirect
      scalar.master_nonneg scalar.late geometry.hdimensions scalar.dimension_master
      scalar.ambient_master scalar.chart_master scalar.stride_master.2 scalar.physical_master.2
      (fun j => (hRinv j).trans (Real.exp_le_exp.mpr scalar.radius_master))
      (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr scalar.scale_late))
      hSLate hσone (fun C hC hBound => (geometry.hbudgets C hC hBound).1)
      hu hp hSliceLog hCtail hForecastCap hForecastCapP
  · have hMk := (hgainKernel (α / 2) hαlower).2.1
    have hCoarse : 0 ≤ coarseTarget := by
      linarith only [scalar.gain_master.1, scalar.coarse_lower]
    have hwidth := preparedModularDetector_narrow_width B selection scalar.physical_master.1
      hCoarse (hMk.trans (Real.exp_le_exp.mpr scalar.kernel_physical))
      scalar.detector_physical scalar.variables_physical scalar.ambient_physical
    exact hwidth.2.trans (Real.exp_le_exp.mpr scalar.xi_late)

end Geometry

section Availability

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
variable (sourceU : ℝ)
variable (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog sourceU pModel
variable (τ : ℝ)

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include ν bW in

theorem preparedFiniteScheduleDegreeGeometryModel_s2_oai
    (Cdetect : ℕ)
    (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant s Pdetect)
    (hsm : s ≤ m)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G) :
    PreparedScheduledDegreeModelAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro u p forecastCap hsource hu hp hslice htail hcap hcapP
  rw [hCdetect, hsource] at scalar geometryAt
  rw [hsource]
  exact preparedUniformDegreeGeometryModelDegree
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ)
    hsm Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius
    scalar geometryAt hRone hRinv hσone hSLate hBa hBi hcapacity
    hu hp hslice htail hcap hcapP

end Availability

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDegreeGeometryModel_s2_oai := @OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDegreeGeometryModel_s2_oai
