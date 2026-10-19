-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedUniformDegreeModelChain_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:32:46.629351+00:00
-- url     : https://prove2.me/submissions/26fe253a-9c91-4882-a7ca-dd21ec45ca48

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B284
import Definitions.Def_OAIE3v2B285
import Definitions.Def_OAIE3v2B286
import Definitions.Def_OAIE3v2B287

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastDataNativeProductBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_centered_forecast_twist_model
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
        Nonempty (NativeSampleModel (1 : X → ℕ) 0 localBudget
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
      (∀ i, models i ∈ twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
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
      twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
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
        Nonempty (NativeSampleModel (1 : X → ℕ) 0 commonBudget
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
    physical site hphysical slices tests (1 : X → ℕ) 0 commonBudget forecast
    hu hp hQ hmassLog hK hC hforecastCap hKp hCp hforecastCapP hthreshold hP
    hslices hsize htests hforecast hdetectCommon Term coefficient atom hatom
    (Real.exp_nonneg massLog) le_rfl hmass happrox' hexcess htail input hinput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

attribute [instance] ActualForecastData.fintypeTerm

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

theorem sharedWidthPreparedCenteredForecastModelInterface_of_radius
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
    SharedWidthPreparedCenteredForecastModelInterface
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
      (preparedModularGeneralDetectorConstants m 0) (0 + 1))).2 hMaster hLate).1).nativeBudget.1
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
  exact exists_centered_forecast_twist_model N poly budget PforecastNative hbudget hForecastNative
    μ centeredLaw hweight physical
    (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val))
    (fun _ _ => rfl) slices tests forecast hu hp hMassLog (Real.exp_nonneg _)
    hCap.1 hForecastCap hKp hCap.2 hForecastCapP hModelPrecision
    hslices.1 hslices.2 htests hForecast hmodelDetect Term coefficient centerConstant twists
    hCoeffMass hApprox hExcessCap le_rfl input hinput

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeProductiveSourceModel
namespace OAI


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
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ)
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

theorem preparedUniformDegreeModelChain_s2_oai
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) («α» := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    {D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (0 + 1)) selectedRows D)
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
    SharedWidthPreparedCenteredForecastModelInterface
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
  exact sharedWidthPreparedCenteredForecastModelInterface_of_radius
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (μ := μ)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hMaster hLate
    hu hp hSliceLog hCtail hForecastCap hForecastCapP hRadius

end Erdos3.VectorPolynomial

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedUniformDegreeModelChain_s2_oai := @OAI.Erdos3.VectorPolynomial.preparedUniformDegreeModelChain_s2_oai
