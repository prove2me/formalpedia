-- Prove2me | solution 1 for OAI.CircleDomainRigidity.MatchedConformalEnds.normalized_identity_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:59:10.927044+00:00
-- url     : https://prove2.me/submissions/2eb1ac40-6478-43de-89f3-71e214eb834b

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010

section
-- module Solutions.Q146_CD.CircleDomains_LengthArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle domains, conformal removability, and conditional analytic rigidity from length and area estimates. -/

noncomputable section
open Set Classical
open scoped OnePoint

open MeasureTheory Filter Bornology
open scoped Topology
namespace CircleDomainRigidity.LengthArea

theorem summable_mul_of_squares {ι : Type*} {r s : ι → ℝ}
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2)) :
    Summable (fun j ↦ r j * s j) := by
  apply (hr.add hs).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|r j| - |s j|), sq_abs (r j), sq_abs (s j),
    sq_nonneg (r j), sq_nonneg (s j)]

theorem hasSum_square_discrepancy {ι : Type*} {r s : ι → ℝ}
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2)) :
    HasSum (fun j ↦ (r j - s j) ^ 2)
      ((∑' j, r j ^ 2) - 2 * (∑' j, r j * s j) + (∑' j, s j ^ 2)) := by
  have hp := summable_mul_of_squares hr hs
  convert! (hr.hasSum.sub (hp.hasSum.mul_left 2)).add hs.hasSum using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  ring

theorem discrepancy_nonpos {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    {u : X → ℝ} {r s : ι → ℝ} {A : ℝ}
    (hu : Integrable u μ) (hu2 : Integrable (fun x ↦ u x ^ 2) μ)
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2))
    (hsource : (∫ _, (1 : ℝ) ∂μ) + Real.pi * (∑' j, r j ^ 2) ≤ A)
    (htarget : (∫ x, u x ^ 2 ∂μ) + Real.pi * (∑' j, s j ^ 2) ≤ A)
    (hflux : 2 * A ≤ 2 * (∫ x, u x ∂μ) + 2 * Real.pi * (∑' j, r j * s j)) :
    (∫ x, (u x - 1) ^ 2 ∂μ) + Real.pi * (∑' j, (r j - s j) ^ 2) ≤ 0 := by
  have hpoly : (fun x ↦ (u x - 1) ^ 2) =
      (fun x ↦ (u x ^ 2 - 2 * u x) + 1) := by
    funext x
    ring
  have hsub : Integrable (fun x ↦ u x ^ 2 - 2 * u x) μ := hu2.sub (hu.const_mul 2)
  rw [hpoly, integral_add hsub (integrable_const 1),
    integral_sub hu2 (hu.const_mul 2), integral_const_mul,
    (hasSum_square_discrepancy hr hs).tsum_eq]
  nlinarith

theorem equality_of_estimates {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    {u : X → ℝ} {r s : ι → ℝ} {A : ℝ}
    (hu : Integrable u μ) (hu2 : Integrable (fun x ↦ u x ^ 2) μ)
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2))
    (hsource : (∫ _, (1 : ℝ) ∂μ) + Real.pi * (∑' j, r j ^ 2) ≤ A)
    (htarget : (∫ x, u x ^ 2 ∂μ) + Real.pi * (∑' j, s j ^ 2) ≤ A)
    (hflux : 2 * A ≤ 2 * (∫ x, u x ∂μ) + 2 * Real.pi * (∑' j, r j * s j)) :
    (u =ᵐ[μ] fun _ ↦ 1) ∧ (∀ j, r j = s j) := by
  have hd := discrepancy_nonpos hu hu2 hr hs hsource htarget hflux
  have hi : 0 ≤ ∫ x, (u x - 1) ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  have ht : 0 ≤ ∑' j, (r j - s j) ^ 2 := tsum_nonneg fun j ↦ sq_nonneg _
  have hp : 0 ≤ Real.pi * (∑' j, (r j - s j) ^ 2) := mul_nonneg Real.pi_pos.le ht
  have hiz : (∫ x, (u x - 1) ^ 2 ∂μ) = 0 := by linarith
  have htz : (∑' j, (r j - s j) ^ 2) = 0 := by nlinarith [Real.pi_pos]
  have hint : Integrable (fun x ↦ (u x - 1) ^ 2) μ := by
    convert! (hu2.sub (hu.const_mul 2)).add (integrable_const 1) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  constructor
  · have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (u x - 1)) hint).mp hiz
    filter_upwards [hae] with x hx
    have h : u x - 1 = 0 := sq_eq_zero_iff.mp hx
    linarith
  · intro j
    have hle := (hasSum_square_discrepancy hr hs).summable.le_tsum j
      (fun k _ ↦ sq_nonneg (r k - s k))
    rw [htz] at hle
    nlinarith [sq_nonneg (r j - s j)]

theorem norm_deriv_eq_one_of_ae {f : ℂ → ℂ} {D W : Set ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hW : IsOpen W) (hWD : W ⊆ D)
    (hae : (fun z ↦ ‖deriv f z‖) =ᵐ[volume.restrict W] fun _ ↦ 1) :
    ∀ z ∈ W, ‖deriv f z‖ = 1 :=
  Measure.eqOn_open_of_ae_eq hae hW ((hf.deriv hD).continuousOn.norm.mono hWD) continuousOn_const

theorem affine_of_unit_derivative_on_open {f : ℂ → ℂ} {D W : Set ℂ}
    (hD : IsOpen D) (hc : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hW : IsOpen W) (hne : W.Nonempty) (hWD : W ⊆ D)
    (hnorm : ∀ z ∈ W, ‖deriv f z‖ = 1) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z ∈ D, f z = a * z + b := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hd : DifferentiableOn ℂ (deriv f) D := hf.deriv hD
  have hevent : (deriv f) =ᶠ[𝓝 z₀] fun _ ↦ deriv f z₀ := by
    apply Complex.eventually_eq_of_isLocalMax_norm
    · exact hd.eventually_differentiableAt (hD.mem_nhds (hWD hz₀))
    · filter_upwards [hW.mem_nhds hz₀] with z hz
      change ‖deriv f z‖ ≤ ‖deriv f z₀‖
      rw [hnorm z hz, hnorm z₀ hz₀]
  have heq : EqOn (deriv f) (fun _ ↦ deriv f z₀) D :=
    (hd.analyticOnNhd hD).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      hc (hWD hz₀) hevent
  have hlin : Differentiable ℂ (fun z : ℂ ↦ deriv f z₀ * z) :=
    differentiable_id.const_mul _
  have heq' : EqOn (deriv f) (deriv (fun z : ℂ ↦ deriv f z₀ * z)) D := by
    intro z hz
    simpa using heq hz
  obtain ⟨b, hb⟩ := hD.exists_eq_add_of_deriv_eq hc hf hlin.differentiableOn heq'
  exact ⟨deriv f z₀, b, hnorm z₀ hz₀, hb⟩

theorem affine_coefficients_of_principal_normalization {a b : ℂ}
    (hlim : Tendsto (fun z : ℂ ↦ a * z + b - z) (cobounded ℂ) (𝓝 0)) :
    a = 1 ∧ b = 0 := by
  have hinv : Tendsto (fun z : ℂ ↦ z⁻¹) (cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have hprod : Tendsto (fun z : ℂ ↦ (a * z + b - z) * z⁻¹)
      (cobounded ℂ) (𝓝 0) := by simpa using hlim.mul hinv
  have hne : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := isBounded_singleton
  have heq : (fun z : ℂ ↦ (a * z + b - z) * z⁻¹) =ᶠ[cobounded ℂ]
      (fun z ↦ (a - 1) + b * z⁻¹) := by
    filter_upwards [hne] with z hz
    simp only [sub_mul, add_mul, mul_assoc, mul_inv_cancel₀ hz, mul_one]
    ring
  have ha_lim : Tendsto (fun z : ℂ ↦ (a - 1) + b * z⁻¹)
      (cobounded ℂ) (𝓝 (a - 1)) := by
    simpa using tendsto_const_nhds.add (hinv.const_mul b)
  have ha : a = 1 := sub_eq_zero.mp (tendsto_nhds_unique ha_lim (hprod.congr' heq))
  refine ⟨ha, ?_⟩
  have hb_lim : Tendsto (fun _ : ℂ ↦ b) (cobounded ℂ) (𝓝 0) := by
    simpa [ha] using hlim
  exact tendsto_nhds_unique tendsto_const_nhds hb_lim

theorem eq_id_of_affine_and_principal_normalization {f : ℂ → ℂ}
    {D : Set ℂ} {a b : ℂ} (hD : IsBounded Dᶜ)
    (haffine : ∀ z ∈ D, f z = a * z + b)
    (hlim : Tendsto (fun z : ℂ ↦ f z - z) (cobounded ℂ) (𝓝 0)) :
    ∀ z ∈ D, f z = z := by
  have hmem : ∀ᶠ z : ℂ in cobounded ℂ, z ∈ D := by
    simpa only [eventually_mem_set, isBounded_def, compl_compl] using hD
  have he : (fun z : ℂ ↦ f z - z) =ᶠ[cobounded ℂ] (fun z ↦ a * z + b - z) := by
    filter_upwards [hmem] with z hz
    rw [haffine z hz]
  obtain ⟨ha, hb⟩ := affine_coefficients_of_principal_normalization (hlim.congr' he)
  intro z hz
  simpa [ha, hb] using haffine z hz

theorem affine_of_length_area_estimates {ι : Type*} {f : ℂ → ℂ} {D W : Set ℂ}
    {r s : ι → ℝ} {A : ℝ}
    (hD : IsOpen D) (hc : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hW : IsOpen W) (hne : W.Nonempty) (hbW : IsBounded W) (hWD : W ⊆ D)
    (hi : Integrable (fun z ↦ ‖deriv f z‖) (volume.restrict W))
    (hi2 : Integrable (fun z ↦ ‖deriv f z‖ ^ 2) (volume.restrict W))
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2))
    (hsource : (∫ _ in W, (1 : ℝ)) + Real.pi * (∑' j, r j ^ 2) ≤ A)
    (htarget : (∫ z in W, ‖deriv f z‖ ^ 2) + Real.pi * (∑' j, s j ^ 2) ≤ A)
    (hflux : 2 * A ≤ 2 * (∫ z in W, ‖deriv f z‖) +
      2 * Real.pi * (∑' j, r j * s j)) :
    (∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z ∈ D, f z = a * z + b) ∧ (∀ j, r j = s j) := by
  let : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.mpr hbW.measure_lt_top.ne
  obtain ⟨hae, heq⟩ := equality_of_estimates hi hi2 hr hs hsource htarget hflux
  have hnorm := norm_deriv_eq_one_of_ae hD hf hW hWD hae
  exact ⟨affine_of_unit_derivative_on_open hD hc hf hW hne hWD hnorm, heq⟩

theorem identity_of_length_area_estimates {ι : Type*} {f : ℂ → ℂ} {D W : Set ℂ}
    {r s : ι → ℝ} {A : ℝ}
    (hD : IsOpen D) (hc : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hDinf : IsBounded Dᶜ)
    (hlim : Tendsto (fun z : ℂ ↦ f z - z) (cobounded ℂ) (𝓝 0))
    (hW : IsOpen W) (hne : W.Nonempty) (hbW : IsBounded W) (hWD : W ⊆ D)
    (hi : Integrable (fun z ↦ ‖deriv f z‖) (volume.restrict W))
    (hi2 : Integrable (fun z ↦ ‖deriv f z‖ ^ 2) (volume.restrict W))
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2))
    (hsource : (∫ _ in W, (1 : ℝ)) + Real.pi * (∑' j, r j ^ 2) ≤ A)
    (htarget : (∫ z in W, ‖deriv f z‖ ^ 2) + Real.pi * (∑' j, s j ^ 2) ≤ A)
    (hflux : 2 * A ≤ 2 * (∫ z in W, ‖deriv f z‖) +
      2 * Real.pi * (∑' j, r j * s j)) :
    (∀ z ∈ D, f z = z) ∧ (∀ j, r j = s j) := by
  obtain ⟨⟨a, b, _, hab⟩, heq⟩ :=
    affine_of_length_area_estimates hD hc hf hW hne hbW hWD
      hi hi2 hr hs hsource htarget hflux
  exact ⟨eq_id_of_affine_and_principal_normalization hDinf hab hlim, heq⟩

end CircleDomainRigidity.LengthArea

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BandIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted dust incidence

This is the dust part of `eq:weighted-level-bound` in Section 1 of
`047-02`. A point contributes its weight on a measurable set of levels.
Tonelli converts the expected total incidence to the sum of weights
times level probabilities; the band-incidence estimate bounds these
probabilities, and square summability makes the result finite.
-/

open Set MeasureTheory Filter
open scoped ENNReal

namespace CircleDomainRigidity

theorem measurable_weightedBandIncidence {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (E : ι → Set T) (m : ι → ℝ) (hE : ∀ s, MeasurableSet (E s)) :
    Measurable (weightedBandIncidence E m) :=
  Measurable.tsum (fun s => measurable_const.indicator (hE s))

theorem weightedBandIncidence_toReal_eq {T ι : Type*}
    (E : ι → Set T) (m : ι → ℝ) (hm : ∀ s, 0 ≤ m s) (t : T) :
    (weightedBandIncidence E m t).toReal = ∑' s, (E s).indicator (fun _ => m s) t := by
  classical
  rw [weightedBandIncidence, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro s
    by_cases ht : t ∈ E s
    · simp only [indicator_of_mem ht, ENNReal.toReal_ofReal (hm s)]
    · simp only [indicator_of_notMem ht, ENNReal.toReal_zero]
  · intro s
    by_cases ht : t ∈ E s
    · simpa only [indicator_of_mem ht] using ENNReal.ofReal_ne_top
    · simp only [indicator_of_notMem ht, ne_eq, ENNReal.zero_ne_top, not_false_eq_true]

/-- Tonelli's exact incidence identity. -/
theorem lintegral_weightedBandIncidence {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m : ι → ℝ) (hE : ∀ s, MeasurableSet (E s)) :
    ∫⁻ t, weightedBandIncidence E m t ∂ν = ∑' s, ENNReal.ofReal (m s) * ν (E s) := by
  unfold weightedBandIncidence
  rw [lintegral_tsum]
  · apply tsum_congr
    intro s
    exact lintegral_indicator_const (hE s) _
  · intro s
    exact (measurable_const.indicator (hE s)).aemeasurable

/-- The band probability bound yields the weighted-level dust estimate. -/
theorem lintegral_weightedBandIncidence_le {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m a : ι → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, ν (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    ∫⁻ t, weightedBandIncidence E m t ∂ν ≤ ENNReal.ofReal (∑' s, m s * a s) := by
  rw [lintegral_weightedBandIncidence ν E m hE]
  have hs := LengthArea.summable_mul_of_squares hm2 ha2
  have hnonneg (s) : 0 ≤ m s * a s := mul_nonneg (hm s) (ha s)
  rw [ENNReal.ofReal_tsum_of_nonneg hnonneg hs]
  apply ENNReal.tsum_le_tsum
  intro s
  rw [ENNReal.ofReal_mul (hm s)]
  exact mul_le_mul_right (hband s) _

theorem lintegral_weightedBandIncidence_lt_top
    {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m a : ι → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, ν (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    ∫⁻ t, weightedBandIncidence E m t ∂ν < ∞ :=
  (lintegral_weightedBandIncidence_le ν E m a hE hm ha hband hm2 ha2).trans_lt
    ENNReal.ofReal_lt_top

/-- The weighted series is summable at almost every level. -/
theorem ae_summable_weighted_band_series
    {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m a : ι → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, ν (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    ∀ᵐ t ∂ν, Summable (fun s => (E s).indicator (fun _ => m s) t) := by
  have hfinite := lintegral_weightedBandIncidence_lt_top ν E m a hE hm ha hband hm2 ha2
  filter_upwards [ae_lt_top (measurable_weightedBandIncidence E m hE) hfinite.ne] with t ht
  change (∑' s, (E s).indicator (fun _ => ENNReal.ofReal (m s)) t) < ∞ at ht
  apply (ENNReal.summable_toReal ht.ne).congr
  intro s
  by_cases hts : t ∈ E s
  · simp only [indicator_of_mem hts, ENNReal.toReal_ofReal (hm s)]
  · simp only [indicator_of_notMem hts, ENNReal.toReal_zero]

/-- The same bound as an ordinary real integral; the integrand is finite
almost everywhere by its finite Tonelli integral. -/
theorem integral_weightedBandIncidence_toReal_le
    {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m a : ι → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, ν (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    Integrable (fun t => (weightedBandIncidence E m t).toReal) ν ∧
      (∫ t, (weightedBandIncidence E m t).toReal ∂ν) ≤ ∑' s, m s * a s := by
  have hmeas := measurable_weightedBandIncidence E m hE
  have hfinite := lintegral_weightedBandIncidence_lt_top ν E m a hE hm ha hband hm2 ha2
  refine ⟨integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfinite.ne, ?_⟩
  rw [integral_toReal hmeas.aemeasurable (ae_lt_top hmeas hfinite.ne)]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_weightedBandIncidence_le ν E m a hE hm ha hband hm2 ha2)
  simpa only [ENNReal.toReal_ofReal (tsum_nonneg (fun s => mul_nonneg (hm s) (ha s)))]
    using hb

/-- The paper's ordinary real weighted series is integrable and obeys
the same dust contribution bound. -/
theorem integral_weighted_band_series_le
    {T ι : Type*} [MeasurableSpace T] [Countable ι]
    (ν : Measure T) (E : ι → Set T) (m a : ι → ℝ)
    (hE : ∀ s, MeasurableSet (E s)) (hm : ∀ s, 0 ≤ m s) (ha : ∀ s, 0 ≤ a s)
    (hband : ∀ s, ν (E s) ≤ ENNReal.ofReal (a s))
    (hm2 : Summable (fun s => m s ^ 2)) (ha2 : Summable (fun s => a s ^ 2)) :
    Integrable (fun t => ∑' s, (E s).indicator (fun _ => m s) t) ν ∧
      (∫ t, ∑' s, (E s).indicator (fun _ => m s) t ∂ν) ≤ ∑' s, m s * a s := by
  simpa only [weightedBandIncidence_toReal_eq E m hm] using
    integral_weightedBandIncidence_toReal_le ν E m a hE hm ha hband hm2 ha2

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SourceArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The source-area inequality for circle domains

The source region and the interiors of its complementary disks are
disjoint subsets of one outer disk. Countable additivity gives the
source-area inequality used in Section 6 of the rigidity manuscript.
No regularity of the remaining point components is needed.
-/

open MeasureTheory Metric Set Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- Countable additivity for a disjoint measurable family, together with
one further disjoint source set, gives an area bound in a containing set. -/
theorem measure_source_add_disks_le {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) {U O : Set X} (D : ι → Set X)
    (hD : ∀ j, MeasurableSet (D j))
    (hpair : Pairwise (Disjoint on D))
    (hdisj : ∀ j, Disjoint U (D j))
    (hUO : U ⊆ O) (hDO : ∀ j, D j ⊆ O) :
    μ U + ∑' j, μ (D j) ≤ μ O := by
  have hd : Disjoint U (⋃ j, D j) := disjoint_iUnion_right.mpr hdisj
  calc
    μ U + ∑' j, μ (D j) = μ (U ∪ ⋃ j, D j) := by
      rw [measure_union hd (MeasurableSet.iUnion hD), measure_iUnion hpair hD]
    _ ≤ μ O := measure_mono (union_subset hUO (iUnion_subset hDO))

/-- The actual geometric source-area bound for pairwise disjoint disks. -/
theorem sourceArea_le {ι : Type*} [Countable ι] {U : Set ℂ}
    (centers : ι → ℂ) (radii : ι → ℝ) (R : ℝ)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (radii j)))
    (hdisj : ∀ j, Disjoint U (ball (centers j) (radii j)))
    (hUO : U ⊆ ball 0 R)
    (hDO : ∀ j, ball (centers j) (radii j) ⊆ ball 0 R) :
    volume U + ∑' j, volume (ball (centers j) (radii j)) ≤ volume (ball (0 : ℂ) R) :=
  measure_source_add_disks_le volume (fun j => ball (centers j) (radii j))
    (fun _ => measurableSet_ball) hpair hdisj hUO hDO

/-- Finitely bounded, pairwise disjoint disks have square-summable radii. -/
theorem summable_radii_sq {ι : Type*} [Countable ι]
    (centers : ι → ℂ) (radii : ι → ℝ) (R : ℝ)
    (hr : ∀ j, 0 ≤ radii j)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (radii j)))
    (hDO : ∀ j, ball (centers j) (radii j) ⊆ ball 0 R) :
    Summable (fun j => radii j ^ 2) := by
  have hbound := sourceArea_le (U := ∅) centers radii R hpair
    (fun _ => by simp) (empty_subset _) hDO
  simp only [measure_empty, zero_add] at hbound
  have hfinite : (∑' j, volume (ball (centers j) (radii j))) ≠ ∞ :=
    ne_of_lt (hbound.trans_lt (measure_ball_lt_top))
  have hs := ENNReal.summable_toReal hfinite
  have hs' : Summable (fun j => Real.pi * radii j ^ 2) :=
    hs.congr (fun j => real_volume_ball (centers j) (hr j))
  exact (summable_mul_left_iff Real.pi_ne_zero).mp hs'

/-- The real source-area inequality, with the familiar factor `π`. -/
theorem sourceArea_real_le {ι : Type*} [Countable ι] {U : Set ℂ}
    (centers : ι → ℂ) (radii : ι → ℝ) (R : ℝ)
    (hr : ∀ j, 0 ≤ radii j) (hR : 0 ≤ R)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (radii j)))
    (hdisj : ∀ j, Disjoint U (ball (centers j) (radii j)))
    (hUO : U ⊆ ball 0 R)
    (hDO : ∀ j, ball (centers j) (radii j) ⊆ ball 0 R) :
    (volume U).toReal + Real.pi * (∑' j, radii j ^ 2) ≤ Real.pi * R ^ 2 := by
  have hbound := sourceArea_le centers radii R hpair hdisj hUO hDO
  have hsumBound : (∑' j, volume (ball (centers j) (radii j))) ≤
      volume (ball (0 : ℂ) R) :=
    le_trans (le_add_left le_rfl) hbound
  have hfinite : (∑' j, volume (ball (centers j) (radii j))) ≠ ∞ :=
    ne_of_lt (hsumBound.trans_lt measure_ball_lt_top)
  have hUfinite : volume U ≠ ∞ :=
    ne_of_lt ((measure_mono hUO).trans_lt measure_ball_lt_top)
  have hreal := ENNReal.toReal_mono (ne_of_lt measure_ball_lt_top) hbound
  rw [ENNReal.toReal_add hUfinite hfinite,
    ENNReal.tsum_toReal_eq (fun _ => ne_of_lt measure_ball_lt_top),
    real_volume_ball 0 hR] at hreal
  have heq : (∑' j, (volume (ball (centers j) (radii j))).toReal) =
      Real.pi * (∑' j, radii j ^ 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    exact real_volume_ball (centers j) (hr j)
  rw [heq] at hreal
  exact hreal

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalExteriorGerm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A holomorphic exterior map tending to the identity has an actual
principal Laurent germ. The first two divided differences give the
coefficient and the analytic remainder; no Laurent estimate is assumed. -/
open Set Filter Function Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem invertedPrincipalRemainder_analytic {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0)) :
    AnalyticAt ℂ (invertedPrincipalRemainder F) 0 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hd := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).eventually hF
    filter_upwards [hd, self_mem_nhdsWithin] with w hw hw0
    have hn : w ≠ 0 := hw0
    have hi : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) w := differentiableAt_inv hn
    have hh := (hw.comp w hi).sub hi
    apply hh.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hn] with z hz
    exact Function.update_of_ne hz _ _
  · exact continuousAt_update_same.mpr
      (ht.comp (tendsto_inv₀_nhdsNE_zero (α := ℂ)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteLineGaps
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual gaps of finitely many disjoint line intervals

Sorting the closed holes supplies the open intervals on which variation
is paid. Every gap is nonempty, the gaps are disjoint, and no point of a
gap belongs to a hole. Point holes are allowed.
-/

open Set Function

namespace CircleDomainRigidity

theorem gapsAfterHoles_disjoint {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2)
    (hfirst : Monotone (fun i => (H i).1)) :
    Pairwise (Disjoint on fun i => Ioo
      (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm
  obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last
    (show i ≠ Fin.last n by
      intro he
      subst i
      exact (not_lt_of_ge (Fin.le_last j)) hlt)
  obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero
    (show j ≠ 0 by intro he; simp [he] at hlt)
  have hkl : k ≤ l := by
    exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hlt)
  apply disjoint_left.mpr
  intro x hx hy
  dsimp only at hx hy
  rw [gapsAfterHoles_castSucc_snd] at hx
  rw [gapsAfterHoles_succ_fst] at hy
  exact (not_lt_of_ge (((hfirst hkl).trans (hvalid l)).trans hy.1.le)) hx.2

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_TargetArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Target area from the exterior area theorem

Ahlfors, *Conformal Invariants* (1973), Exterior Area Theorem, supplies the
area bound for the set omitted by a normalized univalent exterior map.
The numerical bound yields the target-area estimate by change of variables
and disjointness of the image and omitted disks.
-/

open MeasureTheory Metric Set Function Bornology
open scoped ENNReal

namespace CircleDomainRigidity

/-- Complex change of variables identifies image area with Dirichlet area
of an injective holomorphic map. -/
theorem integral_norm_deriv_sq_eq_image_area {f : ℂ → ℂ} {U : Set ℂ}
    (hU : MeasurableSet U) (hf : ∀ z ∈ U, DifferentiableAt ℂ f z)
    (hinj : InjOn f U) :
    (∫ z in U, ‖deriv f z‖ ^ 2) = (volume (f '' U)).toReal := by
  let L : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ
  have hL : ∀ z ∈ U, HasFDerivWithinAt f (L z) U z :=
    fun z hz => ((hf z hz).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet (z : ℂ) : (L z).det = ‖deriv f z‖ ^ 2 := by
    simp [L, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hU hL hinj
    (fun _ : ℂ => (1 : ℝ))
  simpa [hdet, measureReal_def] using h.symm

/-- The genuine exterior-area input yields target-radius summability,
squared-derivative integrability, and the complete target-area estimate.
The only geometric hypotheses on the target disks are disjoint interiors
and disjointness from the image of the source domain. -/
theorem targetArea_of_exterior_area_bound {ι : Type*} [Countable ι]
    {f : ℂ → ℂ} {D : Set ℂ} (centers : ι → ℂ) (s : ι → ℝ) (R : ℝ)
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) (hinj : InjOn f D)
    (hExterior : (closedBall (0 : ℂ) R)ᶜ ⊆ D)
    (hs : ∀ j, 0 ≤ s j)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (s j)))
    (hdisj : ∀ j, Disjoint (f '' D) (ball (centers j) (s j)))
    (harea : ExteriorOmittedAreaBound f R) :
    Summable (fun j => s j ^ 2) ∧
    Integrable (fun z => ‖deriv f z‖ ^ 2) (volume.restrict (D ∩ ball 0 R)) ∧
    (∫ z in D ∩ ball 0 R, ‖deriv f z‖ ^ 2) +
      Real.pi * (∑' j, s j ^ 2) ≤ Real.pi * R ^ 2 := by
  let U := D ∩ ball (0 : ℂ) R
  let O := (f '' (closedBall (0 : ℂ) R)ᶜ)ᶜ
  have hU : IsOpen U := hD.inter isOpen_ball
  have hUinD : U ⊆ D := inter_subset_left
  have hUO : f '' U ⊆ O := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    have hwz : w = z := hinj (hExterior hw) hz.1 heq
    exact hw (hwz ▸ ball_subset_closedBall hz.2)
  have hdiskO : ∀ j, ball (centers j) (s j) ⊆ O := by
    intro j z hz ⟨w, hw, heq⟩
    exact Set.disjoint_left.mp (hdisj j) ⟨w, hExterior hw, heq⟩ hz
  have hdisjU : ∀ j, Disjoint (f '' U) (ball (centers j) (s j)) :=
    fun j => (hdisj j).mono_left (image_mono hUinD)
  have hbound : volume (f '' U) + ∑' j, volume (ball (centers j) (s j)) ≤
      ENNReal.ofReal (Real.pi * R ^ 2) :=
    (measure_source_add_disks_le volume (fun j => ball (centers j) (s j))
      (fun _ => measurableSet_ball) hpair hdisjU hUO hdiskO).trans harea
  have htotalFinite : volume (f '' U) + ∑' j, volume (ball (centers j) (s j)) < ∞ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  have himageFinite : volume (f '' U) ≠ ∞ :=
    ne_of_lt ((le_add_right le_rfl).trans_lt htotalFinite)
  have hsumFinite : (∑' j, volume (ball (centers j) (s j))) ≠ ∞ :=
    ne_of_lt ((le_add_left le_rfl).trans_lt htotalFinite)
  have hsSum : Summable (fun j => s j ^ 2) := by
    have hsum := (ENNReal.summable_toReal hsumFinite).congr
      (fun j => real_volume_ball (centers j) (hs j))
    exact (summable_mul_left_iff Real.pi_ne_zero).mp hsum
  have hdiff : ∀ z ∈ U, DifferentiableAt ℂ f z :=
    fun z hz => (hf z hz.1).differentiableAt (hD.mem_nhds hz.1)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_add himageFinite hsumFinite,
    ENNReal.tsum_toReal_eq (fun _ => ne_of_lt measure_ball_lt_top),
    ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le (sq_nonneg R))] at hreal
  have hsumEq : (∑' j, (volume (ball (centers j) (s j))).toReal) =
      Real.pi * (∑' j, s j ^ 2) := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun j => real_volume_ball (centers j) (hs j))
  rw [hsumEq, ← integral_norm_deriv_sq_eq_image_area hU.measurableSet hdiff
    (hinj.mono hUinD)] at hreal
  exact ⟨hsSum, integrable_norm_deriv_sq_of_image_area_finite hU.measurableSet hdiff
    (hinj.mono hUinD) himageFinite, hreal⟩

/-- On a bounded measurable portion of a holomorphic domain, square
integrability of the derivative implies integrability of its modulus. -/
theorem integrable_norm_deriv_of_sq {f : ℂ → ℂ} {D U : Set ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hU : MeasurableSet U) (hbU : IsBounded U) (hUD : U ⊆ D)
    (hsq : Integrable (fun z => ‖deriv f z‖ ^ 2) (volume.restrict U)) :
    Integrable (fun z => ‖deriv f z‖) (volume.restrict U) := by
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hbU.measure_lt_top.ne
  have hm : AEStronglyMeasurable (fun z => ‖deriv f z‖) (volume.restrict U) :=
    ((hf.deriv hD).continuousOn.norm.mono hUD).aestronglyMeasurable hU
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((memLp_two_iff_integrable_sq hm).mpr hsq)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalLineFubini
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini on the two physical coordinate line families. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem physicalCoordinatePlane_measurePreserving (i : Fin 2) :
    MeasurePreserving (fun p : ℝ × ℝ => physicalCoordinateLine i p.1 p.2)
      (volume.prod volume) volume := by
  have he : MeasurePreserving euclideanPlaneCoordinates.symm (volume.prod volume) volume := by
    simpa only [← Measure.volume_eq_prod] using euclideanPlaneCoordinates_symm_measurePreserving
  fin_cases i
  · simpa [physicalCoordinateLine,Function.comp_def,Prod.swap] using
      he.comp (Measure.measurePreserving_swap (μ := volume) (ν := volume))
  · simpa [physicalCoordinateLine] using he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RealCoordinateLines
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product and complex coordinates of the physical line families. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem realCoordinateLine_contDiff (i : Fin 2) (y : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (realCoordinateLine i y) := by
  unfold realCoordinateLine
  split <;> fun_prop

 theorem realCoordinateLine_physical (i : Fin 2) (y x : ℝ) :
    euclideanPlaneCoordinates (physicalCoordinateLine i y x) = realCoordinateLine i y x := by
  unfold physicalCoordinateLine realCoordinateLine
  split <;> exact euclideanPlaneCoordinates.apply_symm_apply _

 theorem realCoordinatePlane_measurePreserving (i : Fin 2) :
    MeasurePreserving (fun p : ℝ × ℝ => realCoordinateLine i p.1 p.2)
      (volume.prod volume) volume := by
  have h := euclideanPlaneCoordinates_measurePreserving.comp
    (physicalCoordinatePlane_measurePreserving i)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact (realCoordinateLine_physical i p.1 p.2).symm

 theorem complexCoordinateLine_transverse_le (i : Fin 2) (y x : ℝ) (c : ℂ) :
    |y-transverseCoordinate i c| ≤ ‖complexCoordinateLine i y x-c‖ := by
  fin_cases i
  · simpa [complexCoordinateLine,realCoordinateLine,transverseCoordinate] using
      Complex.abs_im_le_norm (complexCoordinateLine 0 y x-c)
  · simpa [complexCoordinateLine,realCoordinateLine,transverseCoordinate] using
      Complex.abs_re_le_norm (complexCoordinateLine 1 y x-c)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CountableAxialDiskTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable axial disk tolls are integrable with their exact mixed-radius
budget. Point disks are missed outside a countable set of lines. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complexCoordinateLine_meets_closedBall (i : Fin 2) (y : ℝ) (c : ℂ) (r : ℝ) :
    (∃ x, complexCoordinateLine i y x ∈ closedBall c r) ↔
      y ∈ Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r) := by
  constructor
  · rintro ⟨x,hx⟩
    have h := (complexCoordinateLine_transverse_le i y x c).trans (by simpa only [mem_closedBall,dist_eq_norm] using hx)
    exact ⟨by linarith [(abs_le.mp h).1],by linarith [(abs_le.mp h).2]⟩
  · intro hy
    fin_cases i
    · simpa [complexCoordinateLine,realCoordinateLine,transverseCoordinate,Complex.equivRealProdCLM_symm_apply,Complex.mk_eq_add_mul_I] using
        (horizontal_line_meets_closedBall c).mpr hy
    · refine ⟨c.im,?_⟩
      have he : dist (complexCoordinateLine 1 y c.im) c = |y-c.re| := by
        rw [dist_eq_norm,← Complex.abs_re_eq_norm.mpr (by simp [complexCoordinateLine,realCoordinateLine])]
        simp [complexCoordinateLine,realCoordinateLine]
      change dist (complexCoordinateLine 1 y c.im) c ≤ r
      rw [he]
      have hyl : c.re-r ≤ y := hy.1
      have hyu : y ≤ c.re+r := hy.2
      exact abs_le.mpr ⟨by linarith,by linarith⟩

 theorem axialDiskToll_integrable {ι : Type*} [Countable ι]
    (i : Fin 2) (c : ι → ℂ) (r s : ι → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : ∀ j, 0 ≤ s j)
    (hr2 : Summable (fun j => r j^2)) (hs2 : Summable (fun j => s j^2)) :
    Integrable (axialDiskToll i c r s) volume ∧
      (∫ y, axialDiskToll i c r s y) ≤ 4*∑' j, r j*s j := by
  have hb (j : ι) : volume (Icc (transverseCoordinate i (c j)-r j)
      (transverseCoordinate i (c j)+r j)) ≤ ENNReal.ofReal (2*r j) := by
    rw [Real.volume_Icc]
    apply le_of_eq
    congr 1
    ring
  have hr' : Summable (fun j => (2*r j)^2) := by simpa only [mul_pow,show (2 : ℝ)^2 = 4 by norm_num] using hr2.mul_left 4
  have hs' : Summable (fun j => (2*s j)^2) := by simpa only [mul_pow,show (2 : ℝ)^2 = 4 by norm_num] using hs2.mul_left 4
  have h := integral_weighted_band_series_le volume
    (fun j => Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j))
    (fun j => 2*s j) (fun j => 2*r j) (fun _ => measurableSet_Icc)
    (fun j => mul_nonneg (by norm_num) (hs j)) (fun j => mul_nonneg (by norm_num) (hr j)) hb hs' hr'
  refine ⟨h.1,?_⟩
  apply h.2.trans_eq
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TypicalAxialDiskTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same full-measure set of lines pays every finite segment and
every finite deletion of the matched disk family. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem axial_disk_tolls_summable_ae {ι : Type*} [Countable ι]
    (i : Fin 2) (c : ι → ℂ) (r s : ι → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : ∀ j, 0 ≤ s j)
    (hr2 : Summable (fun j => r j^2)) (hs2 : Summable (fun j => s j^2)) :
    ∀ᵐ y ∂volume, Summable (fun j =>
      (Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j)).indicator
        (fun _ => 2*s j) y) := by
  apply ae_summable_weighted_band_series volume _ (fun j => 2*s j) (fun j => 2*r j)
    (fun _ => measurableSet_Icc) (fun j => mul_nonneg (by norm_num) (hs j))
    (fun j => mul_nonneg (by norm_num) (hr j))
  · intro j
    rw [Real.volume_Icc]
    apply le_of_eq
    congr 1
    ring
  · simpa only [mul_pow,show (2 : ℝ)^2 = 4 by norm_num] using hs2.mul_left 4
  · simpa only [mul_pow,show (2 : ℝ)^2 = 4 by norm_num] using hr2.mul_left 4

 theorem segment_disk_tolls_summable {ι : Type*} [Countable ι]
    (i : Fin 2) (c : ι → ℂ) (r s : ι → ℝ) (hs : ∀ j, 0 ≤ s j)
    {y : ℝ} (hy : Summable (fun j =>
      (Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j)).indicator
        (fun _ => 2*s j) y)) (a b : ℝ) :
    Summable (fun j => if ∃ x ∈ Icc a b, complexCoordinateLine i y x ∈ closedBall (c j) (r j)
      then 2*s j else 0) := by
  classical
  apply hy.of_nonneg_of_le
  · intro j
    split_ifs
    · exact mul_nonneg (by norm_num) (hs j)
    · exact le_rfl
  · intro j
    split_ifs with hj
    · have hband := (complexCoordinateLine_meets_closedBall i y (c j) (r j)).mp
        ⟨hj.choose,hj.choose_spec.2⟩
      rw [indicator_of_mem hband]
    · exact indicator_nonneg (fun _ _ => mul_nonneg (by norm_num) (hs j)) _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialChordGeometry
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both source-axis geometries use the same exact real chord intervals.
Swapping real coordinates preserves every source disk and its distances. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem axialSwap_dist (i : Fin 2) (z w : ℂ) : dist (axialSwap i z) (axialSwap i w) = dist z w := by
  unfold axialSwap
  split
  · rfl
  · simp only [dist_eq_norm,← mul_sub,norm_mul,Complex.norm_I,one_mul]
    rw [← star_sub,norm_star]

 theorem axialSwap_line (i : Fin 2) (y x : ℝ) :
    axialSwap i (complexCoordinateLine i y x) = (⟨x,y⟩ : ℂ) := by
  fin_cases i <;> apply Complex.ext <;>
    simp [axialSwap,complexCoordinateLine,realCoordinateLine]

 theorem axialSwap_im (i : Fin 2) (c : ℂ) : (axialSwap i c).im = transverseCoordinate i c := by
  fin_cases i <;> simp [axialSwap,transverseCoordinate]

 theorem mem_closedBall_iff_mem_axialChord (i : Fin 2) (c : ℂ) {r y x : ℝ}
    (hr : 0 ≤ r) (hy : y ∈ Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r)) :
    complexCoordinateLine i y x ∈ closedBall c r ↔
      x ∈ Icc (axialChord i c r y).1 (axialChord i c r y).2 := by
  have hd := axialSwap_dist i (complexCoordinateLine i y x) c
  rw [axialSwap_line] at hd
  change dist (complexCoordinateLine i y x) c ≤ r ↔ _
  rw [← hd]
  exact mem_closedBall_iff_mem_horizontalChord _ hr (by simpa only [axialSwap_im] using hy)

 theorem axial_ball_preimage_ordConnected (i : Fin 2) (y : ℝ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    OrdConnected {x | complexCoordinateLine i y x ∈ closedBall c r} := by
  by_cases he : ∃ x, complexCoordinateLine i y x ∈ closedBall c r
  · have hy := (complexCoordinateLine_meets_closedBall i y c r).mp he
    have hset : {x | complexCoordinateLine i y x ∈ closedBall c r} =
        Icc (axialChord i c r y).1 (axialChord i c r y).2 := by
      ext x
      exact mem_closedBall_iff_mem_axialChord i c hr hy
    rw [hset]
    exact ordConnected_Icc
  · have hset : {x | complexCoordinateLine i y x ∈ closedBall c r} = ∅ := by
      ext x
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      exact fun hx => he ⟨x,hx⟩
    rw [hset]
    exact ordConnected_empty

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialSwapDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate swap preserves the actual closed disk family. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem axialSwap_involutive (i : Fin 2) : Involutive (axialSwap i) := by
  intro z
  fin_cases i <;> apply Complex.ext <;> simp [axialSwap]

 theorem axialSwap_mem_closedBall_iff (i : Fin 2) (z c : ℂ) (r : ℝ) :
    axialSwap i z ∈ closedBall (axialSwap i c) r ↔ z ∈ closedBall c r := by
  simp only [mem_closedBall,axialSwap_dist]

 theorem axialSwap_pairwise_disjoint {κ : Type*} (i : Fin 2) (c : κ → ℂ) (r : κ → ℝ)
    (hd : Pairwise (Disjoint on fun j => closedBall (c j) (r j))) :
    Pairwise (Disjoint on fun j => closedBall (axialSwap i (c j)) (r j)) := by
  intro j k hjk
  apply disjoint_left.mpr
  intro z hz hz'
  have hj : axialSwap i z ∈ closedBall (c j) (r j) := by
    simpa only [axialSwap_involutive i (c j)] using
      (axialSwap_mem_closedBall_iff i z (axialSwap i (c j)) (r j)).mpr hz
  have hk : axialSwap i z ∈ closedBall (c k) (r k) := by
    simpa only [axialSwap_involutive i (c k)] using
      (axialSwap_mem_closedBall_iff i z (axialSwap i (c k)) (r k)).mpr hz'
  exact disjoint_left.mp (hd hjk) hj hk

 theorem horizontal_mem_swapped_disk (i : Fin 2) (x y : ℝ) (c : ℂ) (r : ℝ) :
    (⟨x,y⟩ : ℂ) ∈ closedBall (axialSwap i c) r ↔
      complexCoordinateLine i y x ∈ closedBall c r := by
  rw [← axialSwap_line i y x]
  exact axialSwap_mem_closedBall_iff i _ _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_GapFluxTelescoping
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite gap increments equal outer flux minus the increments across
removed intervals, without any continuity assumption on boundary values. -/
open Set
open scoped BigOperators
namespace CircleDomainRigidity

 theorem sum_gap_increments {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ) (v : ℝ → ℝ) :
    (∑ i, (v (gapsAfterHoles a b H i).2-v (gapsAfterHoles a b H i).1)) =
      v b-v a-∑ i, (v (H i).2-v (H i).1) := by
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  have hleft : (∑ i, v (gapsAfterHoles a b H i).1) = v a+∑ i, v (H i).2 := by
    rw [Fin.sum_univ_succ]
    simp only [gapsAfterHoles_zero_fst,gapsAfterHoles_succ_fst]
  have hright : (∑ i, v (gapsAfterHoles a b H i).2) = (∑ i, v (H i).1)+v b := by
    rw [Fin.sum_univ_castSucc]
    simp only [gapsAfterHoles_last_snd,gapsAfterHoles_castSucc_snd]
  rw [hleft,hright]
  ring

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteGapMultiplicity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An interval meeting at most one deleted hole can meet at most two
retained gaps. This is the exact multiplicity in the tail-disk estimate. -/
open Set Function
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem interval_meets_hole_between_gaps {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2) (hfirst : Monotone (fun i => (H i).1))
    {J : Set ℝ} (hJ : OrdConnected J) (i : Fin n) (v : Fin (n+1)) (hiv : i.castSucc < v)
    (hi : (J ∩ Icc (gapsAfterHoles a b H i.castSucc).1
      (gapsAfterHoles a b H i.castSucc).2).Nonempty)
    (hv : (J ∩ Icc (gapsAfterHoles a b H v).1 (gapsAfterHoles a b H v).2).Nonempty) :
    (J ∩ Icc (H i).1 (H i).2).Nonempty := by
  obtain ⟨x,hx,hxi⟩ := hi
  obtain ⟨z,hz,hzv⟩ := hv
  obtain ⟨v',rfl⟩ := Fin.eq_succ_of_ne_zero (show v ≠ 0 by
    intro he; subst v; exact (not_lt_of_ge (Fin.zero_le _)) hiv)
  have hiv' : i ≤ v' := by
    simp only [Fin.lt_def,Fin.val_castSucc,Fin.val_succ] at hiv
    exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hiv)
  have hxl : x ≤ (H i).1 := by simpa only [gapsAfterHoles_castSucc_snd] using hxi.2
  have hlz : (H i).1 ≤ z := (hfirst hiv').trans ((hvalid v').trans (by
    simpa only [gapsAfterHoles_succ_fst] using hzv.1))
  exact ⟨(H i).1,hJ.out hx hz ⟨hxl,hlz⟩,le_rfl,hvalid i⟩

 theorem at_most_two_gaps_of_at_most_one_hole {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2) (hfirst : Monotone (fun i => (H i).1))
    {J : Set ℝ} (hJ : OrdConnected J)
    (hone : ∀ i j, (J ∩ Icc (H i).1 (H i).2).Nonempty →
      (J ∩ Icc (H j).1 (H j).2).Nonempty → i = j) :
    (Finset.univ.filter (fun i => (J ∩ Icc (gapsAfterHoles a b H i).1
      (gapsAfterHoles a b H i).2).Nonempty)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun i => (J ∩ Icc (gapsAfterHoles a b H i).1
      (gapsAfterHoles a b H i).2).Nonempty)
  change S.card ≤ 2
  by_contra h
  have hcard : 2 < S.card := lt_of_not_ge h
  let e := S.orderEmbOfFin rfl
  let x : Fin S.card := ⟨0,by omega⟩
  let y : Fin S.card := ⟨1,by omega⟩
  let z : Fin S.card := ⟨2,by omega⟩
  have hxy : e x < e y := e.strictMono (by change 0 < 1; omega)
  have hyz : e y < e z := e.strictMono (by change 1 < 2; omega)
  have hmem (v : Fin S.card) : (J ∩ Icc (gapsAfterHoles a b H (e v)).1
      (gapsAfterHoles a b H (e v)).2).Nonempty :=
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem rfl v)).2
  obtain ⟨i,hi⟩ := Fin.eq_castSucc_of_ne_last (show e x ≠ Fin.last n by
    intro he; rw [he] at hxy; exact (not_lt_of_ge (Fin.le_last _)) hxy)
  obtain ⟨j,hj⟩ := Fin.eq_castSucc_of_ne_last (show e y ≠ Fin.last n by
    intro he; rw [he] at hyz; exact (not_lt_of_ge (Fin.le_last _)) hyz)
  have hholei := interval_meets_hole_between_gaps a b H hvalid hfirst hJ i (e z)
    (by rw [hi]; exact hxy.trans hyz) (by rw [hi]; exact hmem x) (hmem z)
  have hholej := interval_meets_hole_between_gaps a b H hvalid hfirst hJ j (e z)
    (by rw [hj]; exact hyz) (by rw [hj]; exact hmem y) (hmem z)
  have heij := hone i j hholei hholej
  have he : e x = e y := by rw [← hi,← hj,heij]
  exact (ne_of_lt hxy) he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteGapTollSum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting each remaining disk at most twice gives the exact factor
two for the sum of all retained-gap tolls on one line. -/
open Set Function Filter MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem finite_gap_toll_sum_le {ι κ : Type*} [Fintype ι] [Countable κ]
    (A : ι → Set ℝ) (J : κ → Set ℝ) (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => if (J j).Nonempty then w j else 0))
    (hmult : ∀ j, (Finset.univ.filter (fun i => (J j ∩ A i).Nonempty)).card ≤ 2) :
    (∑ i, ∑' j, if (J j ∩ A i).Nonempty then w j else 0) ≤
      2*∑' j, if (J j).Nonempty then w j else 0 := by
  classical
  let t := fun i j => if (J j ∩ A i).Nonempty then w j else 0
  let b := fun j => if (J j).Nonempty then w j else 0
  have ht (i : ι) : Summable (t i) := by
    apply hs.of_nonneg_of_le
    · intro j
      dsimp only [t]
      split_ifs <;> [exact hw j; exact le_rfl]
    · intro j
      dsimp only [t,b]
      split_ifs with h h'
      · exact le_rfl
      · exact (h' (h.mono inter_subset_left)).elim
      · exact hw j
      · exact le_rfl
  have hcol (j : κ) : (∑ i, t i j) ≤ 2*b j := by
    by_cases hj : (J j).Nonempty
    · have he : (∑ i, t i j) =
          ((Finset.univ.filter (fun i => (J j ∩ A i).Nonempty)).card : ℝ)*w j := by
        simp only [t,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      rw [he]
      dsimp only [b]
      rw [ite_eq_left hj]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmult j) (hw j)
    · have he (i : ι) : t i j = 0 := by
        apply ite_eq_right
        exact fun h => hj (h.mono inter_subset_left)
      simp only [he,Finset.sum_const_zero,b,ite_eq_right hj,mul_zero,le_refl]
  calc
    _ = ∑' j, ∑ i, t i j := (Summable.tsum_finsetSum (fun i _ => ht i)).symm
    _ ≤ ∑' j, 2*b j := Summable.tsum_le_tsum hcol
      (summable_sum (fun i _ => ht i)) (hs.mul_left 2)
    _ = _ := tsum_mul_left

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ClosedGapIntegrals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual closed gaps have disjoint interiors; positive hole widths
make the closed gaps disjoint too. Their density integrals use at most
the density integral on the whole source segment. -/
open Set Function Filter MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem closed_gap_integrals_le {ι : Type*} [Fintype ι]
    (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i))
    (hdis : Pairwise (Disjoint on A)) {B : Set ℝ} (hB : MeasurableSet B) (hsub : ∀ i, A i ⊆ B)
    {ρ : ℝ → ℝ} (hi : IntegrableOn ρ B volume) (hρ : ∀ x ∈ B, 0 ≤ ρ x) :
    (∑ i, ∫ x in A i, ρ x) ≤ ∫ x in B, ρ x := by
  rw [← integral_iUnion_fintype hA hdis (fun i => hi.mono_set (hsub i))]
  apply setIntegral_mono_set hi
  · exact (ae_restrict_mem hB).mono (fun x hx => hρ x hx)
  · exact (iUnion_subset hsub).eventuallyLE

/-- Singleton endpoints have zero length, so even zero-width holes permit
summing the closed-gap integrals without double payment. -/
 theorem closed_gap_integrals_le_of_nonstrict {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2) (hfirst : Monotone (fun i => (H i).1))
    {B V : Set ℝ} (hB : MeasurableSet B) (hV : MeasurableSet V)
    {ρ : ℝ → ℝ} (hi : IntegrableOn ρ B volume) (hρ : ∀ x ∈ B, 0 ≤ ρ x)
    (hsub : ∀ i, Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V ⊆ B) :
    (∑ i, ∫ x in Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V, ρ x) ≤
      ∫ x in B, ρ x := by
  have he (i : Fin (n+1)) :
      (∫ x in Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V, ρ x) =
      ∫ x in Ioo (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V, ρ x := by
    apply setIntegral_congr_set
    filter_upwards [Ioo_ae_eq_Icc (μ := volume)
      (a := (gapsAfterHoles a b H i).1) (b := (gapsAfterHoles a b H i).2)] with x hx
    show (x ∈ Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V) = (x ∈ Ioo (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V)
    simp only [mem_inter_iff]
    exact propext (and_congr_left (fun _ => (iff_of_eq hx).symm))
  simp_rw [he]
  apply closed_gap_integrals_le _ (fun _ => measurableSet_Ioo.inter hV)
    (fun i j hij => (gapsAfterHoles_disjoint a b H hvalid hfirst hij).mono
      inter_subset_left inter_subset_left) hB _ hi hρ
  intro i x hx
  exact hsub i ⟨Ioo_subset_Icc_self hx.1,hx.2⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteHoleSliceAssembly
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual retained-gap estimates gives the outer increment
minus the removed-hole increments, with each tail disk paid twice. -/
open Set Function Filter MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem finite_hole_slice_payment {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hvalid : ∀ i, (H i).1 ≤ (H i).2) (hfirst : Monotone (fun i => (H i).1))
    {κ : Type*} [Countable κ] (J : κ → Set ℝ) (w : κ → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => if (J j).Nonempty then w j else 0))
    (hJ : ∀ j, OrdConnected (J j))
    (hone : ∀ j i k, (J j ∩ Icc (H i).1 (H i).2).Nonempty →
      (J j ∩ Icc (H k).1 (H k).2).Nonempty → i = k)
    (v : ℝ → ℝ) (ρ : ℝ → ℝ) {B V : Set ℝ} (hB : MeasurableSet B) (hV : MeasurableSet V)
    (hi : IntegrableOn ρ B volume) (hρ : ∀ x ∈ B, 0 ≤ ρ x)
    (hsub : ∀ i, Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V ⊆ B)
    (hpay : ∀ i,
      v (gapsAfterHoles a b H i).2-v (gapsAfterHoles a b H i).1 ≤
        (∫ x in Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ∩ V, ρ x) +
        ∑' j, if (J j ∩ Icc (gapsAfterHoles a b H i).1
          (gapsAfterHoles a b H i).2).Nonempty then w j else 0) :
    v b-v a-∑ i, (v (H i).2-v (H i).1) ≤
      (∫ x in B, ρ x)+2*∑' j, if (J j).Nonempty then w j else 0 := by
  rw [← sum_gap_increments a b H v]
  calc
    _ ≤ ∑ i, ((∫ x in Icc (gapsAfterHoles a b H i).1
        (gapsAfterHoles a b H i).2 ∩ V, ρ x) +
        ∑' j, if (J j ∩ Icc (gapsAfterHoles a b H i).1
          (gapsAfterHoles a b H i).2).Nonempty then w j else 0) :=
      Finset.sum_le_sum (fun i _ => hpay i)
    _ = (∑ i, ∫ x in Icc (gapsAfterHoles a b H i).1
        (gapsAfterHoles a b H i).2 ∩ V, ρ x) +
        ∑ i, ∑' j, if (J j ∩ Icc (gapsAfterHoles a b H i).1
          (gapsAfterHoles a b H i).2).Nonempty then w j else 0 := Finset.sum_add_distrib
    _ ≤ _ := add_le_add
      (closed_gap_integrals_le_of_nonstrict a b H hvalid hfirst hB hV hi hρ hsub)
      (finite_gap_toll_sum_le _ J w hw hs (fun j =>
        at_most_two_gaps_of_at_most_one_hole a b H hvalid hfirst (hJ j) (hone j)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialChordInterior
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict disk membership corresponds to the open chord interval. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem mem_ball_iff_mem_horizontalChord (c : ℂ) {r y x : ℝ}
    (hr : 0 ≤ r) (hy : y ∈ Icc (c.im-r) (c.im+r)) :
    (⟨x,y⟩ : ℂ) ∈ ball c r ↔
      x ∈ Ioo (horizontalChord c r y).1 (horizontalChord c r y).2 := by
  have hsq := Real.sq_sqrt (horizontalChord_nonneg c hr hy)
  have hsqrt := Real.sqrt_nonneg (r^2-(y-c.im)^2)
  have hn := Complex.sq_norm ((⟨x,y⟩ : ℂ)-c)
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at hn
  dsimp only [horizontalChord,Prod.fst,Prod.snd]
  rw [mem_ball,dist_eq_norm]
  constructor
  · intro h
    have hbound : (x-c.re)^2 < r^2-(y-c.im)^2 := by nlinarith [norm_nonneg ((⟨x,y⟩ : ℂ)-c)]
    constructor <;> nlinarith [sq_nonneg (x-c.re-Real.sqrt (r^2-(y-c.im)^2)),
      sq_nonneg (x-c.re+Real.sqrt (r^2-(y-c.im)^2))]
  · rintro ⟨hx,hx'⟩
    have hbound : (x-c.re)^2 < r^2-(y-c.im)^2 := by
      nlinarith [mul_pos (show 0 < x-c.re+Real.sqrt (r^2-(y-c.im)^2) by linarith)
        (show 0 < Real.sqrt (r^2-(y-c.im)^2)-(x-c.re) by linarith)]
    nlinarith [norm_nonneg ((⟨x,y⟩ : ℂ)-c)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SortedCrossingChords
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sorting the actual crossed disks gives a finite ordered hole family
with an injective owner map and exact signed flux accounting. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem horizontalChord_injective_on_crossing {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i))) {y a b : ℝ}
    {i j : I} (hi : i ∈ crossingDisks c r y a b) (hj : j ∈ crossingDisks c r y a b)
    (he : horizontalChord (c i) (r i) y = horizontalChord (c j) (r j) y) : i = j := by
  by_contra hij
  have hmem : (horizontalChord (c i) (r i) y).1 ∈
      Icc (horizontalChord (c i) (r i) y).1 (horizontalChord (c i) (r i) y).2 :=
    left_mem_Icc.mpr (horizontalChord_valid _ _ _)
  have hm1 := (mem_closedBall_iff_mem_horizontalChord _ (hr i) (crossingDisk_line_hit hi)).mpr hmem
  have hm2 := (mem_closedBall_iff_mem_horizontalChord _ (hr j) (crossingDisk_line_hit hj)).mpr (he ▸ hmem)
  exact disjoint_left.mp (hd hij) hm1 (by simpa only [← he] using hm2)

 theorem exists_sorted_crossing_chords {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i))) {y a b : ℝ}
    (ha : ∀ i, (⟨a,y⟩ : ℂ) ∉ closedBall (c i) (r i))
    (hb : ∀ i, (⟨b,y⟩ : ℂ) ∉ closedBall (c i) (r i)) :
    Nonempty (SortedCrossingChords c r y a b) := by
  classical
  let K := crossingChords c r y a b
  let H := K.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl
  have hmem (i : Fin K.card) : H i ∈ K := K.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ) rfl i
  have honto (z : ℝ × ℝ) (hz : z ∈ K) : ∃ i, H i = z := by
    let z' : (K : Finset (ℝ ×ₗ ℝ)) := ⟨z,hz⟩
    exact ⟨(K.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).symm z',
      congrArg Subtype.val ((K.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).apply_symm_apply z')⟩
  have howner (i : Fin K.card) : ∃ j ∈ crossingDisks c r y a b,
      horizontalChord (c j) (r j) y = H i := Finset.mem_image.mp (hmem i)
  choose owner howner heq using howner
  have hi := crossingChords_inside c r hr ha hb
  refine ⟨⟨K.card,H,owner,howner,?_,?_,(fun i => (heq i).symm),
    (fun i => hi _ (hmem i)),?_⟩⟩
  · intro i j hij
    apply H.injective
    rw [← heq i,← heq j,hij]
  · intro j hj
    obtain ⟨i,hi⟩ := honto _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    exact ⟨i,horizontalChord_injective_on_crossing c r hr hd (howner i) hj ((heq i).trans hi)⟩
  · exact sorted_holes_separated K (fun z hz => (hi z hz).2.1) (crossingChords_disjoint c r hr hd)

 namespace SortedCrossingChords
 variable {I : Type*} [Fintype I] {c : I → ℂ} {r : I → ℝ} {y a b : ℝ}

 theorem sum_hole_increments (S : SortedCrossingChords c r y a b) (v : ℝ → ℝ) :
    (∑ i, (v (S.hole i).2-v (S.hole i).1)) =
      ∑ j ∈ crossingDisks c r y a b,
        (v (horizontalChord (c j) (r j) y).2-v (horizontalChord (c j) (r j) y).1) := by
  classical
  apply Finset.sum_bij (fun i _ => S.owner i)
  · exact fun i _ => S.owner_mem i
  · exact fun i _ j _ h => S.owner_injective h
  · intro j hj
    obtain ⟨i,hi⟩ := S.owner_surjective j hj
    exact ⟨i,Finset.mem_univ _,hi⟩
  · intro i _
    rw [S.hole_eq]

 theorem monotone_first (S : SortedCrossingChords c r y a b) : Monotone (fun i => (S.hole i).1) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (S.inside i).2.1.trans (S.separated i j h).le

 theorem monotone_last (S : SortedCrossingChords c r y a b) : Monotone (fun i => (S.hole i).2) := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (S.separated i j h).le.trans (S.inside j).2.1

 end SortedCrossingChords
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedGapAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed retained gaps avoid the interiors of the deleted intervals.
Their endpoints lie on the enlarged circles, outside the original disks. -/
open Set Function
namespace CircleDomainRigidity

 theorem closed_gaps_avoid_hole_interiors {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ)
    (hfirst : Monotone (fun i => (H i).1)) (hlast : Monotone (fun i => (H i).2))
    (i : Fin (n+1)) {x : ℝ} (hx : x ∈ Icc
      (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2) :
    ∀ j, x ∉ Ioo (H j).1 (H j).2 := by
  intro j hj
  by_cases hji : j.val < i.val
  · obtain ⟨k,rfl⟩ := Fin.eq_succ_of_ne_zero (show i ≠ 0 by
      intro he; simp [he] at hji)
    rw [gapsAfterHoles_succ_fst] at hx
    have hjk : j ≤ k := Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hji)
    exact (not_lt_of_ge ((hlast hjk).trans hx.1)) hj.2
  · obtain ⟨k,rfl⟩ := Fin.eq_castSucc_of_ne_last (show i ≠ Fin.last n by
      intro he; subst i; exact hji j.isLt)
    rw [gapsAfterHoles_castSucc_snd] at hx
    have hkj : k ≤ j := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hji)
    exact (not_lt_of_ge (hx.2.trans (hfirst hkj))) hj.1

 theorem closed_gaps_inside {n : ℕ} {a b : ℝ} (H : Fin n → ℝ × ℝ)
    (hinside : ∀ i, a ≤ (H i).1 ∧ (H i).1 ≤ (H i).2 ∧ (H i).2 ≤ b)
    (i : Fin (n+1)) : Icc (gapsAfterHoles a b H i).1 (gapsAfterHoles a b H i).2 ⊆ Icc a b := by
  have hl : a ≤ (gapsAfterHoles a b H i).1 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [gapsAfterHoles_zero_fst,le_refl]
    · rw [gapsAfterHoles_succ_fst]
      exact (hinside j).1.trans (hinside j).2.1
  have hr : (gapsAfterHoles a b H i).2 ≤ b := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [gapsAfterHoles_last_snd,le_refl]
    · rw [gapsAfterHoles_castSucc_snd]
      exact (hinside j).2.1.trans (hinside j).2.2
  exact fun _ hx => ⟨hl.trans hx.1,hx.2.trans hr⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SortedChordGapAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enlarging the removed disks makes every closed retained gap avoid
the original source disks, including at the new boundary endpoints. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity
namespace SortedCrossingChords
variable {I : Type*} [Fintype I] {c : I → ℂ} {r : I → ℝ} {y a b : ℝ}

 theorem closed_gap_avoids_original (S : SortedCrossingChords c r y a b)
    (hr : ∀ j, 0 ≤ r j) (r₀ : I → ℝ) (hlt : ∀ j, r₀ j < r j)
    (i : Fin (S.count+1)) {x : ℝ}
    (hx : x ∈ Icc (gapsAfterHoles a b S.hole i).1 (gapsAfterHoles a b S.hole i).2) :
    ∀ j, (⟨x,y⟩ : ℂ) ∉ closedBall (c j) (r₀ j) := by
  intro j hxj
  have hout : (⟨x,y⟩ : ℂ) ∈ ball (c j) (r j) := (closedBall_subset_ball (hlt j)) hxj
  have hxab : x ∈ Icc a b := closed_gaps_inside S.hole
    (fun k => ⟨(S.inside k).1.le,(S.inside k).2.1,(S.inside k).2.2.le⟩) i hx
  have hj : j ∈ crossingDisks c r y a b := mem_crossingDisks.mpr ⟨x,hxab,ball_subset_closedBall hout⟩
  obtain ⟨k,hk⟩ := S.owner_surjective j hj
  have hxi := (mem_ball_iff_mem_horizontalChord _ (hr j) (crossingDisk_line_hit hj)).mp hout
  apply closed_gaps_avoid_hole_interiors a b S.hole S.monotone_first S.monotone_last i hx k
  simpa only [S.hole_eq,hk] using hxi

end SortedCrossingChords
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteDiskSlicePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical gap estimate applied to the actual finite disk family.
The scalar premise is the interval estimate from the common-point
trace theorem. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem axial_disk_toll_eq_hit (i : Fin 2) (c : ℂ) (r s y : ℝ) :
    (Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r)).indicator
      (fun _ => 2*s) y =
      if {x | complexCoordinateLine i y x ∈ closedBall c r}.Nonempty then 2*s else 0 := by
  have he : {x | complexCoordinateLine i y x ∈ closedBall c r}.Nonempty ↔
      y ∈ Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r) :=
    complexCoordinateLine_meets_closedBall i y c r
  by_cases h : y ∈ Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r)
  · rw [indicator_of_mem h,ite_eq_left (he.mpr h)]
  · rw [indicator_of_notMem h,ite_eq_right (fun h' => h (he.mp h'))]

 theorem finite_disk_slice_payment {κ : Type*} [Countable κ]
    (i : Fin 2) (c : κ → ℂ) (r s : κ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : ∀ j, 0 ≤ s j)
    (F : Finset κ) {η : ℝ} (hη : 0 < η)
    (hd : Pairwise (Disjoint on fun j : F => closedBall (c j) (r j+η)))
    (hone : ∀ k ∉ F, ∀ j ∈ F, ∀ l ∈ F,
      (closedBall (c k) (r k) ∩ closedBall (c j) (r j+η)).Nonempty →
      (closedBall (c k) (r k) ∩ closedBall (c l) (r l+η)).Nonempty → j = l)
    {y a b : ℝ} (hab : a < b)
    (ha : ∀ j ∈ F, complexCoordinateLine i y a ∉ closedBall (c j) (r j+η))
    (hb : ∀ j ∈ F, complexCoordinateLine i y b ∉ closedBall (c j) (r j+η))
    (htoll : Summable (fun j : {j : κ // j ∉ F} =>
      (Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j)).indicator
        (fun _ => 2*s j) y))
    (v ρ : ℝ → ℝ) {V : Set ℝ} (hV : MeasurableSet V)
    (hi : IntegrableOn ρ (Icc a b ∩ V) volume) (hρ : ∀ x ∈ Icc a b ∩ V, 0 ≤ ρ x)
    (hpay : ∀ u w : ℝ, u ≤ w → Icc u w ⊆ Icc a b →
      (∀ x ∈ Icc u w, ∀ j ∈ F, complexCoordinateLine i y x ∉ closedBall (c j) (r j)) →
      |v w-v u| ≤ (∫ x in Icc u w ∩ V, ρ x) +
        ∑' j : {j : κ // j ∉ F},
          if ∃ x ∈ Icc u w, complexCoordinateLine i y x ∈ closedBall (c j) (r j)
          then 2*s j else 0) :
    v b-v a-
      (∑ j ∈ crossingDisks (fun j : F => axialSwap i (c j)) (fun j => r j+η) y a b,
        (v (axialChord i (c j) (r j+η) y).2-v (axialChord i (c j) (r j+η) y).1)) ≤
      (∫ x in Icc a b ∩ V, ρ x)+
        2*axialDiskToll i (fun j : {j : κ // j ∉ F} => c j) (fun j => r j) (fun j => s j) y := by
  let c' : F → ℂ := fun j => axialSwap i (c j)
  let r' : F → ℝ := fun j => r j+η
  have hr' (j : F) : 0 ≤ r' j := add_nonneg (hr j) hη.le
  obtain ⟨S⟩ := exists_sorted_crossing_chords c' r' hr'
    (axialSwap_pairwise_disjoint i _ _ hd)
    (fun j hj => ha j j.property ((horizontal_mem_swapped_disk i a y (c j) (r j+η)).mp hj))
    (fun j hj => hb j j.property ((horizontal_mem_swapped_disk i b y (c j) (r j+η)).mp hj))
  let J : {j : κ // j ∉ F} → Set ℝ := fun j => {x | complexCoordinateLine i y x ∈ closedBall (c j) (r j)}
  have ht : Summable (fun j => if (J j).Nonempty then 2*s j else 0) := by
    simpa only [axial_disk_toll_eq_hit] using htoll
  have hgap (k : Fin (S.count+1)) :
      Icc (gapsAfterHoles a b S.hole k).1 (gapsAfterHoles a b S.hole k).2 ⊆ Icc a b :=
    closed_gaps_inside S.hole (fun j => ⟨(S.inside j).1.le,(S.inside j).2.1,(S.inside j).2.2.le⟩) k
  have hp (k : Fin (S.count+1)) := hpay _ _
    (gapsAfterHoles_strict hab S.hole S.inside S.separated k).le (hgap k) (by
      intro x hx j hj hxj
      have havoid := S.closed_gap_avoids_original hr' (fun j : F => r j)
        (fun j => by dsimp [r'] <;> linarith) k hx ⟨j,hj⟩
      exact havoid ((horizontal_mem_swapped_disk i x y (c j) (r j)).mpr hxj))
  have hbound := finite_hole_slice_payment a b S.hole (fun j => (S.inside j).2.1)
    S.monotone_first J (fun j => 2*s j) (fun j => mul_nonneg (by norm_num) (hs j)) ht
    (fun j => axial_ball_preimage_ordConnected i y (c j) (hr j)) (by
      intro k j l hj hl
      apply S.owner_injective
      apply Subtype.ext
      apply hone k k.property (S.owner j) (S.owner j).property (S.owner l) (S.owner l).property
      · obtain ⟨x,hx,hxj⟩ := hj
        refine ⟨complexCoordinateLine i y x,hx,?_⟩
        apply (horizontal_mem_swapped_disk i x y _ _).mp
        apply (mem_closedBall_iff_mem_horizontalChord _ (hr' _) (crossingDisk_line_hit (S.owner_mem j))).mpr
        simpa only [S.hole_eq] using hxj
      · obtain ⟨x,hx,hxl⟩ := hl
        refine ⟨complexCoordinateLine i y x,hx,?_⟩
        apply (horizontal_mem_swapped_disk i x y _ _).mp
        apply (mem_closedBall_iff_mem_horizontalChord _ (hr' _) (crossingDisk_line_hit (S.owner_mem l))).mpr
        simpa only [S.hole_eq] using hxl)
    v ρ (measurableSet_Icc.inter hV) hV hi hρ
    (fun k x hx => ⟨hgap k hx.1,hx.2⟩) (by
      intro k
      exact (le_abs_self _).trans (by simpa only [J,Set.nonempty_def,mem_inter_iff,mem_ofPred_eq,and_comm] using hp k))
  rw [S.sum_hole_increments] at hbound
  simpa only [c',r',axialChord,axialDiskToll,axial_disk_toll_eq_hit] using hbound

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_IntervalCoverMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative measure step in the slice estimate. Connected fiber
coverage pays through domain images, null common traces and disk intervals. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem interval_length_le_image_and_tolls {ι : Type*} [Countable ι]
    {a b : ℝ} {E N : Set ℝ} {I : ι → Set ℝ} (hN : volume N = 0)
    (hcover : uIcc a b ⊆ E ∪ N ∪ ⋃ j, I j) :
    ENNReal.ofReal |b-a| ≤ volume E + ∑' j, volume (I j) := by
  calc
    _ = volume (uIcc a b) := by
      rw [← Icc_min_max,Real.volume_Icc,max_sub_min_eq_abs,abs_sub_comm]
    _ ≤ volume (E ∪ N ∪ ⋃ j, I j) := measure_mono hcover
    _ ≤ volume (E ∪ N) + volume (⋃ j, I j) := measure_union_le _ _
    _ ≤ (volume E + volume N) + ∑' j, volume (I j) :=
      add_le_add (measure_union_le _ _) (measure_iUnion_le _)
    _ = _ := by rw [hN,add_zero]

 theorem interval_length_le_integral_and_tolls {ι : Type*} [Countable ι]
    {a b C : ℝ} {s : ι → ℝ} {E N : Set ℝ} {I : ι → Set ℝ}
    (hC : 0 ≤ C) (hs : ∀ j, 0 ≤ s j) (hsum : Summable s)
    (hN : volume N = 0) (hE : volume E ≤ ENNReal.ofReal C)
    (hI : ∀ j, volume (I j) ≤ ENNReal.ofReal (s j))
    (hcover : uIcc a b ⊆ E ∪ N ∪ ⋃ j, I j) : |b-a| ≤ C+∑' j, s j := by
  have h := interval_length_le_image_and_tolls hN hcover
  have hb : ENNReal.ofReal |b-a| ≤ ENNReal.ofReal (C+∑' j, s j) := by
    apply h.trans
    calc
      volume E + ∑' j, volume (I j) ≤ ENNReal.ofReal C + ∑' j, ENNReal.ofReal (s j) :=
        add_le_add hE (ENNReal.tsum_le_tsum hI)
      _ = ENNReal.ofReal C + ENNReal.ofReal (∑' j, s j) := by rw [ENNReal.ofReal_tsum_of_nonneg hs hsum]
      _ = _ := (ENNReal.ofReal_add hC (tsum_nonneg hs)).symm
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hC (tsum_nonneg hs))).mp hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_OpenLineImageMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable open intervals convert local variation payment into a
measure bound for the entire image, without requiring image measurability. -/
open Set Function MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem open_line_image_measure_le (κ : Measure ℝ) [IsFiniteMeasure κ]
    {U : Set ℝ} (hU : IsOpen U) (v : ℝ → ℝ)
    (hpay : ∀ x ∈ U, ∀ y ∈ U, x ≤ y → Icc x y ⊆ U →
      |v y-v x| ≤ κ.real (Icc x y)) : volume (v '' U) ≤ κ U := by
  classical
  let C : Set (Set ℝ) := {V | ∃ x ∈ U, V = connectedComponentIn U x}
  have hC (V : Set ℝ) (hV : V ∈ C) : IsOpen V ∧ IsConnected V ∧ V ⊆ U := by
    obtain ⟨x,hx,rfl⟩ := hV
    exact ⟨hU.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr hx,
      connectedComponentIn_subset U x⟩
  have hd : C.PairwiseDisjoint id := by
    rintro V ⟨x,hx,rfl⟩ W ⟨y,hy,rfl⟩ hne
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)
  have hcount : C.Countable := hd.countable_of_nonempty_interior (fun V hV => by
    change (interior V).Nonempty
    rw [(hC V hV).1.interior_eq]
    exact (hC V hV).2.1.nonempty)
  let : Countable C := hcount.to_subtype
  have hpiece (V : C) : volume (v '' V.val) ≤ κ V.val := by
    apply (Real.volume_le_diam _).trans
    rw [← ofReal_measureReal]
    apply Metric.ediam_le
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    rw [edist_dist,Real.dist_eq]
    apply ENNReal.ofReal_le_ofReal
    have hfwd (a b : ℝ) (ha : a ∈ V.val) (hb : b ∈ V.val) (hab : a ≤ b) :
        |v b-v a| ≤ κ.real V.val := by
      have hI : Icc a b ⊆ V.val := (hC _ V.property).2.1.isPreconnected.ordConnected.out ha hb
      exact (hpay a ((hC _ V.property).2.2 ha) b ((hC _ V.property).2.2 hb)
        hab (hI.trans (hC _ V.property).2.2)).trans (measureReal_mono hI)
    rcases le_total x y with h | h
    · simpa only [abs_sub_comm] using hfwd x y hx hy h
    · exact hfwd y x hy hx h
  have hunion : (⋃ V : C, V.val) = U := by
    apply Subset.antisymm
    · exact iUnion_subset (fun V => (hC _ V.property).2.2)
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨connectedComponentIn U x,x,hx,rfl⟩,mem_connectedComponentIn hx⟩
  have hdp : Pairwise (Disjoint on fun V : C => V.val) := by
    intro V W hne
    exact hd V.property W.property (fun he => hne (Subtype.ext he))
  calc
    volume (v '' U) = volume (⋃ V : C, v '' V.val) := by rw [← image_iUnion,hunion]
    _ ≤ ∑' V : C, volume (v '' V.val) := measure_iUnion_le _
    _ ≤ ∑' V : C, κ V.val := ENNReal.tsum_le_tsum hpiece
    _ = κ U := by rw [← measure_iUnion hdp (fun V => (hC _ V.property).1.measurableSet),hunion]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RoundHoleOffsets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single positive offset works for a finite family of disjoint round
holes. The enlarged closed holes remain disjoint and inside the given
open region, including when an original hole has radius zero. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_common_round_hole_offset
    {I : Type*} [Fintype I] (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {U : Set ℂ} (hU : IsOpen U) (hin : ∀ i, closedBall (c i) (r i) ⊆ U) :
    ∃ ε > 0, ∀ ρ ∈ Ioc (0 : ℝ) ε,
      (∀ i, closedBall (c i) (r i + ρ) ⊆ U) ∧
      Pairwise (Disjoint on fun i => closedBall (c i) (r i + ρ)) := by
  classical
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ (closedBall (c i) (r i))) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet isClosed_closedBall isClosed_closedBall (hd hij)
  obtain ⟨V, hV, hVdisj⟩ := hn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (closedBall (c i) (r i)))
  have he (i : I) : ∃ δ > 0, closedBall (c i) (r i + δ) ⊆ V i ∩ U := by
    obtain ⟨δ, hδ, hs⟩ := (isCompact_closedBall (c i) (r i)).exists_cthickening_subset_open
      ((hV i).1.inter hU) (fun z hz => ⟨(hV i).2 hz, hin i hz⟩)
    refine ⟨δ, hδ, ?_⟩
    simpa only [cthickening_closedBall hδ.le (hr i), add_comm δ] using hs
  choose δ hδ hδsub using he
  let S : Finset ℝ := insert 1 (Finset.univ.image δ)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let ε := S.min' hS
  have hε : 0 < ε := by
    have hm : ε ∈ S := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]; exact zero_lt_one
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      rw [← hi]
      exact hδ i
  have hεi (i : I) : ε ≤ δ i :=
    Finset.min'_le S (δ i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  refine ⟨ε, hε, ?_⟩
  intro ρ hρ
  have hsub (i : I) : closedBall (c i) (r i + ρ) ⊆ V i ∩ U :=
    (closedBall_subset_closedBall (add_le_add le_rfl (hρ.2.trans (hεi i)))).trans (hδsub i)
  exact ⟨fun i z hz => (hsub i hz).2, fun i j hij => (hVdisj hij).mono
    (fun z hz => (hsub i hz).1) (fun z hz => (hsub j hz).1)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedComponentCorrespondence
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed correspondence on the full spheres. On the domain it is
the conformal map; over a complementary component its fiber is the
whole matching component. This includes disk-to-point and point-to-disk
matches, where a continuous single-valued extension need not exist. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem componentRelation_closed (hf : IsConformalEquivalence f G (f '' G)) :
    IsClosed {z : Sphere × Sphere | D.componentRelation z.1 z.2} := by
  change IsClosed (⋂ n, D.relationStage n)
  apply isClosed_iInter
  intro n
  apply IsClosed.union
  · apply IsCompact.isClosed
    apply (D.cores n).isCompact.image_of_continuousOn
    exact continuousOn_id.prodMk (fun q hq => (hf.1 q ((D.cores n).subset hq)).1.continuousWithinAt.mono
      (D.cores n).subset)
  · apply isClosed_iUnion_of_finite
    intro i
    exact (isCompact_closedTerminalCap _).isClosed.prod (isCompact_closedTerminalCap _).isClosed

 theorem componentRelation_on_domain {q p : Sphere} (hq : q ∈ G)
    (h : D.componentRelation q p) : p = f q := by
  obtain ⟨n,hn⟩ := mem_iUnion.mp (D.cover.symm ▸ hq)
  rcases (D.relationStage_iff n q p).mp (mem_iInter.mp h n) with hqp | ⟨i,hqi,_⟩
  · exact hqp.2
  · rw [SmoothJordanCore.carrier,interior_closedJordanCore] at hn
    exact (hn (mem_iUnion.mpr ⟨i,hqi⟩)).elim

 theorem componentRelation_target_fiber (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    ∃ q ∈ Gᶜ, {q' | D.componentRelation q' p} = connectedComponentIn Gᶜ q := by
  let E := D.endAt hG hf p hp
  refine ⟨E.source,E.outside,?_⟩
  ext q'
  constructor
  · intro h
    rw [E.source_eq]
    apply mem_iInter.mpr
    intro n
    rcases (D.relationStage_iff n q' p).mp (mem_iInter.mp h n) with hg | ⟨i,hqi,hpi⟩
    · exact (hp ⟨q',(D.cores n).subset hg.1,hg.2.symm⟩).elim
    · have hpb : p ∈ closedTerminalCap (D.disks n (E.address n)) :=
        mem_iInter.mp (E.target_eq ▸ mem_connectedComponentIn hp) n
      have hi : i = E.address n := by
        by_contra hne
        exact Set.disjoint_left.mp (disjoint_closedTerminalCaps _ (D.disjoint n) hne) hpi hpb
      simpa only [hi] using hqi
  · intro h
    apply mem_iInter.mpr
    intro n
    apply (D.relationStage_iff n q' p).mpr
    exact Or.inr ⟨E.address n,mem_iInter.mp (E.source_eq ▸ h) n,
      mem_iInter.mp (E.target_eq ▸ mem_connectedComponentIn hp) n⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedRelationNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed relation with compact target sends a neighborhood of a
compact source set into every open neighborhood of its fibers. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_relation_neighborhood {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] {R : X → Y → Prop}
    (hR : IsClosed {p : X × Y | R p.1 p.2}) {K : Set X} {U : Set Y}
    (hU : IsOpen U) (hKU : ∀ x ∈ K, ∀ y, R x y → y ∈ U) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, ∀ y, R x y → y ∈ U := by
  let B := {p : X × Y | R p.1 p.2} ∩ (univ ×ˢ Uᶜ)
  have hB : IsClosed B := hR.inter (isClosed_univ.prod hU.isClosed_compl)
  have hproj : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  refine ⟨(Prod.fst '' B)ᶜ,hproj.isOpen_compl,?_,?_⟩
  · intro x hx
    rintro ⟨p,hp,hpx⟩
    have hr : R p.1 p.2 := hp.1
    have hr' : R x p.2 := by simpa only [hpx] using hr
    exact hp.2.2 (hKU x hx p.2 hr')
  · intro x hx y hxy
    by_contra hy
    exact hx ⟨(x,y),⟨hxy,⟨mem_univ _,hy⟩⟩,rfl⟩

 theorem closed_relation_selection_continuousAt {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {R : X → Y → Prop} (hR : IsClosed {p : X × Y | R p.1 p.2})
    (b : X → Y) (hb : ∀ x, R x (b x)) {x : X}
    (hfiber : ∀ y, R x y → y = b x) : ContinuousAt b x := by
  apply continuousAt_def.mpr
  intro U hU
  obtain ⟨W,hWU,hW,hxW⟩ := mem_nhds_iff.mp hU
  obtain ⟨V,hV,hxV,hmap⟩ := closed_relation_neighborhood (K := {x}) hR hW (by
    intro z hz y hzy
    rw [mem_singleton_iff] at hz
    subst z
    rwa [hfiber y hzy])
  filter_upwards [hV.mem_nhds (hxV (mem_singleton x))] with z hz
  exact hWU (hmap z hz (b z) (hb z))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentRelationSelection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual selections from the matched component correspondence. They
agree with the conformal map on the domain, are constant on each omitted
component, and are continuous at every singleton target fiber. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem selectedTarget_mem (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (q : Sphere) : D.componentRelation q (D.selectedTarget hG hf q) :=
  (D.targetFiber_nonempty hG hf q).some_mem

 theorem selectedTarget_on_domain (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    {q : Sphere} (hq : q ∈ G) : D.selectedTarget hG hf q = f q :=
  D.componentRelation_on_domain hq (D.selectedTarget_mem hG hf q)

 theorem componentRelation_source_saturated (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q q' p : Sphere}
    (hq : q ∈ Gᶜ) (hqq : q' ∈ connectedComponentIn Gᶜ q)
    (hr : D.componentRelation q p) : D.componentRelation q' p := by
  obtain ⟨t,ht,he⟩ := D.componentRelation_source_fiber hG hf hq
  have hp : p ∈ (f '' G)ᶜ := by
    apply connectedComponentIn_subset (f '' G)ᶜ t
    rw [← he]
    exact hr
  obtain ⟨s,hs,hse⟩ := D.componentRelation_target_fiber hG hf hp
  have hqs : q ∈ connectedComponentIn Gᶜ s := by
    rw [← hse]
    exact hr
  have hcc : connectedComponentIn Gᶜ q = connectedComponentIn Gᶜ s :=
    (connectedComponentIn_eq hqs).symm
  change q' ∈ {q' | D.componentRelation q' p}
  rw [hse,← hcc]
  exact hqq

 theorem targetFiber_eq_on_component (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q q' : Sphere}
    (hq : q ∈ Gᶜ) (hqq : q' ∈ connectedComponentIn Gᶜ q) :
    D.targetFiber q = D.targetFiber q' := by
  have hq' : q' ∈ Gᶜ := connectedComponentIn_subset _ _ hqq
  have hback : q ∈ connectedComponentIn Gᶜ q' := by
    rw [← connectedComponentIn_eq hqq]
    exact mem_connectedComponentIn hq
  ext p
  exact ⟨D.componentRelation_source_saturated hG hf hq hqq,
    D.componentRelation_source_saturated hG hf hq' hback⟩

 theorem selectedTarget_eq_on_component (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q q' : Sphere}
    (hq : q ∈ Gᶜ) (hqq : q' ∈ connectedComponentIn Gᶜ q) :
    D.selectedTarget hG hf q = D.selectedTarget hG hf q' := by
  unfold selectedTarget
  simp only [D.targetFiber_eq_on_component hG hf hq hqq]

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CountableMatchedComponents
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional component pairs in the trace argument are countable:
one side has nonempty interior. Common point pairs remain unrestricted. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem IsComplementaryComponent.eq_component_of_mem {G K : Set Sphere}
    (hK : IsComplementaryComponent G K) {q : Sphere} (hq : q ∈ K) :
    K = connectedComponentIn Gᶜ q := by
  obtain ⟨p,_,rfl⟩ := hK
  exact connectedComponentIn_eq hq

 theorem circle_component_singleton_or_interior {G K : Set Sphere}
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hK : IsComplementaryComponent G K) :
    (∃ q, K = {q}) ∨ (interior K).Nonempty := by
  obtain ⟨p,hp,rfl⟩ := hK
  rcases hG.2.2 p hp with hpoint | hround
  · exact Or.inl hpoint
  · have hn : OnePoint.infty ∉ connectedComponentIn Gᶜ p :=
      fun h => (connectedComponentIn_subset _ _ h) hinf
    obtain ⟨c,r,hr,he⟩ := isRoundClosedDisk_eq_euclidean hround hn
    right
    rw [he]
    refine ⟨(c : Sphere),mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset ((OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball).mem_nhds
      (mem_image_of_mem _ (Metric.mem_ball_self hr))) (image_mono Metric.ball_subset_closedBall)

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem exists_matched_pair_of_source (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q : Sphere} (hq : q ∈ Gᶜ) :
    ∃ P : Set Sphere × Set Sphere, D.IsMatchedComponentPair P ∧
      P.1 = connectedComponentIn Gᶜ q := by
  obtain ⟨p,hp,he⟩ := D.componentRelation_source_fiber hG hf hq
  refine ⟨(connectedComponentIn Gᶜ q,connectedComponentIn (f '' G)ᶜ p),
    ⟨⟨q,hq,rfl⟩,⟨p,hp,rfl⟩,?_⟩,rfl⟩
  intro q' hq'
  exact (D.targetFiber_eq_on_component hG hf hq hq').symm.trans he

 theorem matched_pair_indexed_or_common_point
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {P : Set Sphere × Set Sphere} (hP : D.IsMatchedComponentPair P) :
    ((interior P.1).Nonempty ∨ (interior P.2).Nonempty) ∨
      ((∃ q, P.1 = {q}) ∧ (∃ p, P.2 = {p})) := by
  rcases circle_component_singleton_or_interior hG hinf hP.1 with hq | hi
  · rcases circle_component_singleton_or_interior hG' hinf' hP.2.1 with hp | hi
    · exact Or.inr ⟨hq,hp⟩
    · exact Or.inl (Or.inr hi)
  · exact Or.inl (Or.inl hi)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneComponentRelation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed matched correspondence in the finite source chart. Every
point has a singleton fiber or belongs to one of the actual indexed disks. -/
open Set Function Filter Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem planeRelation_closed (hf : IsConformalEquivalence f G (f '' G)) :
    IsClosed {p : ℂ × Sphere | D.planeRelation p.1 p.2} :=
  (D.componentRelation_closed hf).preimage
    ((OnePoint.continuous_coe.comp continuous_fst).prodMk continuous_snd)

 theorem plane_fiber_singleton_or_indexed
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (z : ℂ) :
    (∀ p, D.planeRelation z p → p = D.selectedTarget hG.1 hf (z : Sphere)) ∨
      ∃ j : D.IndexedMatchedPair, (z : Sphere) ∈ j.val.1 := by
  by_cases hz : (z : Sphere) ∈ G
  · left
    intro p hp
    exact (D.componentRelation_on_domain hz hp).trans (D.selectedTarget_on_domain hG.1 hf hz).symm
  · obtain ⟨P,hP,hPe⟩ := D.exists_matched_pair_of_source hG.1 hf hz
    have hzP : (z : Sphere) ∈ P.1 := by rw [hPe]; exact mem_connectedComponentIn hz
    rcases D.matched_pair_indexed_or_common_point hG hinf hG' hinf' hP with hi | ⟨_,hp⟩
    · exact Or.inr ⟨⟨P,hP,hi⟩,hzP⟩
    · left
      obtain ⟨p,hp⟩ := hp
      have he : D.targetFiber (z : Sphere) = {p} := (hP.2.2 _ hzP).trans hp
      intro t ht
      have ht' : t = p := mem_singleton_iff.mp (he ▸ ht)
      have hs : D.selectedTarget hG.1 hf (z : Sphere) = p :=
        mem_singleton_iff.mp (he ▸ D.selectedTarget_mem hG.1 hf (z : Sphere))
      exact ht'.trans hs.symm

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactCoordinateTest
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An axial coordinate on a bounded sphere complement can be represented
by a smooth compact planar test. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_71
theorem exists_smooth_compact_coordinate_test {H : Set Sphere}
    (hH : IsOpen H) (hinf : OnePoint.infty ∈ H) (i : Fin 2) :
    ∃ Φ : EuclideanPlane → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      ∀ z : ℂ, (z : Sphere) ∈ Hᶜ →
        sphereFromPlaneFunction Φ (z : Sphere) = (complexPlaneCoordinates.symm z) i := by
  have hK : IsCompact (physicalPlaneDomain H)ᶜ := by
    have hh := (isCompact_finite_preimage hH.isClosed_compl (not_not.mpr hinf)).image
      complexPlaneCoordinates.symm.continuous
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_compl_iff,physicalPlaneDomain,mem_preimage,mem_image]
    constructor
    · intro hx
      exact ⟨complexPlaneCoordinates x,hx,complexPlaneCoordinates.symm_apply_apply x⟩
    · rintro ⟨z,hz,rfl⟩
      simpa only [planeSphere,ContinuousLinearEquiv.apply_symm_apply] using hz
  obtain ⟨η,V,hη,hsη,_,_,_,hKV,hηV⟩ :=
    exists_smooth_compact_cutoff_one_near hK isOpen_univ (subset_univ _)
  refine ⟨(fun x => η x*x i),hη.mul (by fun_prop),hsη.mul_right,?_⟩
  intro z hz
  rw [sphereFromPlaneFunction_coe]
  have hx : complexPlaneCoordinates.symm z ∈ (physicalPlaneDomain H)ᶜ := by
    simpa only [mem_compl_iff,physicalPlaneDomain,mem_preimage,planeSphere,
      ContinuousLinearEquiv.apply_symm_apply] using hz
  rw [hηV _ (hKV hx),one_mul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedCoordinateTest
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact scalar test recovers each actual finite target coordinate
on all source complementary components. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_72
theorem selectedTarget_outside (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q : Sphere} (hq : q ∈ Gᶜ) :
    D.selectedTarget hG hf q ∈ (f '' G)ᶜ := by
  obtain ⟨p,_,he⟩ := D.componentRelation_source_fiber hG hf hq
  have hm : D.selectedTarget hG hf q ∈ {p' | D.componentRelation q p'} :=
    D.selectedTarget_mem hG hf q
  rw [he] at hm
  exact connectedComponentIn_subset _ _ hm

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialTargetDiskMeasure
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact axial cost of an indexed target disk is at most twice its
radius, including a zero-radius target component. -/
open Set Function MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem physical_coordinate_difference_le (k : Fin 2) (z c : ℂ) :
    |(complexPlaneCoordinates.symm z) k-(complexPlaneCoordinates.symm c) k| ≤ ‖z-c‖ := by
  fin_cases k
  · change |z.re-c.re| ≤ ‖z-c‖
    exact Complex.abs_re_le_norm (z-c)
  · change |z.im-c.im| ≤ ‖z-c‖
    exact Complex.abs_im_le_norm (z-c)

 theorem axial_closedBall_image_measure_le (k : Fin 2) (c : ℂ) {r : ℝ} (_hr : 0 ≤ r) :
    volume ((fun z => (complexPlaneCoordinates.symm z) k) '' closedBall c r) ≤
      ENNReal.ofReal (2*r) := by
  have hsub : ((fun z => (complexPlaneCoordinates.symm z) k) '' closedBall c r) ⊆
      Icc ((complexPlaneCoordinates.symm c) k-r) ((complexPlaneCoordinates.symm c) k+r) := by
    rintro _ ⟨z,hz,rfl⟩
    have hh := (physical_coordinate_difference_le k z c).trans (by simpa only [mem_closedBall,dist_eq_norm] using hz)
    exact ⟨by linarith [(abs_le.mp hh).1],by linarith [(abs_le.mp hh).2]⟩
  apply (measure_mono hsub).trans_eq
  rw [Real.volume_Icc]
  congr 1
  ring

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}

 theorem MatchedRoundDisks.target_axial_image_measure_le (E : D.MatchedRoundDisks)
    (k : Fin 2) (j : D.IndexedMatchedPair) :
    volume ((fun p => (complexPlaneCoordinates.symm (finiteCoord p)) k) '' j.val.2) ≤
      ENNReal.ofReal (2*E.targetRadius j) := by
  rw [E.target_eq,image_image]
  simpa only [finiteCoord_coe,Function.comp_def] using
    axial_closedBall_image_measure_le k (E.targetCenter j) (E.target_nonneg j)

 theorem MatchedRoundDisks.target_scalar_image_measure_le (E : D.MatchedRoundDisks)
    (k : Fin 2) (j : D.IndexedMatchedPair) {φ : Sphere → ℝ}
    (hφ : ∀ p ∈ (f '' G)ᶜ, φ p = (complexPlaneCoordinates.symm (finiteCoord p)) k) :
    volume (φ '' j.val.2) ≤ ENNReal.ofReal (2*E.targetRadius j) := by
  have he : φ '' j.val.2 = (fun p => (complexPlaneCoordinates.symm (finiteCoord p)) k) '' j.val.2 := by
    apply image_congr
    intro p hp
    obtain ⟨q,_,hK⟩ := j.property.1.2.1
    exact hφ p (connectedComponentIn_subset _ _ (hK ▸ hp))
  rw [he]
  exact E.target_axial_image_measure_le k j

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialLineDifferentiation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative of either target coordinate along a unit source axis
is bounded by the complex derivative norm. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem complexCoordinateLine_contDiff (i : Fin 2) (y : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (complexCoordinateLine i y) :=
  Complex.equivRealProdCLM.symm.contDiff.comp (realCoordinateLine_contDiff i y)

 theorem complexCoordinateLine_hasDerivAt (i : Fin 2) (y x : ℝ) :
    HasDerivAt (complexCoordinateLine i y) (if i = 0 then 1 else Complex.I) x := by
  fin_cases i
  · exact Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  · exact Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x y).prodMk (hasDerivAt_id x))

 theorem axial_complex_deriv (i : Fin 2) (y x : ℝ) {F : ℂ → ℂ}
    (hF : DifferentiableAt ℂ F (complexCoordinateLine i y x)) :
    HasDerivAt (fun t => F (complexCoordinateLine i y t))
      (deriv F (complexCoordinateLine i y x)*(if i = 0 then 1 else Complex.I)) x := by
  have h := (hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x
    (complexCoordinateLine_hasDerivAt i y x)
  change HasDerivAt (F ∘ complexCoordinateLine i y)
    ((if i = 0 then 1 else Complex.I)*deriv F (complexCoordinateLine i y x)) x at h
  simpa only [Function.comp_def,mul_comm] using h

 theorem axial_coordinate_deriv_le (i k : Fin 2) (y x : ℝ) {F : ℂ → ℂ}
    (hF : DifferentiableAt ℂ F (complexCoordinateLine i y x)) :
    |deriv (fun t => (complexPlaneCoordinates.symm (F (complexCoordinateLine i y t))) k) x| ≤
      ‖deriv F (complexCoordinateLine i y x)‖ := by
  have hd := axial_complex_deriv i y x hF
  have hn : ‖deriv F (complexCoordinateLine i y x)*(if i = 0 then 1 else Complex.I)‖ =
      ‖deriv F (complexCoordinateLine i y x)‖ := by
    split <;> simp
  fin_cases k
  · change |deriv (fun t => (F (complexCoordinateLine i y t)).re) x| ≤ _
    have he := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd).deriv
    change deriv (fun t => (F (complexCoordinateLine i y t)).re) x = _ at he
    rw [he]
    exact (Complex.abs_re_le_norm _).trans_eq hn
  · change |deriv (fun t => (F (complexCoordinateLine i y t)).im) x| ≤ _
    have he := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd).deriv
    change deriv (fun t => (F (complexCoordinateLine i y t)).im) x = _ at he
    rw [he]
    exact (Complex.abs_im_le_norm _).trans_eq hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_EnclosedCircleChords
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chords of disks inside an outer circle. The selected crossed disks
are exactly those whose transverse interval contains the line. -/
open Set Function Metric
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem horizontalChord_strict (c : ℂ) {r y : ℝ}
    (hy : y ∈ Ioo (c.im-r) (c.im+r)) :
    (horizontalChord c r y).1 < (horizontalChord c r y).2 := by
  have hp : 0 < r^2-(y-c.im)^2 := by
    nlinarith [mul_pos (show 0 < r-(y-c.im) by linarith [hy.2])
      (show 0 < r+(y-c.im) by linarith [hy.1])]
  have hs := Real.sqrt_pos.mpr hp
  dsimp only [horizontalChord]
  linarith

 theorem horizontalChord_endpoint_dist (c : ℂ) {r y : ℝ} (hr : 0 ≤ r)
    (hy : y ∈ Icc (c.im-r) (c.im+r)) (right : Bool) :
    dist (⟨if right then (horizontalChord c r y).2 else (horizontalChord c r y).1,y⟩ : ℂ) c = r := by
  have hs := Real.sq_sqrt (horizontalChord_nonneg c hr hy)
  rw [dist_eq_norm]
  have hn := Complex.sq_norm ((⟨if right then (horizontalChord c r y).2 else (horizontalChord c r y).1,y⟩ : ℂ)-c)
  cases right <;>
    simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,horizontalChord,Complex.normSq_apply,
      Complex.sub_re,Complex.sub_im] at hn ⊢ <;>
    nlinarith [norm_nonneg ((⟨c.re-Real.sqrt (r^2-(y-c.im)^2),y⟩ : ℂ)-c),
      norm_nonneg ((⟨c.re+Real.sqrt (r^2-(y-c.im)^2),y⟩ : ℂ)-c)]

 theorem axialChord_endpoint_dist (i : Fin 2) (c : ℂ) {r y : ℝ} (hr : 0 ≤ r)
    (hy : y ∈ Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r)) (right : Bool) :
    dist (complexCoordinateLine i y
      (if right then (axialChord i c r y).2 else (axialChord i c r y).1)) c = r := by
  rw [← axialSwap_dist i,axialSwap_line]
  exact horizontalChord_endpoint_dist _ hr (by simpa only [axialSwap_im] using hy) right

 theorem enclosed_crossing_iff {κ : Type*} [Fintype κ]
    (i : Fin 2) (c : κ → ℂ) (r : κ → ℝ) {R y : ℝ} (hR : 0 ≤ R)
    (hy : y ∈ Icc (-R) R)
    (hin : ∀ j, closedBall (c j) (r j) ⊆ closedBall 0 R) (j : κ) :
    j ∈ crossingDisks (fun j => axialSwap i (c j)) r y
      (axialChord i 0 R y).1 (axialChord i 0 R y).2 ↔
      y ∈ Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j) := by
  constructor
  · intro hj
    simpa only [axialSwap_im] using crossingDisk_line_hit hj
  · intro hj
    obtain ⟨x,hx⟩ := (complexCoordinateLine_meets_closedBall i y (c j) (r j)).mpr hj
    apply mem_crossingDisks.mpr
    refine ⟨x,?_,(horizontal_mem_swapped_disk i x y (c j) (r j)).mpr hx⟩
    exact (mem_closedBall_iff_mem_axialChord i 0 hR (by
      simpa [transverseCoordinate] using hy)).mp (hin j hx)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialClosedDiskIntegral
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral on an actual outer chord is the corresponding slice
of the globally zero-extended source density. -/
open Set Function Filter MeasureTheory Metric
noncomputable section
namespace CircleDomainRigidity

 theorem axial_closed_disk_integral (i : Fin 2) (y : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hy : y ∈ Icc (-R) R) {U : Set ℂ} (hU : MeasurableSet U) (q : ℂ → ℝ) :
    (∫ x in Icc (axialChord i 0 R y).1 (axialChord i 0 R y).2 ∩
        {x | complexCoordinateLine i y x ∈ U}, q (complexCoordinateLine i y x)) =
      ∫ x, (U ∩ closedBall 0 R).indicator q (complexCoordinateLine i y x) := by
  classical
  have hmem (x : ℝ) : complexCoordinateLine i y x ∈ closedBall 0 R ↔
      x ∈ Icc (axialChord i 0 R y).1 (axialChord i 0 R y).2 :=
    mem_closedBall_iff_mem_axialChord i 0 hR (by simpa [transverseCoordinate] using hy)
  have hset : MeasurableSet (Icc (axialChord i 0 R y).1 (axialChord i 0 R y).2 ∩
      {x | complexCoordinateLine i y x ∈ U}) :=
    measurableSet_Icc.inter (hU.preimage (complexCoordinateLine_contDiff i y).continuous.measurable)
  rw [← integral_indicator hset]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hu : complexCoordinateLine i y x ∈ U <;>
    by_cases hx : x ∈ Icc (axialChord i 0 R y).1 (axialChord i 0 R y).2 <;>
    simp [hu,hx,hmem]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableConstantPieces
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of a function that is constant on countably many
closed pieces and continuous on their complement. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

 theorem measurable_of_countable_constant_pieces
    {X Y ι : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] [Countable ι]
    (K : ι → Set X) (hK : ∀ j, IsClosed (K j)) (b : X → Y)
    (v : ι → Y) (hv : ∀ j x, x ∈ K j → b x = v j)
    (hc : ContinuousOn b (⋃ j, K j)ᶜ) : Measurable b := by
  classical
  let S := ⋃ j, K j
  have hS : MeasurableSet S := MeasurableSet.iUnion (fun j => (hK j).measurableSet)
  have hbc : Measurable (Sᶜ.domRestrict b) :=
    (continuousOn_iff_continuous_domRestrict.mp hc).measurable
  intro U hU
  have hleft : MeasurableSet (b ⁻¹' U ∩ Sᶜ) := by
    convert hS.compl.subtype_image (hbc hU) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_image,domRestrict_apply]
    exact ⟨fun h => ⟨⟨x,h.2⟩,h.1,rfl⟩,fun ⟨p,hp,hpx⟩ => hpx ▸ ⟨hp,p.property⟩⟩
  have he : b ⁻¹' U = (b ⁻¹' U ∩ Sᶜ) ∪ ⋃ j, if v j ∈ U then K j else ∅ := by
    ext x
    constructor
    · intro hx
      by_cases hs : x ∈ S
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hs
        have hu : v j ∈ U := by rw [← hv j x hj]; exact hx
        exact Or.inr (mem_iUnion.mpr ⟨j,by rw [ite_eq_left hu]; exact hj⟩)
      · exact Or.inl ⟨hx,hs⟩
    · rintro (hx | hx)
      · exact hx.1
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
        split_ifs at hj with hu
        · change b x ∈ U
          rwa [hv j x hj]
        · exact hj.elim
  rw [he]
  apply hleft.union
  apply MeasurableSet.iUnion
  intro j
  split_ifs
  · exact (hK j).measurableSet
  · exact MeasurableSet.empty

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_FiniteMatchedField
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual selected matched field is finite, measurable, and bounded
on every compact part of the source plane. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_73
theorem planeRelation_ne_infty (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {z : ℂ} {p : Sphere} (hp : D.planeRelation z p) : p ≠ OnePoint.infty := by
  by_cases hz : (z : Sphere) ∈ G
  · intro he
    have hze : f (z : Sphere) = f OnePoint.infty :=
      (D.componentRelation_on_domain hz hp).symm.trans (he.trans hfix.symm)
    exact OnePoint.coe_ne_infty z (hf.bijOn.injOn hz hinf hze)
  · obtain ⟨q,_,hqe⟩ := D.componentRelation_source_fiber hG hf hz
    have hq : p ∈ connectedComponentIn (f '' G)ᶜ q := hqe ▸ hp
    intro he
    exact (connectedComponentIn_subset _ _ hq) (he.symm ▸ (hfix ▸ mem_image_of_mem f hinf))

 theorem selectedTarget_finite (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (z : ℂ) : D.selectedTarget hG hf (z : Sphere) ≠ OnePoint.infty :=
  D.planeRelation_ne_infty hG hinf hf hfix (D.selectedTarget_mem hG hf _)

 theorem selectedPlane_measurable [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G) :
    Measurable (D.selectedPlane hG.1 hf) := by
  apply measurable_of_countable_constant_pieces
    (fun j => closedBall (E.sourceCenter j) (E.sourceRadius j))
    (fun _ => isClosed_closedBall) (D.selectedPlane hG.1 hf)
    (fun j => D.selectedPlane hG.1 hf (E.sourceCenter j))
  · intro j z hz
    have hc : (E.sourceCenter j : Sphere) ∈ j.val.1 := by
      rw [E.source_eq]
      exact mem_image_of_mem _ (mem_closedBall_self (E.source_nonneg j))
    have hz' : (z : Sphere) ∈ j.val.1 := by rw [E.source_eq]; exact mem_image_of_mem _ hz
    have hcg : (E.sourceCenter j : Sphere) ∈ Gᶜ := by
      rw [j.property.1.1.eq_component_of_mem hc] at hc
      exact connectedComponentIn_subset _ _ hc
    have he := D.selectedTarget_eq_on_component hG.1 hf hcg
      (show (z : Sphere) ∈ connectedComponentIn Gᶜ (E.sourceCenter j : Sphere) by
        rw [← j.property.1.1.eq_component_of_mem hc]; exact hz')
    exact congrArg finiteCoord he.symm
  · intro z hz
    have hsingle := (D.plane_fiber_singleton_or_indexed hG hinf hf hH hinf' z).resolve_right (by
      rintro ⟨j,hj⟩
      rw [E.source_eq] at hj
      obtain ⟨w,hw,hew⟩ := hj
      have hwz : w = z := OnePoint.coe_injective hew
      subst w
      exact hz (mem_iUnion.mpr ⟨j,hw⟩))
    have hs : ContinuousAt (fun z : ℂ => D.selectedTarget hG.1 hf (z : Sphere)) z :=
      (closed_relation_selection_continuousAt (D.planeRelation_closed hf)
        _ (fun z => D.selectedTarget_mem hG.1 hf (z : Sphere)) hsingle)
    have hc : ContinuousAt finiteCoord (D.selectedTarget hG.1 hf (z : Sphere)) :=
      (continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ)
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt (isOpen_compl_singleton.mem_nhds
        (D.selectedTarget_finite hG.1 hinf hf hfix z))
    exact (hc.comp_of_eq hs rfl).continuousWithinAt

 theorem compact_relation_finite_image (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {K : Set ℂ} (hK : IsCompact K) :
    IsCompact {w : ℂ | ∃ z ∈ K, ∃ p, D.planeRelation z p ∧ finiteCoord p = w} := by
  let S := (K ×ˢ (univ : Set Sphere)) ∩ {p : ℂ × Sphere | D.planeRelation p.1 p.2}
  have hS : IsCompact S := (hK.prod isCompact_univ).inter_right (D.planeRelation_closed hf)
  have hT := hS.image continuous_snd
  have havoid : OnePoint.infty ∉ Prod.snd '' S := by
    rintro ⟨⟨z,p⟩,hp,he⟩
    exact D.planeRelation_ne_infty hG hinf hf hfix hp.2 he
  have hcont := continuousOn_finiteCoord_of_avoids_infty havoid
  convert hT.image_of_continuousOn hcont using 1
  all_goals try with_reducible_and_instances rfl
  ext w
  simp only [S,mem_image,mem_inter_iff,mem_prod,mem_univ,and_true,Prod.exists]
  constructor
  · rintro ⟨z,hz,p,hr,rfl⟩
    exact ⟨p,⟨z,p,⟨hz,hr⟩,rfl⟩,rfl⟩
  · rintro ⟨p,⟨z,q,⟨hz,hr⟩,rfl⟩,rfl⟩
    exact ⟨z,hz,q,hr,rfl⟩

 theorem selectedPlane_bounded_on_compact (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ K, ‖D.selectedPlane hG hf z‖ < B := by
  obtain ⟨B,hB,hbound⟩ := (D.compact_relation_finite_image hG hinf hf hfix hK).isBounded.exists_pos_norm_lt
  exact ⟨B,hB,fun z hz => hbound _ ⟨z,hz,_,D.selectedTarget_mem hG hf _,rfl⟩⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedDiskNeighborhood
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform upper control of the actual selected field on circles shrinking
to an indexed source disk, including point-to-disk matches. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem selectedPlane_near_indexed_disk
    (E : D.MatchedRoundDisks) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G))
    (j : D.IndexedMatchedPair) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ closedBall (E.sourceCenter j) (E.sourceRadius j+δ),
      ‖D.selectedPlane hG hf z-E.targetCenter j‖ < E.targetRadius j+ε := by
  let U : Set Sphere := ((↑) : ℂ → Sphere) '' ball (E.targetCenter j) (E.targetRadius j+ε)
  have hU : IsOpen U := OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_ball
  obtain ⟨V,hV,hKV,hrel⟩ := closed_relation_neighborhood (D.componentRelation_closed hf)
    (K := j.val.1) hU (by
      intro q hq p hp
      have hpt : p ∈ j.val.2 := by
        rw [← j.property.1.2.2 q hq]
        exact hp
      rw [E.target_eq] at hpt
      obtain ⟨w,hw,rfl⟩ := hpt
      exact mem_image_of_mem _ (show w ∈ ball (E.targetCenter j) (E.targetRadius j+ε) from
        lt_of_le_of_lt hw (lt_add_of_pos_right _ hε)))
  have hVp : IsOpen (((↑) : ℂ → Sphere) ⁻¹' V) := hV.preimage OnePoint.continuous_coe
  have hsub : closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ ((↑) : ℂ → Sphere) ⁻¹' V := by
    intro z hz
    apply hKV
    rw [E.source_eq]
    exact mem_image_of_mem _ hz
  obtain ⟨δ,hδ,hd⟩ := (isCompact_closedBall (E.sourceCenter j) (E.sourceRadius j)).exists_cthickening_subset_open
    hVp hsub
  have hδsub : closedBall (E.sourceCenter j) (E.sourceRadius j+δ) ⊆
      ((↑) : ℂ → Sphere) ⁻¹' V := by
    simpa only [cthickening_closedBall hδ.le (E.source_nonneg j),add_comm δ] using hd
  refine ⟨δ,hδ,?_⟩
  intro z hz
  have hp := hrel (z : Sphere) (hδsub hz) _ (D.selectedTarget_mem hG hf _)
  obtain ⟨w,hw,he⟩ := hp
  unfold selectedPlane
  rw [← he,finiteCoord_coe]
  simpa only [mem_ball,dist_eq_norm] using hw

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_QuadrantFlux
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle flux expressed on four quarter arcs. This representation
uses the same boundary values as the axial slice integrals. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem quadrantNormal_norm (s t : Bool) (θ : ℝ) : ‖quadrantNormal s t θ‖ = 1 := by
  have hn : ‖quadrantNormal s t θ‖^2 = 1 := by
    rw [Complex.sq_norm]
    have hc := Real.cos_sq_add_sin_sq θ
    cases s <;> cases t <;>
      norm_num [quadrantNormal,quadrantSign,Complex.normSq_apply] <;> nlinarith
  nlinarith [norm_nonneg (quadrantNormal s t θ)]

 theorem quadrantFlux_sub_const (F : ℂ → ℂ) (b c : ℂ) (r : ℝ) :
    quadrantFlux (fun z => F z-b) c r = quadrantFlux F c r := by
  unfold quadrantFlux
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [sub_mul,Complex.sub_re,Finset.sum_sub_distrib]
  have hz : (∑ s : Bool, ∑ t : Bool, (b*star (quadrantNormal s t θ)).re) = 0 := by
    simp [quadrantNormal,quadrantSign,Complex.mul_re]
    ring
  rw [hz,sub_zero]

 theorem quadrantFlux_abs_le {F : ℂ → ℂ} {c : ℂ} {r ε : ℝ}
    (hr : 0 ≤ r) (_hε : 0 ≤ ε)
    (hb : ∀ s t θ, θ ∈ Icc (0 : ℝ) (Real.pi/2) → ‖F (quadrantPoint c r s t θ)‖ ≤ ε) :
    |quadrantFlux F c r| ≤ 2*Real.pi*r*ε := by
  have hπ : 0 ≤ Real.pi/2 := by positivity
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun θ => r*∑ s : Bool, ∑ t : Bool, (F (quadrantPoint c r s t θ)*star (quadrantNormal s t θ)).re)
    (a := (0 : ℝ)) (b := Real.pi/2) (C := r*(4*ε)) (fun θ hθ => by
      rw [uIoc_of_le hπ] at hθ
      have hθ' : θ ∈ Icc (0 : ℝ) (Real.pi/2) := ⟨hθ.1.le,hθ.2⟩
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hr]
      apply mul_le_mul_of_nonneg_left _ hr
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ s : Bool, ∑ t : Bool, ε := by
          apply Finset.sum_le_sum
          intro s _
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          apply Finset.sum_le_sum
          intro t _
          exact (Complex.abs_re_le_norm _).trans ((by
            rw [norm_mul,norm_star,quadrantNormal_norm,mul_one]
            exact hb s t θ hθ') : ‖F (quadrantPoint c r s t θ)*star (quadrantNormal s t θ)‖ ≤ ε)
        _ = 4*ε := by simp <;> ring)
  change ‖quadrantFlux F c r‖ ≤ _ at h
  rw [Real.norm_eq_abs,sub_zero,abs_of_nonneg hπ] at h
  exact h.trans_eq (by ring)

 theorem quadrantFlux_near_const {F : ℂ → ℂ} {b c : ℂ} {r ε : ℝ}
    (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hb : ∀ s t θ, θ ∈ Icc (0 : ℝ) (Real.pi/2) → ‖F (quadrantPoint c r s t θ)-b‖ ≤ ε) :
    |quadrantFlux F c r| ≤ 2*Real.pi*r*ε := by
  rw [← quadrantFlux_sub_const F b]
  exact quadrantFlux_abs_le hr hε hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedInnerCircleFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inner-circle flux bound uses the actual closed correspondence,
not a boundary extension of the conformal map. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem quadrantPoint_dist (c : ℂ) (r : ℝ) (s t : Bool) (θ : ℝ) :
    dist (quadrantPoint c r s t θ) c = |r| := by
  simp only [quadrantPoint,dist_eq_norm,add_sub_cancel_left,norm_mul,
    quadrantNormal_norm,mul_one,Complex.norm_real,Real.norm_eq_abs]

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem indexed_quadrantFlux_bound (E : D.MatchedRoundDisks) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (j : D.IndexedMatchedPair)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ ∈ Ioc (0 : ℝ) δ,
      |quadrantFlux (D.selectedPlane hG hf) (E.sourceCenter j) (E.sourceRadius j+ρ)| ≤
        2*Real.pi*(E.sourceRadius j+ρ)*(E.targetRadius j+ε) := by
  obtain ⟨δ,hδ,hnear⟩ := D.selectedPlane_near_indexed_disk E hG hf j hε
  refine ⟨δ,hδ,?_⟩
  intro ρ hρ
  have hr : 0 ≤ E.sourceRadius j+ρ := add_nonneg (E.source_nonneg j) hρ.1.le
  apply quadrantFlux_near_const (b := E.targetCenter j) hr
    (add_nonneg (E.target_nonneg j) hε.le)
  intro s t θ _
  apply (hnear _ ?_).le
  rw [mem_closedBall,quadrantPoint_dist,abs_of_nonneg hr]
  exact add_le_add le_rfl hρ.2

 theorem indexed_quadrantFlux_limiting_bound (E : D.MatchedRoundDisks) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (j : D.IndexedMatchedPair)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ ∈ Ioc (0 : ℝ) δ,
      quadrantFlux (D.selectedPlane hG hf) (E.sourceCenter j) (E.sourceRadius j+ρ) ≤
        2*Real.pi*E.sourceRadius j*E.targetRadius j+ε := by
  have hc : ContinuousAt (fun t : ℝ => 2*Real.pi*(E.sourceRadius j+t)*(E.targetRadius j+t)) 0 := by fun_prop
  obtain ⟨ζ,hζ,hζbound⟩ := Metric.continuousAt_iff.mp hc ε hε
  let η := min (ζ/2) 1
  have hη : 0 < η := lt_min (by positivity) zero_lt_one
  have hηζ : η < ζ := (min_le_left (ζ/2) 1).trans_lt (by linarith)
  have hlimit := hζbound (show dist η 0 < ζ by simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_pos hη] using hηζ)
  obtain ⟨δ,hδ,hbound⟩ := D.indexed_quadrantFlux_bound E hG hf j hη
  refine ⟨min δ η,lt_min hδ hη,?_⟩
  intro ρ hρ
  have hb := hbound ρ ⟨hρ.1,hρ.2.trans (min_le_left _ _)⟩
  have hρη : ρ ≤ η := hρ.2.trans (min_le_right _ _)
  have hm : 2*Real.pi*(E.sourceRadius j+ρ)*(E.targetRadius j+η) ≤
      2*Real.pi*(E.sourceRadius j+η)*(E.targetRadius j+η) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl hρη)
      (mul_nonneg (by norm_num) Real.pi_pos.le)) (add_nonneg (E.target_nonneg j) hη.le)
  have hlim : 2*Real.pi*(E.sourceRadius j+η)*(E.targetRadius j+η) <
      2*Real.pi*E.sourceRadius j*E.targetRadius j+ε := by
    rw [dist_eq_norm,Real.norm_eq_abs] at hlimit
    simp only [add_zero] at hlimit
    linarith [(abs_lt.mp hlimit).2]
  exact (le_abs_self _).trans (hb.trans (hm.trans hlim.le))

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedIntervalIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable bounded scalar data are integrable on every finite interval. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem intervalIntegrable_of_measurable_bound {g : ℝ → ℝ}
    (hg : Measurable g) {a b C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ x ∈ uIcc a b, |g x| ≤ C) : IntervalIntegrable g volume a b := by
  apply (intervalIntegrable_iff' (by finiteness)).mpr
  have hi : IntegrableOn (fun _ : ℝ => C) (uIcc a b) volume :=
    integrableOn_const measure_Icc_lt_top.ne
  apply hi.mono' hg.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
  simpa only [Real.norm_eq_abs] using hb x hx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuarterCircleSubstitution
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotone one-dimensional substitutions for quarter-circle projections.
The scalar integrand may be measurable rather than continuous. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem integral_quarter_sin (g : ℝ → ℝ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ θ in (0 : ℝ)..(Real.pi/2), g (c+r*Real.sin θ)*(r*Real.cos θ)) =
      ∫ y in c..(c+r), g y := by
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hd (θ : ℝ) : HasDerivAt (fun t => c+r*Real.sin t) (r*Real.cos θ) θ :=
    (Real.hasDerivAt_sin θ).const_mul r |>.const_add c
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun θ => c+r*Real.sin θ) (f' := fun θ => r*Real.cos θ) (g := g)
    (by fun_prop) (fun θ _ => hd θ) (by
      intro θ hθ
      rw [min_eq_left hπ,max_eq_right hπ] at hθ
      exact mul_nonneg hr (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],hθ.2.le⟩))
  simpa only [Function.comp_def,Real.sin_zero,mul_zero,add_zero,Real.sin_pi_div_two,mul_one] using h

 theorem integral_quarter_cos (g : ℝ → ℝ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ θ in (0 : ℝ)..(Real.pi/2), g (c+r*Real.cos θ)*(r*Real.sin θ)) =
      ∫ x in c..(c+r), g x := by
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hd (θ : ℝ) : HasDerivAt (fun t => c+r*Real.cos t) (-(r*Real.sin θ)) θ := by
    simpa only [mul_neg] using (Real.hasDerivAt_cos θ).const_mul r |>.const_add c
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (f := fun θ => c+r*Real.cos θ) (f' := fun θ => -(r*Real.sin θ)) (g := g)
    (by fun_prop) (fun θ _ => hd θ) (by
      intro θ hθ
      rw [min_eq_left hπ,max_eq_right hπ] at hθ
      exact neg_nonpos.mpr (mul_nonneg hr (Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le,by linarith [hθ.2,Real.pi_pos]⟩)))
  simp only [Function.comp_def,Real.cos_zero,mul_one,Real.cos_pi_div_two,mul_zero,add_zero,
    mul_neg,intervalIntegral.integral_neg] at h
  rw [intervalIntegral.integral_symm c (c+r)] at h
  exact neg_injective h

 theorem quarter_sin_sqrt {r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) :
    Real.sqrt (r^2-(r*Real.sin θ)^2) = r*Real.cos θ := by
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have he : r^2-(r*Real.sin θ)^2 = (r*Real.cos θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [he,Real.sqrt_sq (mul_nonneg hr hc)]

 theorem quarter_cos_sqrt {r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) :
    Real.sqrt (r^2-(r*Real.cos θ)^2) = r*Real.sin θ := by
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1,by linarith [hθ.2,Real.pi_pos]⟩
  have he : r^2-(r*Real.cos θ)^2 = (r*Real.sin θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [he,Real.sqrt_sq (mul_nonneg hr hs)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuarterCircleSignedSubstitution
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflected quarter-circle projections, with the positive transverse
Lebesgue orientation. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem integral_quarter_sin_sub (g : ℝ → ℝ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ θ in (0 : ℝ)..(Real.pi/2), g (c-r*Real.sin θ)*(r*Real.cos θ)) =
      ∫ y in (c-r)..c, g y := by
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hd (θ : ℝ) : HasDerivAt (fun t => c-r*Real.sin t) (-(r*Real.cos θ)) θ := by
    simpa only [neg_mul] using ((Real.hasDerivAt_sin θ).const_mul r).const_sub c
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (f := fun θ => c-r*Real.sin θ) (f' := fun θ => -(r*Real.cos θ)) (g := g)
    (by fun_prop) (fun θ _ => hd θ) (by
      intro θ hθ
      rw [min_eq_left hπ,max_eq_right hπ] at hθ
      exact neg_nonpos.mpr (mul_nonneg hr (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1,Real.pi_pos],hθ.2.le⟩)))
  simp only [Function.comp_def,Real.sin_zero,mul_zero,sub_zero,Real.sin_pi_div_two,mul_one,
    mul_neg,intervalIntegral.integral_neg] at h
  rw [intervalIntegral.integral_symm (c-r) c] at h
  exact neg_injective h

 theorem integral_quarter_cos_sub (g : ℝ → ℝ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ θ in (0 : ℝ)..(Real.pi/2), g (c-r*Real.cos θ)*(r*Real.sin θ)) =
      ∫ x in (c-r)..c, g x := by
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hd (θ : ℝ) : HasDerivAt (fun t => c-r*Real.cos t) (r*Real.sin θ) θ := by
    simpa only [mul_neg,neg_neg] using ((Real.hasDerivAt_cos θ).const_mul r).const_sub c
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun θ => c-r*Real.cos θ) (f' := fun θ => r*Real.sin θ) (g := g)
    (by fun_prop) (fun θ _ => hd θ) (by
      intro θ hθ
      rw [min_eq_left hπ,max_eq_right hπ] at hθ
      exact mul_nonneg hr (Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le,by linarith [hθ.2,Real.pi_pos]⟩))
  simpa only [Function.comp_def,Real.cos_zero,mul_one,Real.cos_pi_div_two,mul_zero,sub_zero] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleProjectionEndpoints
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The endpoint maps in axial slicing are exactly the four quarter arcs. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem horizontalCirclePoint_quarter (c : ℂ) {r θ : ℝ} (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) (s t : Bool) :
    horizontalCirclePoint s c r (c.im+quadrantSign t*r*Real.sin θ) = quadrantPoint c r s t θ := by
  have he : (c.im+quadrantSign t*r*Real.sin θ-c.im)^2 = (r*Real.sin θ)^2 := by
    cases t <;> simp [quadrantSign]
  apply Complex.ext
  · simp only [horizontalCirclePoint,he,quarter_sin_sqrt hr hθ,quadrantPoint,quadrantNormal,
      Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  · simp only [horizontalCirclePoint,quadrantPoint,quadrantNormal,Complex.add_im,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    ring

 theorem verticalCirclePoint_quarter (c : ℂ) {r θ : ℝ} (hr : 0 ≤ r)
    (hθ : θ ∈ Icc (0 : ℝ) (Real.pi/2)) (s t : Bool) :
    verticalCirclePoint t c r (c.re+quadrantSign s*r*Real.cos θ) = quadrantPoint c r s t θ := by
  have he : (c.re+quadrantSign s*r*Real.cos θ-c.re)^2 = (r*Real.cos θ)^2 := by
    cases s <;> simp [quadrantSign]
  apply Complex.ext
  · simp only [verticalCirclePoint,quadrantPoint,quadrantNormal,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  · simp only [verticalCirclePoint,he,quarter_cos_sqrt hr hθ,quadrantPoint,quadrantNormal,
      Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleProjectionIntegrable
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual circle endpoint values are measurable and bounded, hence
all axial and quarter-arc flux integrals are genuine integrals. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem horizontalCirclePoint_mem (c : ℂ) {r y : ℝ} (hr : 0 ≤ r)
    (hy : y ∈ Icc (c.im-r) (c.im+r)) (s : Bool) : horizontalCirclePoint s c r y ∈ closedBall c r := by
  cases s
  · have h := (mem_closedBall_iff_mem_horizontalChord c hr hy).mpr
      (left_mem_Icc.mpr (horizontalChord_valid c r y))
    simpa [horizontalCirclePoint,horizontalChord,quadrantSign,sub_eq_add_neg] using h
  · have h := (mem_closedBall_iff_mem_horizontalChord c hr hy).mpr
      (right_mem_Icc.mpr (horizontalChord_valid c r y))
    simpa [horizontalCirclePoint,horizontalChord,quadrantSign,sub_eq_add_neg] using h

 theorem verticalCirclePoint_mem (c : ℂ) {r x : ℝ} (hr : 0 ≤ r)
    (hx : x ∈ Icc (c.re-r) (c.re+r)) (t : Bool) : verticalCirclePoint t c r x ∈ closedBall c r := by
  have hhy : x ∈ Icc (transverseCoordinate 1 c-r) (transverseCoordinate 1 c+r) := hx
  have hvalid : (axialChord 1 c r x).1 ≤ (axialChord 1 c r x).2 := horizontalChord_valid _ _ _
  cases t
  · have h := (mem_closedBall_iff_mem_axialChord 1 c hr hhy).mpr (left_mem_Icc.mpr hvalid)
    simpa [verticalCirclePoint,axialChord,horizontalChord,axialSwap,quadrantSign,
      complexCoordinateLine,realCoordinateLine,Complex.equivRealProdCLM_symm_apply,Complex.mk_eq_add_mul_I,sub_eq_add_neg] using h
  · have h := (mem_closedBall_iff_mem_axialChord 1 c hr hhy).mpr (right_mem_Icc.mpr hvalid)
    simpa [verticalCirclePoint,axialChord,horizontalChord,axialSwap,quadrantSign,
      complexCoordinateLine,realCoordinateLine,Complex.equivRealProdCLM_symm_apply,Complex.mk_eq_add_mul_I,sub_eq_add_neg] using h

 theorem continuous_horizontalCirclePoint (s : Bool) (c : ℂ) (r : ℝ) :
    Continuous (horizontalCirclePoint s c r) := by
  change Continuous (fun y => Complex.equivRealProdCLM.symm
    (c.re+quadrantSign s*Real.sqrt (r^2-(y-c.im)^2),y))
  fun_prop

 theorem continuous_verticalCirclePoint (t : Bool) (c : ℂ) (r : ℝ) :
    Continuous (verticalCirclePoint t c r) := by
  change Continuous (fun x => Complex.equivRealProdCLM.symm
    (x,c.im+quadrantSign t*Real.sqrt (r^2-(x-c.re)^2)))
  fun_prop

 theorem circle_projection_integrable {F : ℂ → ℂ} (hF : Measurable F) (c : ℂ) {r B : ℝ}
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hb : ∀ z ∈ closedBall c r, ‖F z‖ ≤ B) :
    IntervalIntegrable (fun y => (F (horizontalCirclePoint true c r y)).re-
      (F (horizontalCirclePoint false c r y)).re) volume (c.im-r) (c.im+r) ∧
    IntervalIntegrable (fun x => (F (verticalCirclePoint true c r x)).im-
      (F (verticalCirclePoint false c r x)).im) volume (c.re-r) (c.re+r) := by
  constructor
  · apply intervalIntegrable_of_measurable_bound (C := 2*B)
      ((Complex.measurable_re.comp (hF.comp (continuous_horizontalCirclePoint true c r).measurable)).sub
        (Complex.measurable_re.comp (hF.comp (continuous_horizontalCirclePoint false c r).measurable)))
      (mul_nonneg (by norm_num) hB)
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    have hright := (Complex.abs_re_le_norm _).trans (hb _ (horizontalCirclePoint_mem c hr hy true))
    have hleft := (Complex.abs_re_le_norm _).trans (hb _ (horizontalCirclePoint_mem c hr hy false))
    exact (abs_sub _ _).trans (by dsimp only [Function.comp_apply] <;> linarith)
  · apply intervalIntegrable_of_measurable_bound (C := 2*B)
      ((Complex.measurable_im.comp (hF.comp (continuous_verticalCirclePoint true c r).measurable)).sub
        (Complex.measurable_im.comp (hF.comp (continuous_verticalCirclePoint false c r).measurable)))
      (mul_nonneg (by norm_num) hB)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have htop := (Complex.abs_im_le_norm _).trans (hb _ (verticalCirclePoint_mem c hr hx true))
    have hbottom := (Complex.abs_im_le_norm _).trans (hb _ (verticalCirclePoint_mem c hr hx false))
    exact (abs_sub _ _).trans (by dsimp only [Function.comp_apply] <;> linarith)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_QuarterFluxIntegrability
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The four quarter-arc coordinate functions of a measurable bounded
field have the integrability needed for the projection identity. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem quadrant_components_integrable {F : ℂ → ℂ} (hF : Measurable F) (c : ℂ) {r B : ℝ}
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hb : ∀ z ∈ closedBall c r, ‖F z‖ ≤ B) (s t : Bool) :
    IntervalIntegrable (fun θ => (F (quadrantPoint c r s t θ)).re) volume 0 (Real.pi/2) ∧
    IntervalIntegrable (fun θ => (F (quadrantPoint c r s t θ)).im) volume 0 (Real.pi/2) := by
  have hq : Continuous (quadrantPoint c r s t) := by
    change Continuous (fun θ => c + (r : ℂ) * Complex.equivRealProdCLM.symm
      (quadrantSign s * Real.cos θ, quadrantSign t * Real.sin θ))
    fun_prop
  have hbound (θ : ℝ) : ‖F (quadrantPoint c r s t θ)‖ ≤ B :=
    hb _ (by rw [mem_closedBall,quadrantPoint_dist,abs_of_nonneg hr])
  constructor
  · exact intervalIntegrable_of_measurable_bound
      (Complex.measurable_re.comp (hF.comp hq.measurable)) hB
      (fun θ _ => (Complex.abs_re_le_norm _).trans (hbound θ))
  · exact intervalIntegrable_of_measurable_bound
      (Complex.measurable_im.comp (hF.comp hq.measurable)) hB
      (fun θ _ => (Complex.abs_im_le_norm _).trans (hbound θ))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CircleProjectionFlux
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sum of the two axial endpoint integrals is exactly circle flux
for bounded measurable boundary values. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem circle_projection_flux {F : ℂ → ℂ} (hF : Measurable F) (c : ℂ) {r B : ℝ}
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hb : ∀ z ∈ closedBall c r, ‖F z‖ ≤ B) :
    horizontalCircleFlux F c r+verticalCircleFlux F c r = quadrantFlux F c r := by
  let q := fun s t θ => F (quadrantPoint c r s t θ)
  let p1 := fun θ => ((q true true θ).re-(q false true θ).re)*(r*Real.cos θ)
  let p2 := fun θ => ((q true false θ).re-(q false false θ).re)*(r*Real.cos θ)
  let p3 := fun θ => ((q true true θ).im-(q true false θ).im)*(r*Real.sin θ)
  let p4 := fun θ => ((q false true θ).im-(q false false θ).im)*(r*Real.sin θ)
  have hq := quadrant_components_integrable hF c hr hB hb
  have hp1 : IntervalIntegrable p1 volume 0 (Real.pi/2) :=
    ((hq true true).1.sub (hq false true).1).mul_continuousOn (by fun_prop)
  have hp2 : IntervalIntegrable p2 volume 0 (Real.pi/2) :=
    ((hq true false).1.sub (hq false false).1).mul_continuousOn (by fun_prop)
  have hp3 : IntervalIntegrable p3 volume 0 (Real.pi/2) :=
    ((hq true true).2.sub (hq true false).2).mul_continuousOn (by fun_prop)
  have hp4 : IntervalIntegrable p4 volume 0 (Real.pi/2) :=
    ((hq false true).2.sub (hq false false).2).mul_continuousOn (by fun_prop)
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have ehp (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi/2)) :
      horizontalCircleIncrement F c r (c.im+r*Real.sin θ) =
        (q true true θ).re-(q false true θ).re := by
    change (F _).re-(F _).re = _
    rw [show c.im+r*Real.sin θ = c.im+quadrantSign true*r*Real.sin θ by simp [quadrantSign]]
    rw [horizontalCirclePoint_quarter c hr hθ, horizontalCirclePoint_quarter c hr hθ]
  have ehm (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi/2)) :
      horizontalCircleIncrement F c r (c.im-r*Real.sin θ) =
        (q true false θ).re-(q false false θ).re := by
    change (F _).re-(F _).re = _
    rw [show c.im-r*Real.sin θ = c.im+quadrantSign false*r*Real.sin θ by simp [quadrantSign,sub_eq_add_neg]]
    rw [horizontalCirclePoint_quarter c hr hθ, horizontalCirclePoint_quarter c hr hθ]
  have evp (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi/2)) :
      verticalCircleIncrement F c r (c.re+r*Real.cos θ) =
        (q true true θ).im-(q true false θ).im := by
    change (F _).im-(F _).im = _
    rw [show c.re+r*Real.cos θ = c.re+quadrantSign true*r*Real.cos θ by simp [quadrantSign]]
    rw [verticalCirclePoint_quarter c hr hθ, verticalCirclePoint_quarter c hr hθ]
  have evm (θ : ℝ) (hθ : θ ∈ Icc 0 (Real.pi/2)) :
      verticalCircleIncrement F c r (c.re-r*Real.cos θ) =
        (q false true θ).im-(q false false θ).im := by
    change (F _).im-(F _).im = _
    rw [show c.re-r*Real.cos θ = c.re+quadrantSign false*r*Real.cos θ by simp [quadrantSign,sub_eq_add_neg]]
    rw [verticalCirclePoint_quarter c hr hθ, verticalCirclePoint_quarter c hr hθ]
  have e1 : (∫ θ in (0 : ℝ)..(Real.pi/2), p1 θ) =
      ∫ y in c.im..(c.im+r), horizontalCircleIncrement F c r y := by
    rw [← integral_quarter_sin (horizontalCircleIncrement F c r) c.im hr]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hπ] at hθ
    dsimp only [p1]
    rw [ehp θ hθ]
  have e2 : (∫ θ in (0 : ℝ)..(Real.pi/2), p2 θ) =
      ∫ y in (c.im-r)..c.im, horizontalCircleIncrement F c r y := by
    rw [← integral_quarter_sin_sub (horizontalCircleIncrement F c r) c.im hr]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hπ] at hθ
    dsimp only [p2]
    rw [ehm θ hθ]
  have e3 : (∫ θ in (0 : ℝ)..(Real.pi/2), p3 θ) =
      ∫ x in c.re..(c.re+r), verticalCircleIncrement F c r x := by
    rw [← integral_quarter_cos (verticalCircleIncrement F c r) c.re hr]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hπ] at hθ
    dsimp only [p3]
    rw [evp θ hθ]
  have e4 : (∫ θ in (0 : ℝ)..(Real.pi/2), p4 θ) =
      ∫ x in (c.re-r)..c.re, verticalCircleIncrement F c r x := by
    rw [← integral_quarter_cos_sub (verticalCircleIncrement F c r) c.re hr]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hπ] at hθ
    dsimp only [p4]
    rw [evm θ hθ]
  obtain ⟨hh,hv⟩ := circle_projection_integrable hF c hr hB hb
  obtain ⟨hhl,hhr⟩ := (IntervalIntegrable.trans_iff (show c.im ∈ uIcc (c.im-r) (c.im+r) by
    rw [uIcc_of_le (by linarith)]; constructor <;> linarith)).mp hh
  obtain ⟨hvl,hvr⟩ := (IntervalIntegrable.trans_iff (show c.re ∈ uIcc (c.re-r) (c.re+r) by
    rw [uIcc_of_le (by linarith)]; constructor <;> linarith)).mp hv
  have edensity (θ : ℝ) : r*(∑ s : Bool, ∑ t : Bool,
      (F (quadrantPoint c r s t θ)*star (quadrantNormal s t θ)).re) =
      p1 θ+p2 θ+p3 θ+p4 θ := by
    simp [quadrantNormal,quadrantSign,p1,p2,p3,p4,q,Complex.mul_re]
    ring
  symm
  change (∫ θ in (0 : ℝ)..(Real.pi/2), _) = _
  simp_rw [edensity]
  rw [intervalIntegral.integral_add ((hp1.add hp2).add hp3) hp4,
    intervalIntegral.integral_add (hp1.add hp2) hp3,intervalIntegral.integral_add hp1 hp2,
    e1,e2,e3,e4]
  have eh := intervalIntegral.integral_add_adjacent_intervals hhl hhr
  have ev := intervalIntegral.integral_add_adjacent_intervals hvl hvr
  unfold horizontalCircleFlux verticalCircleFlux
  dsimp only [horizontalCircleIncrement,verticalCircleIncrement]
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialCircleFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common notation for the two axial circle fluxes. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem axialCircleIncrement_zero (F : ℂ → ℂ) (c : ℂ) (r y : ℝ) :
    axialCircleIncrement 0 F c r y = horizontalCircleIncrement F c r y := by
  change (F (complexCoordinateLine 0 y (axialChord 0 c r y).2)).re-
    (F (complexCoordinateLine 0 y (axialChord 0 c r y).1)).re = _
  simp [horizontalCircleIncrement,axialChord,axialSwap,horizontalChord,
    complexCoordinateLine,realCoordinateLine,horizontalCirclePoint,quadrantSign,
    Complex.equivRealProdCLM_symm_apply,Complex.mk_eq_add_mul_I,sub_eq_add_neg]

 theorem axialCircleIncrement_one (F : ℂ → ℂ) (c : ℂ) (r y : ℝ) :
    axialCircleIncrement 1 F c r y = verticalCircleIncrement F c r y := by
  change (F (complexCoordinateLine 1 y (axialChord 1 c r y).2)).im-
    (F (complexCoordinateLine 1 y (axialChord 1 c r y).1)).im = _
  simp [verticalCircleIncrement,axialChord,axialSwap,horizontalChord,
    complexCoordinateLine,realCoordinateLine,verticalCirclePoint,quadrantSign,
    Complex.equivRealProdCLM_symm_apply,Complex.mk_eq_add_mul_I,sub_eq_add_neg]

 theorem axialCircleFlux_add {F : ℂ → ℂ} (hF : Measurable F) (c : ℂ) {r B : ℝ}
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hb : ∀ z ∈ closedBall c r, ‖F z‖ ≤ B) :
    axialCircleFlux 0 F c r+axialCircleFlux 1 F c r = quadrantFlux F c r := by
  simpa only [axialCircleFlux,transverseCoordinate,ite_true, if_true,Fin.zero_eta,Fin.isValue,
    show ¬ (1 : Fin 2) = 0 by decide,ite_false, if_false,axialCircleIncrement_zero,axialCircleIncrement_one,
    horizontalCircleFlux,verticalCircleFlux] using circle_projection_flux hF c hr hB hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialBandFlux
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero extension of each axial circle increment to all transverse
lines. Its integral is exactly the corresponding circle flux. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem axialBandIncrement_integrable {F : ℂ → ℂ} (hF : Measurable F)
    (i : Fin 2) (c : ℂ) {r B : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hb : ∀ z ∈ closedBall c r, ‖F z‖ ≤ B) : Integrable (axialBandIncrement i F c r) volume := by
  have hi : IntervalIntegrable (axialCircleIncrement i F c r) volume
      (transverseCoordinate i c-r) (transverseCoordinate i c+r) := by
    obtain ⟨hh,hv⟩ := circle_projection_integrable hF c hr hB hb
    fin_cases i
    · change IntervalIntegrable (fun y => axialCircleIncrement 0 F c r y) volume (c.im-r) (c.im+r)
      simpa only [axialCircleIncrement_zero,horizontalCircleIncrement] using hh
    · change IntervalIntegrable (fun y => axialCircleIncrement 1 F c r y) volume (c.re-r) (c.re+r)
      simpa only [axialCircleIncrement_one,verticalCircleIncrement] using hv
  rw [axialBandIncrement,integrable_indicator_iff measurableSet_Icc]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith) (by finiteness)).mp hi

 theorem integral_axialBandIncrement (i : Fin 2) (F : ℂ → ℂ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ y, axialBandIncrement i F c r y) = axialCircleFlux i F c r := by
  rw [axialBandIncrement,integral_indicator measurableSet_Icc,axialCircleFlux,
    intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_EnclosedCrossingSum
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sum over crossed inner circles is the finite sum of their
zero-extended axial increments. -/
open Set Function Metric
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem enclosed_crossing_sum {κ : Type*} [Fintype κ]
    (i : Fin 2) (F : ℂ → ℂ) (c : κ → ℂ) (r : κ → ℝ) {R y : ℝ} (hR : 0 ≤ R)
    (hy : y ∈ Icc (-R) R)
    (hin : ∀ j, closedBall (c j) (r j) ⊆ closedBall 0 R) :
    (∑ j ∈ crossingDisks (fun j => axialSwap i (c j)) r y
      (axialChord i 0 R y).1 (axialChord i 0 R y).2, axialCircleIncrement i F (c j) (r j) y) =
      ∑ j, axialBandIncrement i F (c j) (r j) y := by
  classical
  simp only [crossingDisks,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∃ x ∈ Icc (axialChord i 0 R y).1 (axialChord i 0 R y).2,
      (⟨x,y⟩ : ℂ) ∈ closedBall (axialSwap i (c j)) (r j)) ↔
      y ∈ Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j) := by
    simpa only [mem_crossingDisks] using enclosed_crossing_iff i c r hR hy hin j
  rw [he]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CompactScalarAxialDerivative
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A scalar test agreeing with an axial coordinate near a source point
has exactly the same line derivative there. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem compact_scalar_axial_deriv_le {W : Set ℂ} (hW : IsOpen W)
    {b : ℂ → ℝ} {F : ℂ → ℂ} (i k : Fin 2) (y x : ℝ)
    (hx : complexCoordinateLine i y x ∈ W)
    (hF : DifferentiableAt ℂ F (complexCoordinateLine i y x))
    (hb : ∀ z ∈ W, b z = (complexPlaneCoordinates.symm (F z)) k) :
    |deriv (fun t => b (complexCoordinateLine i y t)) x| ≤
      ‖deriv F (complexCoordinateLine i y x)‖ := by
  have he : (fun t => b (complexCoordinateLine i y t)) =ᶠ[𝓝 x]
      (fun t => (complexPlaneCoordinates.symm (F (complexCoordinateLine i y t))) k) := by
    filter_upwards [((complexCoordinateLine_contDiff i y).continuous.continuousAt.preimage_mem_nhds
      (hW.mem_nhds hx))] with t ht
    exact hb _ ht
  rw [he.deriv_eq]
  exact axial_coordinate_deriv_le i k y x hF

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedRelationIntermediateValue
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed compact-valued relation with connected fibers has the
intermediate-value property over a connected source. This is the
interval coverage needed for the finite-hole slice estimate. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_relation_intermediate_value
    {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace Y] [CompactSpace Y]
    {R : X → Y → Prop} (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hne : ∀ x, ∃ y, R x y)
    (hfiber : ∀ x, IsPreconnected {y | R x y})
    {φ : Y → ℝ} (hφ : Continuous φ)
    {x₀ x₁ : X} {y₀ y₁ : Y} (h₀ : R x₀ y₀) (h₁ : R x₁ y₁)
    {t : ℝ} (ht₀ : φ y₀ ≤ t) (ht₁ : t ≤ φ y₁) :
    ∃ x y, R x y ∧ φ y = t := by
  by_contra hnot
  have hne_t (x : X) (y : Y) (hy : R x y) : φ y ≠ t :=
    fun he => hnot ⟨x,y,hy,he⟩
  let A := {x | ∀ y, R x y → φ y < t}
  let B := {x | ∀ y, R x y → t < φ y}
  have hopen (U : Set ℝ) (hU : IsOpen U) :
      IsOpen {x | ∀ y, R x y → φ y ∈ U} := by
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    obtain ⟨V,hV,hxV,hmap⟩ := closed_relation_neighborhood (K := {x}) hR (hU.preimage hφ) (by
      intro z hz y hzy
      have he := mem_singleton_iff.mp hz
      subst z
      exact hx y hzy)
    exact ⟨V,fun z hz y hzy => hmap z hz y hzy,hV,hxV (mem_singleton x)⟩
  have hA : IsOpen A := hopen (Iio t) isOpen_Iio
  have hB : IsOpen B := hopen (Ioi t) isOpen_Ioi
  have hcover : (univ : Set X) ⊆ A ∪ B := by
    intro x _
    obtain ⟨p,hp⟩ := hne x
    have hc := ((hfiber x).image φ hφ.continuousOn).ordConnected
    rcases lt_or_gt_of_ne (hne_t x p hp) with hpt | htp
    · left
      intro q hq
      apply lt_of_not_ge
      intro htq
      obtain ⟨z,hz,hzt⟩ := hc.out (mem_image_of_mem φ hp) (mem_image_of_mem φ hq) ⟨hpt.le,htq⟩
      exact hne_t x z hz hzt
    · right
      intro q hq
      apply lt_of_not_ge
      intro hqt
      obtain ⟨z,hz,hzt⟩ := hc.out (mem_image_of_mem φ hq) (mem_image_of_mem φ hp) ⟨hqt,htp.le⟩
      exact hne_t x z hz hzt
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨y,hy⟩ := hne x
    exact (not_lt_of_ge (hxA y hy).le) (hxB y hy)
  rcases isPreconnected_univ.subset_or_subset hA hB hdisj hcover with ha | hb
  · exact (not_lt_of_ge ht₁) (ha (mem_univ x₁) y₁ h₁)
  · exact (not_lt_of_ge ht₀) (hb (mem_univ x₀) y₀ h₀)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedIntervalCoverage
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual matched end relation covers all scalar values between
selected endpoints of a source segment. No continuity of the selection
at a nontrivial complementary component is assumed. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem targetFiber_isPreconnected (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (q : Sphere) :
    IsPreconnected (D.targetFiber q) := by
  by_cases hq : q ∈ G
  · have he : D.targetFiber q = {f q} := by
      ext p
      exact ⟨fun hp => D.componentRelation_on_domain hq hp,
        fun hp => (mem_singleton_iff.mp hp) ▸ D.componentRelation_graph hf hq⟩
    rw [he]
    exact isPreconnected_singleton
  · obtain ⟨p,_,he⟩ := D.componentRelation_source_fiber hG hf hq
    change IsPreconnected {p' | D.componentRelation q p'}
    rw [he]
    exact isPreconnected_connectedComponentIn

 theorem interval_fiber_scalar_coverage (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {γ : ℝ → Sphere} (hγ : Continuous γ)
    {φ : Sphere → ℝ} (hφ : Continuous φ) {a b : ℝ} (hab : a ≤ b)
    {pa pb : Sphere} (hpa : D.componentRelation (γ a) pa)
    (hpb : D.componentRelation (γ b) pb)
    {t : ℝ} (ht : t ∈ uIcc (φ pa) (φ pb)) :
    ∃ x ∈ Icc a b, ∃ p, D.componentRelation (γ x) p ∧ φ p = t := by
  let X := Icc a b
  let : PreconnectedSpace X := Subtype.preconnectedSpace isPreconnected_Icc
  let R : X → Sphere → Prop := fun x p => D.componentRelation (γ x) p
  have hR : IsClosed {p : X × Sphere | R p.1 p.2} :=
    (D.componentRelation_closed hf).preimage
      ((hγ.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  have hne (x : X) : ∃ p, R x p := D.targetFiber_nonempty hG hf (γ x)
  have hc (x : X) : IsPreconnected {p | R x p} := D.targetFiber_isPreconnected hG hf (γ x)
  have ha : a ∈ X := left_mem_Icc.mpr hab
  have hb : b ∈ X := right_mem_Icc.mpr hab
  have hqa : R ⟨a,ha⟩ pa := hpa
  have hqb : R ⟨b,hb⟩ pb := hpb
  rcases le_total (φ pa) (φ pb) with h | h
  · rw [uIcc_of_le h] at ht
    obtain ⟨x,p,hxp,hpt⟩ := closed_relation_intermediate_value hR hne hc hφ hqa hqb ht.1 ht.2
    exact ⟨x,x.property,p,hxp,hpt⟩
  · rw [uIcc_of_ge h] at ht
    obtain ⟨x,p,hxp,hpt⟩ := closed_relation_intermediate_value hR hne hc hφ hqb hqa ht.1 ht.2
    exact ⟨x,x.property,p,hxp,hpt⟩

 theorem interval_scalar_coverage (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {γ : ℝ → Sphere} (hγ : Continuous γ)
    {φ : Sphere → ℝ} (hφ : Continuous φ) {a b : ℝ} (hab : a ≤ b)
    {t : ℝ} (ht : t ∈ uIcc (φ (D.selectedTarget hG hf (γ a)))
      (φ (D.selectedTarget hG hf (γ b)))) :
    ∃ x ∈ Icc a b, ∃ p, D.componentRelation (γ x) p ∧ φ p = t :=
  D.interval_fiber_scalar_coverage hG hf hγ hφ hab
    (D.selectedTarget_mem hG hf (γ a)) (D.selectedTarget_mem hG hf (γ b)) ht

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedSliceCover
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar values across an axial segment are covered by actual domain
images, common-point traces and the corresponding remaining target disks. -/
open Set Function Filter
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem scalar_slice_cover
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {γ : ℝ → ℂ} (hγ : Continuous γ) {φ : Sphere → ℝ} (hφ : Continuous φ)
    {a b : ℝ} (hab : a ≤ b) (F : Finset D.IndexedMatchedPair)
    (havoid : ∀ x ∈ Icc a b, ∀ j ∈ F, (γ x : Sphere) ∉ j.val.1) :
    uIcc (φ (D.selectedTarget hG.1 hf (γ a : Sphere)))
      (φ (D.selectedTarget hG.1 hf (γ b : Sphere))) ⊆
      (fun x => φ (f (γ x : Sphere))) '' {x ∈ Icc a b | (γ x : Sphere) ∈ G} ∪
      (fun x => φ (D.selectedTarget hG.1 hf (γ x : Sphere))) ''
        {x ∈ Icc a b | γ x ∈ D.commonPointPlane} ∪
      ⋃ j : {j : D.IndexedMatchedPair // j ∉ F},
        if (∃ x ∈ Icc a b, (γ x : Sphere) ∈ j.val.val.1) then φ '' j.val.val.2 else ∅ := by
  classical
  intro t ht
  obtain ⟨x,hx,p,hp,rfl⟩ := D.interval_scalar_coverage hG.1 hf
    (OnePoint.continuous_coe.comp hγ) hφ hab ht
  by_cases hxG : (γ x : Sphere) ∈ G
  · apply Or.inl
    apply Or.inl
    refine ⟨x,⟨hx,hxG⟩,?_⟩
    rw [D.componentRelation_on_domain hxG hp]
  by_cases hj : ∃ j : D.IndexedMatchedPair, (γ x : Sphere) ∈ j.val.1
  · obtain ⟨j,hxj⟩ := hj
    have hjF : j ∉ F := fun h => havoid x hx j h hxj
    apply Or.inr
    apply mem_iUnion.mpr
    refine ⟨⟨j,hjF⟩,?_⟩
    rw [ite_eq_left (show ∃ z ∈ Icc a b, (γ z : Sphere) ∈ j.val.1 from ⟨x,hx,hxj⟩)]
    refine ⟨p,?_,rfl⟩
    rw [← j.property.1.2.2 (γ x : Sphere) hxj]
    exact hp
  · apply Or.inl
    apply Or.inr
    have hxC : γ x ∈ D.commonPointPlane := ⟨hxG,fun j hj' => hj ⟨j,hj'⟩⟩
    have hsingle := (D.plane_fiber_singleton_or_indexed hG hinf hf hH hinf' (γ x)).resolve_right hj
    exact ⟨x,⟨hx,hxC⟩,congrArg φ (hsingle p hp).symm⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothOpenImageMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The image length of a smooth function on an arbitrary open subset
of a line is bounded by its actual derivative integral. The domain may
have countably many interval components. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_open_image_measure_le {U : Set ℝ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f U)
    (hi : IntegrableOn (fun x => |deriv f x|) U volume) :
    volume (f '' U) ≤ ENNReal.ofReal (∫ x in U, |deriv f x|) := by
  let g := U.indicator (fun x => |deriv f x|)
  have hg : Integrable g volume := (integrable_indicator_iff hU.measurableSet).mpr hi
  have hg0 (x : ℝ) : 0 ≤ g x := indicator_nonneg (fun _ _ => abs_nonneg _) _
  let κ := volume.withDensity (fun x => ENNReal.ofReal (g x))
  let : IsFiniteMeasure κ := ⟨by
    change volume.withDensity (fun x => ENNReal.ofReal (g x)) univ < ∞
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg0)]
    exact ENNReal.ofReal_lt_top⟩
  have hκ {S : Set ℝ} (hS : MeasurableSet S) (hSU : S ⊆ U) :
      κ S = ENNReal.ofReal (∫ x in S, |deriv f x|) := by
    rw [withDensity_apply _ hS,← ofReal_integral_eq_lintegral_ofReal hg.restrict
      (ae_restrict_of_ae (Eventually.of_forall hg0))]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hS] with x hx
    exact indicator_of_mem (hSU hx) _
  rw [← hκ hU.measurableSet Subset.rfl]
  apply open_line_image_measure_le κ hU f
  intro x hx y hy hxy hI
  have hd : ContinuousOn (deriv f) U := by
    have h := (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply (continuousOn_const (c := (1 : ℝ)))
    simpa only [fderiv_apply_one_eq_deriv] using h
  have hint : IntervalIntegrable (deriv f) volume x y :=
    (hd.mono (by simpa only [uIcc_of_le hxy] using hI)).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => ((hf.contDiffAt (hU.mem_nhds (hI (by simpa only [uIcc_of_le hxy] using ht)))).differentiableAt
      (by norm_num)).hasDerivAt) hint
  calc
    |f y-f x| = ‖∫ t in x..y, deriv f t‖ := by rw [he,Real.norm_eq_abs]
    _ ≤ ∫ t in x..y, ‖deriv f t‖ := intervalIntegral.norm_integral_le_integral_norm hxy
    _ = ∫ t in Icc x y, |deriv f t| := by
      rw [intervalIntegral.integral_of_le hxy,← integral_Icc_eq_integral_Ioc]
      simp only [Real.norm_eq_abs]
    _ = κ.real (Icc x y) := by
      rw [measureReal_def,hκ measurableSet_Icc hI,ENNReal.toReal_ofReal]
      exact integral_nonneg (fun _ => abs_nonneg _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothClosedSliceImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Including the two endpoints of a slice does not increase its image
measure. This gives the derivative bound on a closed component segment. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_closed_slice_image_measure_le {V : Set ℝ} (hV : IsOpen V)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f V) {a b : ℝ}
    (hi : IntegrableOn (fun x => |deriv f x|) (Icc a b ∩ V) volume) :
    volume (f '' (Icc a b ∩ V)) ≤
      ENNReal.ofReal (∫ x in Icc a b ∩ V, |deriv f x|) := by
  let U := Ioo a b ∩ V
  have hU : IsOpen U := isOpen_Ioo.inter hV
  have hUV : U ⊆ Icc a b ∩ V := inter_subset_inter Ioo_subset_Icc_self Subset.rfl
  have hsub : f '' (Icc a b ∩ V) ⊆ f '' U ∪ {f a, f b} := by
    rintro _ ⟨x,hx,rfl⟩
    by_cases ha : x = a
    · subst x; exact Or.inr (by simp)
    by_cases hb : x = b
    · subst x; exact Or.inr (by simp)
    exact Or.inl ⟨x,⟨⟨lt_of_le_of_ne hx.1.1 (Ne.symm ha),
      lt_of_le_of_ne hx.1.2 hb⟩,hx.2⟩,rfl⟩
  have hnull : volume ({f a, f b} : Set ℝ) = 0 := ((finite_singleton (f b)).insert (f a)).measure_zero volume
  calc
    _ ≤ volume (f '' U ∪ {f a,f b}) := measure_mono hsub
    _ ≤ volume (f '' U) + volume ({f a,f b} : Set ℝ) := measure_union_le _ _
    _ = volume (f '' U) := by rw [hnull,add_zero]
    _ ≤ ENNReal.ofReal (∫ x in U, |deriv f x|) :=
      smooth_open_image_measure_le hU (hf.mono inter_subset_right) (hi.mono_set hUV)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (setIntegral_mono_set hi
      (Eventually.of_forall (fun _ => abs_nonneg _)) hUV.eventuallyLE)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedSliceEstimate
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical slice estimate for the actual matched correspondence.
Only disks meeting the segment are charged. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem scalar_slice_estimate [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {γ : ℝ → ℂ} (hγ : Continuous γ) {φ : Sphere → ℝ} (hφ : Continuous φ)
    (k : Fin 2) (hcoord : ∀ p ∈ (f '' G)ᶜ,
      φ p = (complexPlaneCoordinates.symm (finiteCoord p)) k)
    {a b : ℝ} (hab : a ≤ b) (F : Finset D.IndexedMatchedPair)
    (havoid : ∀ x ∈ Icc a b, ∀ j ∈ F, (γ x : Sphere) ∉ j.val.1)
    (hnull : volume ((fun x => φ (D.selectedTarget hG.1 hf (γ x : Sphere))) ''
      {x | γ x ∈ D.commonPointPlane}) = 0)
    (hsmooth : ContDiffOn ℝ 1 (fun x => φ (f (γ x : Sphere)))
      {x | (γ x : Sphere) ∈ G})
    (hi : IntegrableOn (fun x => |deriv (fun t => φ (f (γ t : Sphere))) x|)
      (Icc a b ∩ {x | (γ x : Sphere) ∈ G}) volume)
    (hsum : Summable (fun j : {j : D.IndexedMatchedPair // j ∉ F} =>
      if ∃ x ∈ Icc a b, (γ x : Sphere) ∈ j.val.val.1 then 2*E.targetRadius j else 0)) :
    |φ (D.selectedTarget hG.1 hf (γ b : Sphere))-
        φ (D.selectedTarget hG.1 hf (γ a : Sphere))| ≤
      (∫ x in Icc a b ∩ {x | (γ x : Sphere) ∈ G},
        |deriv (fun t => φ (f (γ t : Sphere))) x|) +
      ∑' j : {j : D.IndexedMatchedPair // j ∉ F},
        if ∃ x ∈ Icc a b, (γ x : Sphere) ∈ j.val.val.1 then 2*E.targetRadius j else 0 := by
  classical
  have hV : IsOpen {x | (γ x : Sphere) ∈ G} :=
    hG.1.preimage (OnePoint.continuous_coe.comp hγ)
  apply interval_length_le_integral_and_tolls
    (I := fun j : {j : D.IndexedMatchedPair // j ∉ F} =>
      if ∃ x ∈ Icc a b, (γ x : Sphere) ∈ j.val.val.1 then φ '' j.val.val.2 else ∅)
    (integral_nonneg (fun _ => abs_nonneg _))
    (fun j => by split_ifs <;> [exact mul_nonneg (by norm_num) (E.target_nonneg j); exact le_rfl]) hsum
  · apply measure_mono_null (image_mono (inter_subset_right (s := Icc a b))) hnull
  · exact smooth_closed_slice_image_measure_le hV hsmooth hi
  · intro j
    by_cases hj : ∃ x ∈ Icc a b, (γ x : Sphere) ∈ j.val.val.1
    · simp only [ite_eq_left hj]
      exact E.target_scalar_image_measure_le k j hcoord
    · simp only [ite_eq_right hj,measure_empty,ENNReal.ofReal_zero,le_refl]
  · exact D.scalar_slice_cover hG hinf hf hH hinf' hγ hφ hab F havoid

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SmoothMatchedScalar
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact smooth target scalar supplies all analytic hypotheses of
the actual matched mask. In particular its source differential is L². -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer MatchedConformalEnds
attribute [local instance] sphereMetric sphereBorel

 theorem smooth_compact_sphere_scalar {Φ : EuclideanPlane → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ) :
    Continuous (sphereFromPlaneFunction Φ) ∧
      (∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), sphereFromPlaneFunction Φ p = 0) ∧
      ∃ L : ℝ≥0, LipschitzWith L (fun z : ℂ => sphereFromPlaneFunction Φ (z : Sphere)) := by
  refine ⟨continuous_sphereFromPlaneFunction hΦ.continuous hs,
    sphereFromPlaneFunction_zero_near_infty hs,?_⟩
  let g := Φ ∘ complexPlaneCoordinates.symm
  have hg : ContDiff ℝ ∞ g := hΦ.comp complexPlaneCoordinates.symm.contDiff
  have hgs : HasCompactSupport g := hs.comp_homeomorph complexPlaneCoordinates.symm.toHomeomorph
  obtain ⟨B,hB⟩ := (hg.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).bounded_above_of_compact_support (hgs.fderiv ℝ)
  let L : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hl : LipschitzWith L g := lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable (by simp)) (by
    intro z
    change ‖fderiv ℝ g z‖ ≤ max B 0
    exact (hB z).trans (le_max_left _ _))
  have he : (fun z : ℂ => sphereFromPlaneFunction Φ (z : Sphere)) = g :=
    funext (fun z => sphereFromPlaneFunction_coe Φ z)
  rw [he]
  exact ⟨L,hl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereScalarLineSmooth
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness on the domain of the actual finite chart and of a compact
smooth scalar pulled back along either source axis. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)
include D

 theorem finite_part_contDiffOn (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty) :
    ContDiffOn ℝ ∞ (fun z : ℂ => finiteCoord (f (z : Sphere))) {z | (z : Sphere) ∈ G} := by
  apply DifferentiableOn.contDiffOn _ (hG.preimage OnePoint.continuous_coe) |>.restrict_scalars ℝ
  intro z hz
  exact (analyticAt_finite_map_of_conformal hG hf.1 hz
    (D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hz))).differentiableAt.differentiableWithinAt

 theorem sphere_scalar_line_contDiffOn
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin 2) (y : ℝ) :
    ContDiffOn ℝ 1 (fun x => sphereFromPlaneFunction Φ (f (complexCoordinateLine i y x : Sphere)))
      {x | (complexCoordinateLine i y x : Sphere) ∈ G} := by
  have hF := D.finite_part_contDiffOn hG hinf hf hfix
  have hb := hΦ.comp_contDiffOn (complexPlaneCoordinates.symm.contDiff.comp_contDiffOn hF)
  have hl := hb.comp (complexCoordinateLine_contDiff i y).contDiffOn
    (show MapsTo (complexCoordinateLine i y) {x | (complexCoordinateLine i y x : Sphere) ∈ G}
      {z | (z : Sphere) ∈ G} from fun _ hx => hx)
  apply (hl.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).congr
  intro x hx
  have hne := D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hx)
  simp only [sphereFromPlaneFunction,ite_eq_right hne,Function.comp_apply]

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ActualAxialSlice
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slice estimate for the actual selected finite field and actual
complex derivative, with no assumed variation or image-length bound. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] Classical.propDecidable
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem actual_axial_slice_estimate [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hsΦ : HasCompactSupport Φ)
    {W : Set ℂ} (hW : IsOpen W) (k : Fin 2)
    (hcoord : ∀ p ∈ (f '' G)ᶜ, sphereFromPlaneFunction Φ p =
      (complexPlaneCoordinates.symm (finiteCoord p)) k)
    (hrel : ∀ z ∈ W, ∀ p, D.planeRelation z p → sphereFromPlaneFunction Φ p =
      (complexPlaneCoordinates.symm (finiteCoord p)) k)
    (i : Fin 2) (y : ℝ)
    (htrace : volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) k) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (htoll : Summable (fun j : D.IndexedMatchedPair =>
      (Icc (transverseCoordinate i (E.sourceCenter j)-E.sourceRadius j)
        (transverseCoordinate i (E.sourceCenter j)+E.sourceRadius j)).indicator
          (fun _ => 2*E.targetRadius j) y))
    {a b : ℝ} (hab : a ≤ b) (F : Finset D.IndexedMatchedPair)
    (hsegment : ∀ x ∈ Icc a b, complexCoordinateLine i y x ∈ W)
    (havoid : ∀ x ∈ Icc a b, ∀ j ∈ F, (complexCoordinateLine i y x : Sphere) ∉ j.val.1)
    (hρ : IntegrableOn (fun x => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (complexCoordinateLine i y x)‖)
      (Icc a b ∩ {x | (complexCoordinateLine i y x : Sphere) ∈ G}) volume) :
    |(complexPlaneCoordinates.symm (D.selectedPlane hG.1 hf (complexCoordinateLine i y b))) k-
      (complexPlaneCoordinates.symm (D.selectedPlane hG.1 hf (complexCoordinateLine i y a))) k| ≤
      (∫ x in Icc a b ∩ {x | (complexCoordinateLine i y x : Sphere) ∈ G},
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) (complexCoordinateLine i y x)‖) +
      ∑' j : {j : D.IndexedMatchedPair // j ∉ F},
        if ∃ x ∈ Icc a b, (complexCoordinateLine i y x : Sphere) ∈ j.val.val.1
          then 2*E.targetRadius j else 0 := by
  let φ := sphereFromPlaneFunction Φ
  let bφ := fun z : ℂ => φ (f (z : Sphere))
  let U := {x | (complexCoordinateLine i y x : Sphere) ∈ G}
  let V := Icc a b ∩ U
  have hline := (complexCoordinateLine_contDiff i y).continuous
  have hU : IsOpen U := hG.1.preimage (OnePoint.continuous_coe.comp hline)
  have hV : MeasurableSet V := measurableSet_Icc.inter hU.measurableSet
  have hsm := D.sphere_scalar_line_contDiffOn hG.1 hinf hf hfix hΦ i y
  have hmajor (x : ℝ) (hx : x ∈ V) :
      |deriv (fun t => bφ (complexCoordinateLine i y t)) x| ≤
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) (complexCoordinateLine i y x)‖ := by
    apply compact_scalar_axial_deriv_le
      (hW.inter (hG.1.preimage OnePoint.continuous_coe)) i k y x
      ⟨hsegment x hx.1,hx.2⟩
      ((analyticAt_finite_map_of_conformal hG.1 hf.1 hx.2
        (D.planeRelation_ne_infty hG.1 hinf hf hfix (D.componentRelation_graph hf hx.2))).differentiableAt)
    intro z hz
    exact hrel z hz.1 _ (D.componentRelation_graph hf hz.2)
  have hdermeas : AEStronglyMeasurable (fun x =>
      |deriv (fun t => bφ (complexCoordinateLine i y t)) x|) (volume.restrict V) :=
    ((hsm.continuousOn_deriv_of_isOpen hU le_rfl).abs.mono inter_subset_right).aestronglyMeasurable hV
  have hi : IntegrableOn (fun x => |deriv (fun t => bφ (complexCoordinateLine i y t)) x|) V volume :=
    hρ.mono' hdermeas (by
      filter_upwards [ae_restrict_mem hV] with x hx
      simpa only [Real.norm_eq_abs,abs_abs] using hmajor x hx)
  have hnull : volume ((fun x => φ (D.selectedTarget hG.1 hf (complexCoordinateLine i y x : Sphere))) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0 := by
    convert htrace using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply image_congr
    intro x hx
    exact hcoord _ (D.selectedTarget_outside hG.1 hf hx.1)
  have hsum : Summable (fun j : {j : D.IndexedMatchedPair // j ∉ F} =>
      if ∃ x ∈ Icc a b, (complexCoordinateLine i y x : Sphere) ∈ j.val.val.1
        then 2*E.targetRadius j else 0) := by
    have h := (segment_disk_tolls_summable i E.sourceCenter E.sourceRadius E.targetRadius
      E.target_nonneg htoll a b).subtype (fun j => j ∉ F)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    congr 1
    congr 1
    funext x
    rw [E.source_eq]
    simp only [OnePoint.coe_injective.eq_iff,mem_image,exists_eq_right]
  have hslice := D.scalar_slice_estimate E hG hinf hf hH hinf' hline
    (smooth_compact_sphere_scalar hΦ hsΦ).1 k hcoord hab F havoid hnull hsm hi hsum
  have ha := hrel _ (hsegment a (left_mem_Icc.mpr hab)) _ (D.selectedTarget_mem hG.1 hf _)
  have hb := hrel _ (hsegment b (right_mem_Icc.mpr hab)) _ (D.selectedTarget_mem hG.1 hf _)
  rw [ha,hb] at hslice
  exact hslice.trans (add_le_add (setIntegral_mono_on hi hρ hV hmajor) le_rfl)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactRelationCoordinateTest
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One compact smooth coordinate test agrees with the actual coordinate
on all fibers over a prescribed compact source set and on all target
complementary components. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_74
theorem compact_relation_image (hf : IsConformalEquivalence f G (f '' G))
    {K : Set ℂ} (hK : IsCompact K) :
    IsCompact {p : Sphere | ∃ z ∈ K, D.planeRelation z p} := by
  have h := ((hK.prod (isCompact_univ : IsCompact (univ : Set Sphere))).inter_right
    (D.planeRelation_closed hf)).image continuous_snd
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [mem_image,mem_inter_iff,mem_prod,mem_univ,and_true,Prod.exists]
  constructor
  · rintro ⟨z,hz,hr⟩
    exact ⟨z,p,⟨hz,hr⟩,rfl⟩
  · rintro ⟨z,q,⟨hz,hr⟩,rfl⟩
    exact ⟨z,hz,hr⟩

 theorem exists_compact_relation_coordinate_test
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsOpen (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {K : Set ℂ} (hK : IsCompact K) (k : Fin 2) :
    ∃ Φ : EuclideanPlane → ℝ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
      (∀ p ∈ (f '' G)ᶜ, sphereFromPlaneFunction Φ p =
        (complexPlaneCoordinates.symm (finiteCoord p)) k) ∧
      ∀ z ∈ K, ∀ p, D.planeRelation z p → sphereFromPlaneFunction Φ p =
        (complexPlaneCoordinates.symm (finiteCoord p)) k := by
  let L : Set Sphere := {p | ∃ z ∈ K, D.planeRelation z p} ∪ (f '' G)ᶜ
  have hL : IsClosed L := (D.compact_relation_image hf hK).isClosed.union hH.isClosed_compl
  have hLinf : OnePoint.infty ∉ L := by
    rintro (⟨z,_,hz⟩ | hz)
    · exact D.planeRelation_ne_infty hG hinf hf hfix hz rfl
    · exact hz hinf'
  obtain ⟨Φ,hΦ,hs,hcoord⟩ := exists_smooth_compact_coordinate_test hL.isOpen_compl hLinf k
  have hc (p : Sphere) (hp : p ∈ L) : sphereFromPlaneFunction Φ p =
      (complexPlaneCoordinates.symm (finiteCoord p)) k := by
    cases p using OnePoint.rec with
    | infty => exact (hLinf hp).elim
    | coe z => simpa only [finiteCoord_coe] using hcoord z (not_not.mpr hp)
  exact ⟨Φ,hΦ,hs,fun p hp => hc p (Or.inr hp),fun z hz p hr => hc p (Or.inl ⟨z,hz,hr⟩)⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialSlicesFromTrace
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact scalar used in the slice proof is constructed from the
actual relation. One typical line supports every segment and finite
family of removed source disks inside the working disk. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] Classical.propDecidable
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem axial_slices_of_trace [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (R : ℝ) (i k : Fin 2) (y : ℝ)
    (htrace : volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) k) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (htoll : Summable (fun j : D.IndexedMatchedPair =>
      (Icc (transverseCoordinate i (E.sourceCenter j)-E.sourceRadius j)
        (transverseCoordinate i (E.sourceCenter j)+E.sourceRadius j)).indicator
          (fun _ => 2*E.targetRadius j) y))
    (hρ : IntegrableOn (fun x => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (complexCoordinateLine i y x)‖)
      {x | (complexCoordinateLine i y x : Sphere) ∈ G ∧ complexCoordinateLine i y x ∈ ball 0 R} volume) :
    ∀ a b : ℝ, a ≤ b → ∀ F : Finset D.IndexedMatchedPair,
      (∀ x ∈ Icc a b, complexCoordinateLine i y x ∈ ball 0 R) →
      (∀ x ∈ Icc a b, ∀ j ∈ F, (complexCoordinateLine i y x : Sphere) ∉ j.val.1) →
      |(complexPlaneCoordinates.symm (D.selectedPlane hG.1 hf (complexCoordinateLine i y b))) k-
        (complexPlaneCoordinates.symm (D.selectedPlane hG.1 hf (complexCoordinateLine i y a))) k| ≤
        (∫ x in Icc a b ∩ {x | (complexCoordinateLine i y x : Sphere) ∈ G},
          ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) (complexCoordinateLine i y x)‖) +
        ∑' j : {j : D.IndexedMatchedPair // j ∉ F},
          if ∃ x ∈ Icc a b, (complexCoordinateLine i y x : Sphere) ∈ j.val.val.1
            then 2*E.targetRadius j else 0 := by
  obtain ⟨Φ,hΦ,hsΦ,hcoord,hrel⟩ := D.exists_compact_relation_coordinate_test hG.1 hinf hf hfix
    hH.1 hinf' (isCompact_closedBall (0 : ℂ) R) k
  intro a b hab F hseg havoid
  exact D.actual_axial_slice_estimate E hG hinf hf hfix hH hinf' hΦ hsΦ isOpen_ball k
    hcoord (fun z hz => hrel z (ball_subset_closedBall hz)) i y htrace htoll hab F hseg havoid
    (hρ.mono_set (fun x hx => ⟨hx.2,hseg x hx.1⟩))

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ActualFiniteDiskSlice
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual matched field satisfies the finite enlarged-hole slice
inequality. No independent slice or flux assumption is retained. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_75
theorem actual_finite_disk_slice [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (R : ℝ) (i k : Fin 2) (y : ℝ)
    (htrace : volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) k) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (htoll : Summable (fun j : D.IndexedMatchedPair =>
      (Icc (transverseCoordinate i (E.sourceCenter j)-E.sourceRadius j)
        (transverseCoordinate i (E.sourceCenter j)+E.sourceRadius j)).indicator
          (fun _ => 2*E.targetRadius j) y))
    (hρ : IntegrableOn (fun x => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (complexCoordinateLine i y x)‖)
      {x | (complexCoordinateLine i y x : Sphere) ∈ G ∧ complexCoordinateLine i y x ∈ ball 0 R} volume)
    (F : Finset D.IndexedMatchedPair) {η : ℝ} (hη : 0 < η)
    (hd : Pairwise (Disjoint on fun j : F => closedBall (E.sourceCenter j) (E.sourceRadius j+η)))
    (hone : ∀ l ∉ F, ∀ j ∈ F, ∀ m ∈ F,
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter j) (E.sourceRadius j+η)).Nonempty →
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter m) (E.sourceRadius m+η)).Nonempty → j = m)
    {a b : ℝ} (hab : a < b)
    (hseg : ∀ x ∈ Icc a b, complexCoordinateLine i y x ∈ ball 0 R)
    (ha : ∀ j ∈ F, complexCoordinateLine i y a ∉ closedBall (E.sourceCenter j) (E.sourceRadius j+η))
    (hb : ∀ j ∈ F, complexCoordinateLine i y b ∉ closedBall (E.sourceCenter j) (E.sourceRadius j+η)) :
    let v := fun x => (complexPlaneCoordinates.symm (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) k
    v b-v a-
      (∑ j ∈ crossingDisks (fun j : F => axialSwap i (E.sourceCenter j))
          (fun j => E.sourceRadius j+η) y a b,
        (v (axialChord i (E.sourceCenter j) (E.sourceRadius j+η) y).2-
          v (axialChord i (E.sourceCenter j) (E.sourceRadius j+η) y).1)) ≤
      (∫ x in Icc a b ∩ {x | (complexCoordinateLine i y x : Sphere) ∈ G},
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) (complexCoordinateLine i y x)‖)+
        2*axialDiskToll i (fun j : {j : D.IndexedMatchedPair // j ∉ F} => E.sourceCenter j)
          (fun j => E.sourceRadius j) (fun j => E.targetRadius j) y := by
  dsimp only
  have hmem (j : D.IndexedMatchedPair) (z : ℂ) :
      (z : Sphere) ∈ j.val.1 ↔ z ∈ closedBall (E.sourceCenter j) (E.sourceRadius j) := by
    rw [E.source_eq j]
    constructor
    · rintro ⟨w,hw,he⟩
      exact OnePoint.coe_injective he ▸ hw
    · exact mem_image_of_mem _
  apply finite_disk_slice_payment i E.sourceCenter E.sourceRadius E.targetRadius
    E.source_nonneg E.target_nonneg F hη hd hone hab ha hb
  · exact htoll.comp_injective Subtype.val_injective
  · exact hG.1.measurableSet.preimage (OnePoint.continuous_coe.comp (complexCoordinateLine_contDiff i y).continuous).measurable
  · exact hρ.mono_set (fun x hx => ⟨hx.2,hseg x hx.1⟩)
  · exact fun _ _ => norm_nonneg _
  · intro u w huw hsub havoid
    have hp := D.axial_slices_of_trace E hG hinf hf hfix hH hinf' R i k y htrace htoll hρ u w huw F
      (fun x hx => hseg x (hsub hx)) (by
        intro x hx j hj hxj
        exact havoid x hx j hj ((hmem j _).mp hxj))
    simpa only [hmem] using hp

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ActualEnclosedCircleSlice
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact finite-circle slice inequality for the selected matched
field and the actual zero-extended source differential. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_76
theorem actual_enclosed_circle_slice [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {R W : ℝ} (hR : 0 < R) (hRW : R < W) (i : Fin 2) (y : ℝ) (hy : y ∈ Ioo (-R) R)
    (htrace : volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) i) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (htoll : Summable (fun j : D.IndexedMatchedPair =>
      (Icc (transverseCoordinate i (E.sourceCenter j)-E.sourceRadius j)
        (transverseCoordinate i (E.sourceCenter j)+E.sourceRadius j)).indicator
          (fun _ => 2*E.targetRadius j) y))
    (hρ : IntegrableOn (fun x => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere)))
        (complexCoordinateLine i y x)‖)
      {x | (complexCoordinateLine i y x : Sphere) ∈ G ∧ complexCoordinateLine i y x ∈ ball 0 W} volume)
    (F : Finset D.IndexedMatchedPair) {η : ℝ} (hη : 0 < η)
    (hd : Pairwise (Disjoint on fun j : F => closedBall (E.sourceCenter j) (E.sourceRadius j+η)))
    (hin : ∀ j ∈ F, closedBall (E.sourceCenter j) (E.sourceRadius j+η) ⊆ ball 0 R)
    (hone : ∀ l ∉ F, ∀ j ∈ F, ∀ m ∈ F,
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter j) (E.sourceRadius j+η)).Nonempty →
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter m) (E.sourceRadius m+η)).Nonempty → j = m) :
    axialBandIncrement i (D.selectedPlane hG.1 hf) 0 R y-
      (∑ j : F, axialBandIncrement i (D.selectedPlane hG.1 hf)
        (E.sourceCenter j) (E.sourceRadius j+η) y) ≤
      (∫ x, ({z : ℂ | (z : Sphere) ∈ G} ∩ closedBall 0 R).indicator
        (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖) (complexCoordinateLine i y x))+
        2*axialDiskToll i (fun j : {j : D.IndexedMatchedPair // j ∉ F} => E.sourceCenter j)
          (fun j => E.sourceRadius j) (fun j => E.targetRadius j) y := by
  let a := (axialChord i 0 R y).1
  let b := (axialChord i 0 R y).2
  have hy' : y ∈ Icc (-R) R := Ioo_subset_Icc_self hy
  have hab : a < b := horizontalChord_strict _ (by simpa [axialSwap] using hy)
  have houter (x : ℝ) (hx : x ∈ Icc a b) : complexCoordinateLine i y x ∈ closedBall 0 R :=
    (mem_closedBall_iff_mem_axialChord i 0 hR.le (by simpa [transverseCoordinate] using hy')).mpr hx
  have hend (right : Bool) : dist (complexCoordinateLine i y (if right then b else a)) 0 = R :=
    axialChord_endpoint_dist i 0 hR.le (by simpa [transverseCoordinate] using hy') right
  have ha : ∀ j ∈ F, complexCoordinateLine i y a ∉ closedBall (E.sourceCenter j) (E.sourceRadius j+η) := by
    intro j hj hx
    have hn := hin j hj hx
    have he := hend false
    simp only [Bool.false_eq_true,ite_false, if_false] at he
    exact (not_lt_of_ge he.ge) hn
  have hb : ∀ j ∈ F, complexCoordinateLine i y b ∉ closedBall (E.sourceCenter j) (E.sourceRadius j+η) := by
    intro j hj hx
    have hn := hin j hj hx
    have he := hend true
    simp only [ite_true, if_true] at he
    exact (not_lt_of_ge he.ge) hn
  have h := D.actual_finite_disk_slice E hG hinf hf hfix hH hinf' W i i y htrace htoll hρ F hη hd hone hab
    (fun x hx => (closedBall_subset_ball hRW) (houter x hx)) ha hb
  change axialCircleIncrement i (D.selectedPlane hG.1 hf) 0 R y-
    (∑ j ∈ crossingDisks (fun j : F => axialSwap i (E.sourceCenter j)) (fun j => E.sourceRadius j+η) y a b,
      axialCircleIncrement i (D.selectedPlane hG.1 hf) (E.sourceCenter j) (E.sourceRadius j+η) y) ≤ _ at h
  rw [enclosed_crossing_sum (κ := F) i (D.selectedPlane hG.1 hf)
    (fun j => E.sourceCenter j) (fun j => E.sourceRadius j+η) hR.le hy'
    (fun j => (hin j j.property).trans ball_subset_closedBall)] at h
  have he := axial_closed_disk_integral i y hR.le hy'
    (U := {z : ℂ | (z : Sphere) ∈ G})
    (hG.1.preimage OnePoint.continuous_coe).measurableSet
    (fun z : ℂ => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
  change (∫ x in Icc a b ∩ {x | (complexCoordinateLine i y x : Sphere) ∈ G},
    ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) (complexCoordinateLine i y x)‖) = _ at he
  rw [he] at h
  have hout : axialBandIncrement i (D.selectedPlane hG.1 hf) 0 R y =
      axialCircleIncrement i (D.selectedPlane hG.1 hf) 0 R y := by
    apply indicator_of_mem
    simpa [transverseCoordinate] using hy'
  rwa [← hout] at h

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_AxialLineIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual complex axial parametrizations preserve plane area.
Fubini provides the common integrable line densities. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem axialPlaneHomeomorph_apply (i : Fin 2) (p : ℝ × ℝ) :
    axialPlaneHomeomorph i p = complexCoordinateLine i p.1 p.2 := by
  unfold axialPlaneHomeomorph complexCoordinateLine realCoordinateLine
  split <;> rfl

 theorem complexCoordinatePlane_measurePreserving (i : Fin 2) :
    MeasurePreserving (axialPlaneHomeomorph i) (volume.prod volume) volume := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).comp
    (realCoordinatePlane_measurePreserving i)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact axialPlaneHomeomorph_apply i p

 theorem integral_axial_slices {ρ : ℂ → ℝ} (hρ : Integrable ρ) (i : Fin 2) :
    (∀ᵐ y ∂volume, Integrable (fun x => ρ (complexCoordinateLine i y x)) volume) ∧
    Integrable (fun y => ∫ x, ρ (complexCoordinateLine i y x)) volume ∧
    (∫ y, ∫ x, ρ (complexCoordinateLine i y x)) = ∫ z, ρ z := by
  have hp : Integrable (fun p : ℝ × ℝ => ρ (axialPlaneHomeomorph i p)) (volume.prod volume) :=
    (complexCoordinatePlane_measurePreserving i).integrable_comp_of_integrable hρ
  simp_rw [axialPlaneHomeomorph_apply] at hp
  refine ⟨hp.prod_right_ae,hp.integral_prod_left,?_⟩
  calc
    _ = ∫ p : ℝ × ℝ, ρ (axialPlaneHomeomorph i p) ∂volume.prod volume := by
      simpa only [axialPlaneHomeomorph_apply] using (integral_prod _ hp).symm
    _ = _ := (complexCoordinatePlane_measurePreserving i).integral_comp
      (axialPlaneHomeomorph i).toMeasurableEquiv.measurableEmbedding ρ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_EnclosedFluxIntegration
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the finite-circle slice inequality. Both the exact axial
circle flux and the area integral are retained. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem enclosed_band_subset (i : Fin 2) (c : ℂ) (r R : ℝ)
    (hin : closedBall c r ⊆ ball 0 R) :
    Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r) ⊆ Ioo (-R) R := by
  intro y hy
  obtain ⟨x,hx⟩ := (complexCoordinateLine_meets_closedBall i y c r).mpr hy
  have hb : ‖complexCoordinateLine i y x‖ < R := by
    simpa only [mem_ball,dist_zero_right] using hin hx
  have ht : |y| ≤ ‖complexCoordinateLine i y x‖ := by
    simpa [transverseCoordinate] using complexCoordinateLine_transverse_le i y x 0
  exact abs_lt.mp (ht.trans_lt hb)

 theorem enclosed_flux_integration {κ : Type*} [Fintype κ]
    (i : Fin 2) {F : ℂ → ℂ} (hF : Measurable F) (c : κ → ℂ) (r : κ → ℝ)
    {R B : ℝ} (hR : 0 ≤ R) (hr : ∀ j, 0 ≤ r j) (hB : 0 ≤ B)
    (hb : ∀ z ∈ closedBall (0 : ℂ) R, ‖F z‖ ≤ B)
    (hin : ∀ j, closedBall (c j) (r j) ⊆ ball 0 R)
    {q : ℂ → ℝ} (hq : Integrable q volume) (hq0 : ∀ z, 0 ≤ q z)
    {T : ℝ → ℝ} {C : ℝ} (hT : Integrable T volume) (hT0 : ∀ y, 0 ≤ T y)
    (hTC : (∫ y, T y) ≤ C)
    (hslice : ∀ᵐ y ∂volume, y ∈ Ioo (-R) R →
      axialBandIncrement i F 0 R y-(∑ j, axialBandIncrement i F (c j) (r j) y) ≤
        (∫ x, q (complexCoordinateLine i y x))+2*T y) :
    axialCircleFlux i F 0 R-(∑ j, axialCircleFlux i F (c j) (r j)) ≤ (∫ z, q z)+2*C := by
  have ho := axialBandIncrement_integrable hF i 0 hR hB hb
  have hi (j : κ) := axialBandIncrement_integrable hF i (c j) (hr j) hB
    (fun z hz => hb z (ball_subset_closedBall (hin j hz)))
  have hs : Integrable (fun y => ∑ j, axialBandIncrement i F (c j) (r j) y) volume :=
    integrable_finsetSum _ (fun j _ => hi j)
  have hq' := integral_axial_slices hq i
  have ha : ∀ᵐ y ∂volume,
      axialBandIncrement i F 0 R y-(∑ j, axialBandIncrement i F (c j) (r j) y) ≤
        (∫ x, q (complexCoordinateLine i y x))+2*T y := by
    filter_upwards [hslice,volume.ae_ne (-R),volume.ae_ne R] with y hy hm hp
    by_cases h : y ∈ Ioo (-R) R
    · exact hy h
    · have hn : y ∉ Icc (-R) R := by
        rintro ⟨hl,hu⟩
        exact h ⟨lt_of_le_of_ne hl (Ne.symm hm),lt_of_le_of_ne hu hp⟩
      have hz : axialBandIncrement i F 0 R y = 0 := by
        apply indicator_of_notMem
        simpa [transverseCoordinate] using hn
      have hzj (j : κ) : axialBandIncrement i F (c j) (r j) y = 0 := by
        apply indicator_of_notMem
        exact fun hj => h (enclosed_band_subset i (c j) (r j) R (hin j) hj)
      simp only [hz,hzj,Finset.sum_const_zero,sub_zero]
      exact add_nonneg (integral_nonneg (fun x => hq0 _)) (mul_nonneg (by norm_num) (hT0 y))
  have h := integral_mono_ae (ho.sub hs) (hq'.2.1.add (hT.const_mul 2)) ha
  dsimp only [Pi.sub_apply,Pi.add_apply] at h
  rw [integral_sub ho hs,integral_finsetSum _ (fun j _ => hi j),
    integral_add hq'.2.1 (hT.const_mul 2),integral_const_mul,hq'.2.2,
    integral_axialBandIncrement i F 0 hR] at h
  simp_rw [integral_axialBandIncrement i F _ (hr _)] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hTC (by norm_num : (0 : ℝ) ≤ 2)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_IntegrableAxialRestriction
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini for restrictions to actual measurable plane sets. -/
open Set Function Filter MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem integrable_axial_restriction_ae {U : Set ℂ} (hU : MeasurableSet U)
    {q : ℂ → ℝ} (hq : IntegrableOn q U volume) (i : Fin 2) :
    ∀ᵐ y ∂volume, IntegrableOn (fun x => q (complexCoordinateLine i y x))
      {x | complexCoordinateLine i y x ∈ U} volume := by
  have hi : Integrable (U.indicator q) volume := (integrable_indicator_iff hU).mpr hq
  filter_upwards [(integral_axial_slices hi i).1] with y hy
  apply (integrable_indicator_iff
    (hU.preimage (complexCoordinateLine_contDiff i y).continuous.measurable)).mp
  convert hy using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  by_cases h : complexCoordinateLine i y x ∈ U <;> simp [h]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ActualAxialCircleFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-hole axial flux bound from the proved common-point
trace and the source differential. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_77
theorem actual_axial_circle_flux [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {R W : ℝ} (hR : 0 < R) (hRW : R < W) (i : Fin 2)
    (htrace : ∀ᵐ y ∂volume, volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) i) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (hρ : IntegrableOn (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
      ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 W) volume)
    (F : Finset D.IndexedMatchedPair) {η : ℝ} (hη : 0 < η)
    (hd : Pairwise (Disjoint on fun j : F => closedBall (E.sourceCenter j) (E.sourceRadius j+η)))
    (hin : ∀ j ∈ F, closedBall (E.sourceCenter j) (E.sourceRadius j+η) ⊆ ball 0 R)
    (hone : ∀ l ∉ F, ∀ j ∈ F, ∀ m ∈ F,
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter j) (E.sourceRadius j+η)).Nonempty →
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter m) (E.sourceRadius m+η)).Nonempty → j = m) :
    axialCircleFlux i (D.selectedPlane hG.1 hf) 0 R-
      (∑ j : F, axialCircleFlux i (D.selectedPlane hG.1 hf)
        (E.sourceCenter j) (E.sourceRadius j+η)) ≤
      (∫ z in {z : ℂ | (z : Sphere) ∈ G} ∩ closedBall 0 R,
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)+
        8*∑' j : {j : D.IndexedMatchedPair // j ∉ F}, E.sourceRadius j*E.targetRadius j := by
  let U : Set ℂ := {z | (z : Sphere) ∈ G}
  let q := (U ∩ closedBall 0 R).indicator
    (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
  have hU : MeasurableSet U := (hG.1.preimage OnePoint.continuous_coe).measurableSet
  have hq : Integrable q volume := (integrable_indicator_iff (hU.inter measurableSet_closedBall)).mpr
    (hρ.mono_set (inter_subset_inter_right U (closedBall_subset_ball hRW)))
  obtain ⟨B,hB,hbound⟩ := D.selectedPlane_bounded_on_compact hG.1 hinf hf hfix
    (isCompact_closedBall (0 : ℂ) R)
  have ht := axialDiskToll_integrable i
    (fun j : {j : D.IndexedMatchedPair // j ∉ F} => E.sourceCenter j)
    (fun j => E.sourceRadius j) (fun j => E.targetRadius j)
    (fun j => E.source_nonneg j) (fun j => E.target_nonneg j)
    (E.source_summable.comp_injective Subtype.val_injective)
    (E.target_summable.comp_injective Subtype.val_injective)
  have h := enclosed_flux_integration i
    (D.selectedPlane_measurable E hG hinf hf hfix hH hinf')
    (fun j : F => E.sourceCenter j) (fun j => E.sourceRadius j+η)
    hR.le (fun j => add_nonneg (E.source_nonneg j) hη.le) hB.le
    (fun z hz => (hbound z hz).le) (fun j => hin j j.property) hq
    (fun z => indicator_nonneg (fun z _ => norm_nonneg _) z) ht.1
    (fun y => tsum_nonneg (fun j => indicator_nonneg
      (fun _ _ => mul_nonneg (by norm_num) (E.target_nonneg j)) y)) ht.2 (by
      filter_upwards [htrace,
        axial_disk_tolls_summable_ae i E.sourceCenter E.sourceRadius E.targetRadius
          E.source_nonneg E.target_nonneg E.source_summable E.target_summable,
        integrable_axial_restriction_ae (hU.inter measurableSet_ball) hρ i] with y htrace htoll hline
      intro hy
      exact D.actual_enclosed_circle_slice E hG hinf hf hfix hH hinf' hR hRW i y hy
        htrace htoll hline F hη hd hin hone)
  dsimp only [q] at h
  rw [integral_indicator (hU.inter measurableSet_closedBall)] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ActualFiniteCircleFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adding the two actual axial inequalities gives the full outward
circle flux, with exactly sixteen times the remaining mixed-radius sum. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem actual_finite_circle_flux [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {R W : ℝ} (hR : 0 < R) (hRW : R < W)
    (htrace : ∀ i : Fin 2, ∀ᵐ y ∂volume, volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) i) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (hρ : IntegrableOn (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
      ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 W) volume)
    (F : Finset D.IndexedMatchedPair) {η : ℝ} (hη : 0 < η)
    (hd : Pairwise (Disjoint on fun j : F => closedBall (E.sourceCenter j) (E.sourceRadius j+η)))
    (hin : ∀ j ∈ F, closedBall (E.sourceCenter j) (E.sourceRadius j+η) ⊆ ball 0 R)
    (hone : ∀ l ∉ F, ∀ j ∈ F, ∀ m ∈ F,
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter j) (E.sourceRadius j+η)).Nonempty →
      (closedBall (E.sourceCenter l) (E.sourceRadius l) ∩
        closedBall (E.sourceCenter m) (E.sourceRadius m+η)).Nonempty → j = m) :
    quadrantFlux (D.selectedPlane hG.1 hf) 0 R ≤
      2*(∫ z in {z : ℂ | (z : Sphere) ∈ G} ∩ closedBall 0 R,
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)+
      (∑ j : F, quadrantFlux (D.selectedPlane hG.1 hf) (E.sourceCenter j) (E.sourceRadius j+η))+
      16*∑' j : {j : D.IndexedMatchedPair // j ∉ F}, E.sourceRadius j*E.targetRadius j := by
  have h0 := D.actual_axial_circle_flux E hG hinf hf hfix hH hinf' hR hRW 0 (htrace 0) hρ F hη hd hin hone
  have h1 := D.actual_axial_circle_flux E hG hinf hf hfix hH hinf' hR hRW 1 (htrace 1) hρ F hη hd hin hone
  have hm := D.selectedPlane_measurable E hG hinf hf hfix hH hinf'
  obtain ⟨B,hB,hbound⟩ := D.selectedPlane_bounded_on_compact hG.1 hinf hf hfix
    (isCompact_closedBall (0 : ℂ) R)
  have hout := axialCircleFlux_add hm 0 hR.le hB.le (fun z hz => (hbound z hz).le)
  have hinflux (j : F) := axialCircleFlux_add hm (E.sourceCenter j)
    (add_nonneg (E.source_nonneg j) hη.le) hB.le
    (fun z hz => (hbound z (ball_subset_closedBall (hin j j.property hz))).le)
  have hsum : (∑ j : F, axialCircleFlux 0 (D.selectedPlane hG.1 hf) (E.sourceCenter j) (E.sourceRadius j+η))+
      (∑ j : F, axialCircleFlux 1 (D.selectedPlane hG.1 hf) (E.sourceCenter j) (E.sourceRadius j+η)) =
      ∑ j : F, quadrantFlux (D.selectedPlane hG.1 hf) (E.sourceCenter j) (E.sourceRadius j+η) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hinflux j)
  linarith

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FinitePositiveMinimum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common positive radius for finitely many local estimates. -/
noncomputable section
namespace CircleDomainRigidity

 theorem finite_positive_lower_bound {ι : Type*} [Fintype ι]
    (δ : ι → ℝ) (hδ : ∀ j, 0 < δ j) : ∃ ε > 0, ∀ j, ε ≤ δ j := by
  classical
  let S : Finset ℝ := insert 1 (Finset.univ.image δ)
  have hS : S.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS,?_,?_⟩
  · have hm := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hm with he | he
    · rw [he]; exact zero_lt_one
    · obtain ⟨j,_,he⟩ := Finset.mem_image.mp he
      rw [← he]
      exact hδ j
  · intro j
    exact Finset.min'_le S _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_FiniteInnerFluxLimit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual inner-circle estimates hold simultaneously on every
finite family of matched disks. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem finite_inner_quadrantFlux_limiting_bound (E : D.MatchedRoundDisks) (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (F : Finset D.IndexedMatchedPair)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ ∈ Ioc (0 : ℝ) δ,
      (∑ j : F, quadrantFlux (D.selectedPlane hG hf) (E.sourceCenter j) (E.sourceRadius j+ρ)) ≤
        2*Real.pi*(∑ j ∈ F, E.sourceRadius j*E.targetRadius j)+ε := by
  classical
  have he : 0 < ε/((F.card : ℝ)+1) := div_pos hε (by positivity)
  have hj (j : F) := D.indexed_quadrantFlux_limiting_bound E hG hf j he
  choose δ hδ hbound using hj
  obtain ⟨η,hη,hηδ⟩ := finite_positive_lower_bound δ hδ
  refine ⟨η,hη,?_⟩
  intro ρ hρ
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hbound j ρ ⟨hρ.1,hρ.2.trans (hηδ j)⟩)
  have hbase : (∑ j : F, 2*Real.pi*E.sourceRadius j*E.targetRadius j) =
      2*Real.pi*(∑ j ∈ F, E.sourceRadius j*E.targetRadius j) := by
    have heq : (∑ j : F, E.sourceRadius j*E.targetRadius j) =
        ∑ j ∈ F, E.sourceRadius j*E.targetRadius j :=
      (Finset.sum_subtype F (by simp) (fun j => E.sourceRadius j*E.targetRadius j)).symm
    simp only [mul_assoc,← Finset.mul_sum,heq]
  have herr : (F.card : ℝ)*(ε/((F.card : ℝ)+1)) ≤ ε := by
    have hd : 0 < (F.card : ℝ)+1 := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  rw [Finset.sum_add_distrib,hbase] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at hs
  exact hs.trans (add_le_add le_rfl herr)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ClosedDiskIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Outer circles have zero plane area; the source density integral is
unchanged when the outer disk is closed. -/
open Set Function Filter MeasureTheory Metric
noncomputable section
namespace CircleDomainRigidity

 theorem integral_inter_closedBall_eq_ball (U : Set ℂ) (c : ℂ) (r : ℝ) (q : ℂ → ℝ) :
    (∫ z in U ∩ closedBall c r, q z) = ∫ z in U ∩ ball c r, q z := by
  apply setIntegral_congr_set
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (Measure.addHaar_sphere volume c r)] with z hz
  apply propext
  have hne : dist z c ≠ r := hz
  show (z ∈ U ∩ closedBall c r) ↔ (z ∈ U ∩ ball c r)
  simp only [mem_inter_iff,mem_closedBall,mem_ball]
  exact and_congr_right (fun _ => ⟨fun h => lt_of_le_of_ne h hne,fun h => h.le⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteTailDiskSeparation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finitely many source disks can be enlarged so that every remaining
disk meets at most one enlargement. The radius-square sum supplies the
finite set of large remaining disks. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem finite_large_square_summable_radii {ι : Type*} {r : ι → ℝ}
    (hr : ∀ j, 0 ≤ r j) (hs : Summable (fun j => r j^2)) {ε : ℝ} (hε : 0 < ε) :
    {j | ε ≤ r j}.Finite := by
  have he : ∀ᶠ j in cofinite, r j^2 < ε^2 :=
    hs.tendsto_cofinite_zero (Iio_mem_nhds (sq_pos_of_pos hε))
  have hf := mem_cofinite.mp he
  apply hf.subset
  intro j hj
  change ¬ r j^2 < ε^2
  exact not_lt.mpr ((sq_le_sq₀ hε.le (hr j)).mpr hj)

 theorem dist_centers_le_of_closedBall_inter {c d : ℂ} {r s : ℝ}
    (h : (closedBall c r ∩ closedBall d s).Nonempty) : dist c d ≤ r+s := by
  obtain ⟨x,hx,hx'⟩ := h
  exact (dist_triangle c x d).trans (add_le_add (by simpa only [dist_comm,mem_closedBall] using hx) hx')

 theorem exists_finite_tail_disk_separation {ι : Type*}
    (c : ι → ℂ) (r : ι → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hd : Pairwise (Disjoint on fun j => closedBall (c j) (r j)))
    (hs : Summable (fun j => r j^2)) (F : Finset ι) :
    ∃ ε > 0, ∀ ρ ∈ Ioc (0 : ℝ) ε,
      Pairwise (Disjoint on fun j : F => closedBall (c j) (r j+ρ)) ∧
      ∀ k ∉ F, ∀ i ∈ F, ∀ j ∈ F,
        (closedBall (c k) (r k) ∩ closedBall (c i) (r i+ρ)).Nonempty →
        (closedBall (c k) (r k) ∩ closedBall (c j) (r j+ρ)).Nonempty → i = j := by
  classical
  obtain ⟨δ,hδ,hδprop⟩ := exists_common_round_hole_offset
    (fun j : F => c j) (fun j : F => r j) (fun j => hr j)
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) isOpen_univ
    (fun _ => subset_univ _)
  let B := (finite_large_square_summable_radii hr hs (show 0 < δ/4 by positivity)).toFinset
  let T := F ∪ B
  obtain ⟨η,hη,hηprop⟩ := exists_common_round_hole_offset
    (fun j : T => c j) (fun j : T => r j) (fun j => hr j)
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) isOpen_univ
    (fun _ => subset_univ _)
  refine ⟨min (δ/4) η,lt_min (by positivity) hη,?_⟩
  intro ρ hρ
  have hρδ : ρ ≤ δ/4 := hρ.2.trans (min_le_left _ _)
  have hρη : ρ ≤ η := hρ.2.trans (min_le_right _ _)
  have hpair := (hδprop δ ⟨hδ,le_rfl⟩).2
  refine ⟨?_,?_⟩
  · intro i j hij
    exact (hpair hij).mono
      (closedBall_subset_closedBall (by linarith))
      (closedBall_subset_closedBall (by linarith))
  · intro k hk i hi j hj hki hkj
    by_contra hij
    by_cases hkB : k ∈ B
    · have hkT : k ∈ T := Finset.mem_union_right F hkB
      have hiT : i ∈ T := Finset.mem_union_left B hi
      have hki' : (⟨k,hkT⟩ : T) ≠ ⟨i,hiT⟩ := by
        intro he
        have hki : k = i := congrArg Subtype.val he
        exact hk (hki.symm ▸ hi)
      have hdis : Disjoint (closedBall (c k) (r k)) (closedBall (c i) (r i+ρ)) :=
        ((hηprop ρ ⟨hρ.1,hρη⟩).2 hki').mono_left
          (closedBall_subset_closedBall (le_add_of_nonneg_right hρ.1.le))
      exact Set.disjoint_left.mp hdis hki.choose_spec.1 hki.choose_spec.2
    · have hsmall : r k < δ/4 := by
        have hn : ¬ δ/4 ≤ r k := by simpa only [B,Set.Finite.mem_toFinset,mem_ofPred_eq] using hkB
        exact lt_of_not_ge hn
      have hdij := (disjoint_closedBall_closedBall_iff
        (add_nonneg (hr i) hδ.le) (add_nonneg (hr j) hδ.le)).mp
        (hpair (show (⟨i,hi⟩ : F) ≠ ⟨j,hj⟩ from fun he => hij (congrArg Subtype.val he)))
      have hdi := dist_centers_le_of_closedBall_inter hki
      have hdj := dist_centers_le_of_closedBall_inter hkj
      have htri := dist_triangle (c i) (c k) (c j)
      rw [dist_comm (c i) (c k)] at htri
      linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ActualFiniteFluxLimit
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the finite enlargements proves the manuscript's precise
finite-hole flux inequality for the actual selected correspondence. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem actual_finite_flux_of_trace [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {R W : ℝ} (hR : 0 < R) (hRW : R < W)
    (htrace : ∀ i : Fin 2, ∀ᵐ y ∂volume, volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) i) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0)
    (hρ : IntegrableOn (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
      ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 W) volume)
    (hcontain : ∀ j, closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ ball 0 R)
    (F : Finset D.IndexedMatchedPair) :
    quadrantFlux (D.selectedPlane hG.1 hf) 0 R ≤
      2*(∫ z in {z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R,
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)+
      2*Real.pi*(∑ j ∈ F, E.sourceRadius j*E.targetRadius j)+
      16*∑' j : {j : D.IndexedMatchedPair // j ∉ F}, E.sourceRadius j*E.targetRadius j := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ₁,hδ₁,hsep⟩ := exists_finite_tail_disk_separation E.sourceCenter E.sourceRadius
    E.source_nonneg E.source_disjoint E.source_summable F
  obtain ⟨δ₂,hδ₂,hbox⟩ := exists_common_round_hole_offset
    (fun j : F => E.sourceCenter j) (fun j => E.sourceRadius j) (fun j => E.source_nonneg j)
    (fun j k hjk => E.source_disjoint (fun he => hjk (Subtype.ext he))) isOpen_ball
    (fun j => hcontain j)
  obtain ⟨δ₃,hδ₃,hinner⟩ := D.finite_inner_quadrantFlux_limiting_bound E hG.1 hf F hε
  let η := min δ₁ (min δ₂ δ₃)
  have hη : 0 < η := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hη₁ : η ≤ δ₁ := min_le_left _ _
  have hη₂ : η ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hη₃ : η ≤ δ₃ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hd,hone⟩ := hsep η ⟨hη,hη₁⟩
  have hin (j : D.IndexedMatchedPair) (hj : j ∈ F) := (hbox η ⟨hη,hη₂⟩).1 ⟨j,hj⟩
  have h := D.actual_finite_circle_flux E hG hinf hf hfix hH hinf' hR hRW htrace hρ F hη hd hin hone
  rw [integral_inter_closedBall_eq_ball] at h
  have hi := hinner η ⟨hη,hη₃⟩
  linarith

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_FluxLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Passing finite-hole flux estimates to the limit

The rigidity manuscript's finite-hole estimate bounds the flux with an
error of sixteen times the remaining mixed-radius sum. Square-summability
of the source and target radii makes this error tend to zero along arbitrary
finite subsets of the index type, giving `eq:limiting-flux`.
-/

open Filter
open scoped Topology

namespace CircleDomainRigidity

/-- The mixed-radius tail vanishes as the retained finite family exhausts
the holes. The hypotheses ensure that the total mixed-radius sum is the
actual convergent series. -/
theorem tendsto_mixed_radius_tail {ι : Type*} {r s : ι → ℝ}
    (hr : Summable (fun j => r j ^ 2)) (hs : Summable (fun j => s j ^ 2)) :
    Tendsto (fun F : Finset ι => ∑' j : {j // j ∉ F}, r j * s j)
      atTop (𝓝 0) := by
  have hsum := LengthArea.summable_mul_of_squares hr hs
  have hpartial : Tendsto (fun F : Finset ι => ∑ j ∈ F, r j * s j)
      atTop (𝓝 (∑' j, r j * s j)) := hsum.hasSum
  have htail : Tendsto
      (fun F : Finset ι => (∑' j, r j * s j) - ∑ j ∈ F, r j * s j)
      atTop (𝓝 ((∑' j, r j * s j) - ∑' j, r j * s j)) :=
    tendsto_const_nhds.sub hpartial
  convert htail using 1
  · funext F
    have hsplit := hsum.sum_add_tsum_subtype_compl F
    linarith
  · simp

/-- A uniform finite-hole flux estimate gives the limiting flux bound.
The coefficient `16` is the two-direction multiplicity bound appearing
immediately before `eq:limiting-flux` in the rigidity manuscript. -/
theorem limiting_flux_of_finite_hole_estimates {ι : Type*} {r s : ι → ℝ}
    {A I : ℝ} (hr : Summable (fun j => r j ^ 2))
    (hs : Summable (fun j => s j ^ 2))
    (hfinite : ∀ F : Finset ι, 2 * A ≤ 2 * I +
      2 * Real.pi * (∑ j ∈ F, r j * s j) +
      16 * (∑' j : {j // j ∉ F}, r j * s j)) :
    2 * A ≤ 2 * I + 2 * Real.pi * (∑' j, r j * s j) := by
  have hsum := LengthArea.summable_mul_of_squares hr hs
  have hpartial : Tendsto (fun F : Finset ι => ∑ j ∈ F, r j * s j)
      atTop (𝓝 (∑' j, r j * s j)) := hsum.hasSum
  have htail := tendsto_mixed_radius_tail hr hs
  have hlimit : Tendsto
      (fun F : Finset ι => 2 * I + 2 * Real.pi * (∑ j ∈ F, r j * s j) +
        16 * (∑' j : {j // j ∉ F}, r j * s j)) atTop
      (𝓝 (2 * I + 2 * Real.pi * (∑' j, r j * s j) + 16 * 0)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hpartial)).add
      (tendsto_const_nhds.mul htail)
  have hle := ge_of_tendsto hlimit (Filter.Eventually.of_forall hfinite)
  simpa using hle

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_GeometricRigidity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rigidity reduction with geometric source-area control

Source area and square-summability of the source radii follow from the
geometry of disjoint source disks. The target area follows from an exterior-area
bound. Together with the finite-hole flux estimate, these bounds force rigidity
through the length-area argument.
-/

open MeasureTheory Set Metric Filter Bornology Function
open scoped Topology

namespace CircleDomainRigidity

/-- A principal-normalized conformal map is the identity once the target
area and flux estimates are established. Source area and square-summable
source radii follow from disjoint disk geometry. -/
theorem identity_of_disk_geometry_and_target_flux {ι : Type*} [Countable ι]
    {f : ℂ → ℂ} {D : Set ℂ} (centers : ι → ℂ) (r s : ι → ℝ) (R : ℝ)
    (hD : IsOpen D) (hconn : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hDinf : IsBounded Dᶜ)
    (hnorm : Tendsto (fun z : ℂ => f z - z) (cobounded ℂ) (𝓝 0))
    (hR : 0 ≤ R) (hr : ∀ j, 0 ≤ r j)
    (hWne : (D ∩ ball 0 R).Nonempty)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (r j)))
    (hdisj : ∀ j, Disjoint D (ball (centers j) (r j)))
    (hcontain : ∀ j, ball (centers j) (r j) ⊆ ball 0 R)
    (hi : Integrable (fun z => ‖deriv f z‖) (volume.restrict (D ∩ ball 0 R)))
    (hi2 : Integrable (fun z => ‖deriv f z‖ ^ 2) (volume.restrict (D ∩ ball 0 R)))
    (hs : Summable (fun j => s j ^ 2))
    (htarget : (∫ z in D ∩ ball 0 R, ‖deriv f z‖ ^ 2) +
      Real.pi * (∑' j, s j ^ 2) ≤ Real.pi * R ^ 2)
    (hflux : 2 * (Real.pi * R ^ 2) ≤
      2 * (∫ z in D ∩ ball 0 R, ‖deriv f z‖) +
      2 * Real.pi * (∑' j, r j * s j)) :
    (∀ z ∈ D, f z = z) ∧ (∀ j, r j = s j) := by
  have hrSum : Summable (fun j => r j ^ 2) :=
    summable_radii_sq centers r R hr hpair hcontain
  have hsourceReal : (volume (D ∩ ball 0 R)).toReal +
      Real.pi * (∑' j, r j ^ 2) ≤ Real.pi * R ^ 2 :=
    sourceArea_real_le centers r R hr hR hpair
      (fun j => (hdisj j).mono_left inter_subset_left)
      inter_subset_right hcontain
  have hsource : (∫ _ in D ∩ ball 0 R, (1 : ℝ)) +
      Real.pi * (∑' j, r j ^ 2) ≤ Real.pi * R ^ 2 := by
    simpa [measureReal_def] using hsourceReal
  exact LengthArea.identity_of_length_area_estimates hD hconn hf hDinf hnorm
    (hD.inter isOpen_ball) hWne (isBounded_ball.subset inter_subset_right)
    inter_subset_left hi hi2 hrSum hs hsource htarget hflux

/-- All area and integrability premises follow from geometric disjointness
and the exterior omitted-area bound, under the limiting-flux inequality. -/
theorem identity_of_disk_geometry_exterior_area_and_flux
    {ι : Type*} [Countable ι] {f : ℂ → ℂ} {D : Set ℂ}
    (sourceCenters targetCenters : ι → ℂ) (r s : ι → ℝ) (R : ℝ)
    (hD : IsOpen D) (hconn : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hinj : InjOn f D)
    (hExterior : (closedBall (0 : ℂ) R)ᶜ ⊆ D)
    (hnorm : Tendsto (fun z : ℂ => f z - z) (cobounded ℂ) (𝓝 0))
    (hR : 0 ≤ R) (hr : ∀ j, 0 ≤ r j) (hs : ∀ j, 0 ≤ s j)
    (hWne : (D ∩ ball 0 R).Nonempty)
    (hSourcePair : Pairwise (Disjoint on fun j => ball (sourceCenters j) (r j)))
    (hSourceDisj : ∀ j, Disjoint D (ball (sourceCenters j) (r j)))
    (hSourceContain : ∀ j, ball (sourceCenters j) (r j) ⊆ ball 0 R)
    (hTargetPair : Pairwise (Disjoint on fun j => ball (targetCenters j) (s j)))
    (hTargetDisj : ∀ j, Disjoint (f '' D) (ball (targetCenters j) (s j)))
    (harea : ExteriorOmittedAreaBound f R)
    (hflux : 2 * (Real.pi * R ^ 2) ≤
      2 * (∫ z in D ∩ ball 0 R, ‖deriv f z‖) +
      2 * Real.pi * (∑' j, r j * s j)) :
    (∀ z ∈ D, f z = z) ∧ (∀ j, r j = s j) := by
  obtain ⟨hsSum, hi2, htarget⟩ := targetArea_of_exterior_area_bound
    targetCenters s R hD hf hinj hExterior hs hTargetPair hTargetDisj harea
  have hbounded : IsBounded (D ∩ ball (0 : ℂ) R) :=
    isBounded_ball.subset inter_subset_right
  have hi := integrable_norm_deriv_of_sq hD hf
    (hD.inter isOpen_ball).measurableSet hbounded inter_subset_left hi2
  have hDinf : IsBounded Dᶜ :=
    isBounded_closedBall.subset (compl_subset_comm.mp hExterior)
  exact identity_of_disk_geometry_and_target_flux sourceCenters r s R hD hconn hf
    hDinf hnorm hR hr hWne hSourcePair hSourceDisj hSourceContain
    hi hi2 hsSum htarget hflux

/-- The finite-hole flux estimates suffice for normalized rigidity. Source
and target geometry imply the required square-summability, so the remaining
tail tends to zero without any separate convergence assumption. -/
theorem identity_of_disk_geometry_exterior_area_and_finite_flux
    {ι : Type*} [Countable ι] {f : ℂ → ℂ} {D : Set ℂ}
    (sourceCenters targetCenters : ι → ℂ) (r s : ι → ℝ) (R : ℝ)
    (hD : IsOpen D) (hconn : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hinj : InjOn f D)
    (hExterior : (closedBall (0 : ℂ) R)ᶜ ⊆ D)
    (hnorm : Tendsto (fun z : ℂ => f z - z) (cobounded ℂ) (𝓝 0))
    (hR : 0 ≤ R) (hr : ∀ j, 0 ≤ r j) (hs : ∀ j, 0 ≤ s j)
    (hWne : (D ∩ ball 0 R).Nonempty)
    (hSourcePair : Pairwise (Disjoint on fun j => ball (sourceCenters j) (r j)))
    (hSourceDisj : ∀ j, Disjoint D (ball (sourceCenters j) (r j)))
    (hSourceContain : ∀ j, ball (sourceCenters j) (r j) ⊆ ball 0 R)
    (hTargetPair : Pairwise (Disjoint on fun j => ball (targetCenters j) (s j)))
    (hTargetDisj : ∀ j, Disjoint (f '' D) (ball (targetCenters j) (s j)))
    (harea : ExteriorOmittedAreaBound f R)
    (hfinite : ∀ F : Finset ι, 2 * (Real.pi * R ^ 2) ≤
      2 * (∫ z in D ∩ ball 0 R, ‖deriv f z‖) +
      2 * Real.pi * (∑ j ∈ F, r j * s j) +
      16 * (∑' j : {j // j ∉ F}, r j * s j)) :
    (∀ z ∈ D, f z = z) ∧ (∀ j, r j = s j) := by
  have hrSum := summable_radii_sq sourceCenters r R hr hSourcePair hSourceContain
  have hsSum := (targetArea_of_exterior_area_bound
    targetCenters s R hD hf hinj hExterior hs hTargetPair hTargetDisj harea).1
  have hflux := limiting_flux_of_finite_hole_estimates hrSum hsSum hfinite
  exact identity_of_disk_geometry_exterior_area_and_flux
    sourceCenters targetCenters r s R hD hconn hf hinj hExterior hnorm hR hr hs
    hWne hSourcePair hSourceDisj hSourceContain hTargetPair hTargetDisj harea hflux

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ActualLocalIntegrability
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local derivative integrability follows from the actual bounded image
of each compact source disk. No boundary area or integrability premise is
needed for the finite-hole estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)
include D

 theorem finite_part_differentiableOn (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty) :
    DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f (z : Sphere))) {z | (z : Sphere) ∈ G} := by
  intro z hz
  exact (analyticAt_finite_map_of_conformal hG hf.1 hz
    (D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hz))).differentiableAt.differentiableWithinAt

 theorem selectedPlane_eq_finite_part (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {z : ℂ} (hz : (z : Sphere) ∈ G) :
    D.selectedPlane hG hf z = finiteCoord (f (z : Sphere)) :=
  congrArg finiteCoord (D.componentRelation_on_domain hz (D.selectedTarget_mem hG hf _))

 theorem finite_part_injOn (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty) :
    InjOn (fun z : ℂ => finiteCoord (f (z : Sphere))) {z | (z : Sphere) ∈ G} := by
  intro x hx y hy hxy
  have hfx := D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hx)
  have hfy := D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hy)
  apply OnePoint.coe_injective
  apply hf.bijOn.injOn hx hy
  exact (CannonMobius.coe_coordinate hfx).symm.trans
    ((congrArg ((↑) : ℂ → Sphere) hxy).trans (CannonMobius.coe_coordinate hfy))

 theorem actual_local_derivative_integrable (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty) (R : ℝ) :
    IntegrableOn (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
      ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R) volume := by
  let U : Set ℂ := {z | (z : Sphere) ∈ G}
  have hU : IsOpen U := hG.preimage OnePoint.continuous_coe
  have hd := D.finite_part_differentiableOn hG hinf hf hfix
  obtain ⟨B,hB,hbound⟩ := D.selectedPlane_bounded_on_compact hG hinf hf hfix
    (isCompact_closedBall (0 : ℂ) R)
  have himage : (fun z : ℂ => finiteCoord (f (z : Sphere))) '' (U ∩ ball 0 R) ⊆ ball 0 B := by
    rintro w ⟨z,hz,rfl⟩
    rw [mem_ball,dist_zero_right]
    dsimp only
    rw [← D.selectedPlane_eq_finite_part hG hf hz.1]
    exact hbound z (ball_subset_closedBall hz.2)
  have hsq := integrable_norm_deriv_sq_of_image_area_finite (hU.inter isOpen_ball).measurableSet
    (fun z hz => (hd z hz.1).differentiableAt (hU.mem_nhds hz.1))
    ((D.finite_part_injOn hG hinf hf hfix).mono inter_subset_left)
    (ne_of_lt ((measure_mono himage).trans_lt measure_ball_lt_top))
  exact integrable_norm_deriv_of_sq hU hd (hU.inter isOpen_ball).measurableSet
    (isBounded_ball.subset inter_subset_right) inter_subset_left hsq

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedDiskDomainGeometry
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual matched disks are disjoint from the source and target
plane domains. All complementary points lie in one bounded disk. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem MatchedRoundDisks.source_disjoint_domain (E : D.MatchedRoundDisks) (j : D.IndexedMatchedPair) :
    Disjoint {z : ℂ | (z : Sphere) ∈ G} (ball (E.sourceCenter j) (E.sourceRadius j)) := by
  apply disjoint_left.mpr
  intro z hz hzb
  have hm : (z : Sphere) ∈ j.val.1 := by rw [E.source_eq j]; exact mem_image_of_mem _ (ball_subset_closedBall hzb)
  rw [j.property.1.1.eq_component_of_mem hm] at hm
  exact (connectedComponentIn_subset _ _ hm) hz

 theorem MatchedRoundDisks.target_disjoint_image (E : D.MatchedRoundDisks)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (j : D.IndexedMatchedPair) :
    Disjoint ((fun z : ℂ => finiteCoord (f (z : Sphere))) '' {z : ℂ | (z : Sphere) ∈ G})
      (ball (E.targetCenter j) (E.targetRadius j)) := by
  apply disjoint_left.mpr
  rintro w ⟨z,hz,rfl⟩ hw
  have hfinite := D.planeRelation_ne_infty hG hinf hf hfix (D.componentRelation_graph hf hz)
  have hm : (finiteCoord (f (z : Sphere)) : Sphere) ∈ j.val.2 := by
    rw [E.target_eq j]
    exact mem_image_of_mem _ (ball_subset_closedBall hw)
  have he : (finiteCoord (f (z : Sphere)) : Sphere) = f (z : Sphere) :=
    CannonMobius.coe_coordinate hfinite
  rw [he] at hm
  rw [j.property.1.2.1.eq_component_of_mem hm] at hm
  exact (connectedComponentIn_subset _ _ hm) (mem_image_of_mem f hz)

 theorem finite_domain_exterior_radius (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) :
    ∃ R > 0, ∀ z : ℂ, (z : Sphere) ∉ G → ‖z‖ < R := by
  exact ((OnePoint.isOpen_iff_of_mem hinf).mp hG).2.isBounded.exists_pos_norm_lt

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuarterCircleAverage
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reassembling the four geometric quarter circles into the usual
circle average. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem quadrantPoint_true_true (r θ : ℝ) :
    quadrantPoint 0 r true true θ = circleMap 0 r θ := by
  apply Complex.ext <;> simp [quadrantPoint,quadrantNormal,quadrantSign,circleMap_zero_re,circleMap_zero_im]

 theorem quadrantPoint_false_true (r θ : ℝ) :
    quadrantPoint 0 r false true θ = circleMap 0 r (Real.pi-θ) := by
  apply Complex.ext <;> simp [quadrantPoint,quadrantNormal,quadrantSign,circleMap_zero_re,circleMap_zero_im]

 theorem quadrantPoint_false_false (r θ : ℝ) :
    quadrantPoint 0 r false false θ = circleMap 0 r (Real.pi+θ) := by
  apply Complex.ext <;> simp [quadrantPoint,quadrantNormal,quadrantSign,circleMap_zero_re,circleMap_zero_im,
    Real.cos_add,Real.sin_add]

 theorem quadrantPoint_true_false (r θ : ℝ) :
    quadrantPoint 0 r true false θ = circleMap 0 r (2*Real.pi-θ) := by
  apply Complex.ext <;> simp [quadrantPoint,quadrantNormal,quadrantSign,circleMap_zero_re,circleMap_zero_im,
    Real.cos_two_pi_sub,Real.sin_two_pi_sub]

 theorem integral_four_quadrants {H : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hH : ContinuousOn H (closedBall 0 r)) :
    (∫ θ in (0 : ℝ)..(Real.pi/2), ∑ s : Bool, ∑ t : Bool, H (quadrantPoint 0 r s t θ)) =
      ∫ θ in (0 : ℝ)..(2*Real.pi), H (circleMap 0 r θ) := by
  let f := fun θ => H (circleMap 0 r θ)
  have hf : Continuous f := hH.comp_continuous (continuous_circleMap 0 r) (by
    intro θ
    simp only [mem_closedBall,dist_zero_right,norm_circleMap_zero,abs_of_nonneg hr,le_refl])
  have e (θ : ℝ) : (∑ s : Bool, ∑ t : Bool, H (quadrantPoint 0 r s t θ)) =
      f θ+f (Real.pi-θ)+f (Real.pi+θ)+f (2*Real.pi-θ) := by
    simp only [Fintype.sum_bool,quadrantPoint_false_false,quadrantPoint_false_true,
      quadrantPoint_true_false,quadrantPoint_true_true]
    dsimp only [f]
    abel
  have h1 : IntervalIntegrable f volume 0 (Real.pi/2) := hf.intervalIntegrable (0 : ℝ) (Real.pi/2)
  have h2 : IntervalIntegrable (fun θ => f (Real.pi-θ)) volume 0 (Real.pi/2) := (hf.comp (continuous_const.sub continuous_id)).intervalIntegrable (0 : ℝ) (Real.pi/2)
  have h3 : IntervalIntegrable (fun θ => f (Real.pi+θ)) volume 0 (Real.pi/2) := (hf.comp (continuous_const.add continuous_id)).intervalIntegrable (0 : ℝ) (Real.pi/2)
  have h4 : IntervalIntegrable (fun θ => f (2*Real.pi-θ)) volume 0 (Real.pi/2) := (hf.comp (continuous_const.sub continuous_id)).intervalIntegrable (0 : ℝ) (Real.pi/2)
  have e2 : (∫ θ in (0 : ℝ)..(Real.pi/2), f (Real.pi-θ)) =
      ∫ θ in (Real.pi/2)..Real.pi, f θ := by
    rw [intervalIntegral.integral_comp_sub_left]
    congr 1 <;> ring
  have e3 : (∫ θ in (0 : ℝ)..(Real.pi/2), f (Real.pi+θ)) =
      ∫ θ in Real.pi..(3*Real.pi/2), f θ := by
    rw [intervalIntegral.integral_comp_add_left]
    congr 1 <;> ring
  have e4 : (∫ θ in (0 : ℝ)..(Real.pi/2), f (2*Real.pi-θ)) =
      ∫ θ in (3*Real.pi/2)..(2*Real.pi), f θ := by
    rw [intervalIntegral.integral_comp_sub_left]
    congr 1 <;> ring
  simp_rw [e]
  rw [intervalIntegral.integral_add ((h1.add h2).add h3) h4,
    intervalIntegral.integral_add (h1.add h2) h3,intervalIntegral.integral_add h1 h2,e2,e3,e4,
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalQuadrantGeometry
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inversion sends each quarter circle to the opposite vertical quarter.
The principal flux density is the mean of its analytic inverse germ. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem star_quadrantNormal (s t : Bool) (θ : ℝ) :
    star (quadrantNormal s t θ) = quadrantNormal s (!t) θ := by
  cases t <;> apply Complex.ext <;> simp [quadrantNormal,quadrantSign]

 theorem inverse_quadrantPoint (r : ℝ) (s t : Bool) (θ : ℝ) :
    (quadrantPoint 0 r s t θ)⁻¹ = quadrantPoint 0 r⁻¹ s (!t) θ := by
  simp only [quadrantPoint,zero_add,mul_inv_rev,Complex.inv_eq_conj (quadrantNormal_norm s t θ),
    ← Complex.ofReal_inv]
  rw [show starRingEnd ℂ (quadrantNormal s t θ) = star (quadrantNormal s t θ) from rfl,
    star_quadrantNormal,mul_comm]

 theorem principal_quadrant_density {F H : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (he : ∀ z : ℂ, z ≠ 0 → H z⁻¹ = z⁻¹*F z) (θ : ℝ) :
    r*(∑ s : Bool, ∑ t : Bool,
      (F (quadrantPoint 0 r s t θ)*star (quadrantNormal s t θ)).re) =
      r^2*(∑ s : Bool, ∑ t : Bool, H (quadrantPoint 0 r⁻¹ s t θ)).re := by
  have hpoint (s t : Bool) :
      F (quadrantPoint 0 r s t θ)*star (quadrantNormal s t θ) =
        (r : ℂ)*H (quadrantPoint 0 r⁻¹ s (!t) θ) := by
    have hn : quadrantPoint 0 r s t θ ≠ 0 := by
      intro h
      have hh := quadrantPoint_dist 0 r s t θ
      rw [h,dist_self,abs_of_pos hr] at hh
      exact hr.ne' hh.symm
    rw [← inverse_quadrantPoint,he _ hn]
    simp only [quadrantPoint,zero_add,mul_inv_rev,
      Complex.inv_eq_conj (quadrantNormal_norm s t θ)]
    rw [← Complex.ofReal_inv]
    change F ((r : ℂ)*quadrantNormal s t θ)*star (quadrantNormal s t θ) =
      (r : ℂ)*(star (quadrantNormal s t θ)*(r⁻¹ : ℝ)*F ((r : ℂ)*quadrantNormal s t θ))
    rw [Complex.ofReal_inv]
    field_simp [show (r : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hr.ne']
  simp_rw [hpoint]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    ← Finset.mul_sum]
  simp only [Fintype.sum_bool,Bool.not_false,Bool.not_true,Complex.add_re]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrincipalQuadrantMean
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic inverse mean equals one, so the principal outer flux is
exactly the area factor. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principal_quadrantFlux_of_inverse_mean {F H : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hH : ContinuousOn H (closedBall 0 r⁻¹))
    (hmean : Real.circleAverage H 0 r⁻¹ = 1)
    (he : ∀ z : ℂ, z ≠ 0 → H z⁻¹ = z⁻¹*F z) :
    quadrantFlux F 0 r = 2*Real.pi*r^2 := by
  have hQ (s t : Bool) : Continuous (fun θ => H (quadrantPoint 0 r⁻¹ s t θ)) := by
    apply hH.comp_continuous
    · change Continuous (fun θ => (0 : ℂ)+(r⁻¹ : ℝ)*Complex.equivRealProdCLM.symm
        (quadrantSign s*Real.cos θ,quadrantSign t*Real.sin θ))
      fun_prop
    · intro θ
      rw [mem_closedBall,quadrantPoint_dist,abs_of_pos (inv_pos.mpr hr)]
  have hi : IntervalIntegrable (fun θ => ∑ s : Bool, ∑ t : Bool,
      H (quadrantPoint 0 r⁻¹ s t θ)) volume 0 (Real.pi/2) :=
    (continuous_finsetSum _ (fun s _ => continuous_finsetSum _ (fun t _ => hQ s t))).intervalIntegrable _ _
  have hRe := Complex.reCLM.intervalIntegral_comp_comm hi
  have hmeanR := congrArg Complex.re hmean
  simp only [Real.circleAverage_def,Complex.smul_re,smul_eq_mul,Complex.one_re] at hmeanR
  have hπ : (2 : ℝ)*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hval : (∫ θ in (0 : ℝ)..(2*Real.pi), H (circleMap 0 r⁻¹ θ)).re = 2*Real.pi := by
    apply mul_left_cancel₀ (inv_ne_zero hπ)
    simpa only [inv_mul_cancel₀ hπ] using hmeanR
  calc
    quadrantFlux F 0 r = r^2*(∫ θ in (0 : ℝ)..(Real.pi/2),
        (∑ s : Bool, ∑ t : Bool, H (quadrantPoint 0 r⁻¹ s t θ)).re) := by
      unfold quadrantFlux
      simp_rw [principal_quadrant_density hr he]
      rw [intervalIntegral.integral_const_mul]
    _ = r^2*(∫ θ in (0 : ℝ)..(Real.pi/2),
        ∑ s : Bool, ∑ t : Bool, H (quadrantPoint 0 r⁻¹ s t θ)).re := by
      exact congrArg (fun x : ℝ => r^2*x) hRe
    _ = r^2*(∫ θ in (0 : ℝ)..(2*Real.pi), H (circleMap 0 r⁻¹ θ)).re := by
      rw [integral_four_quadrants (inv_nonneg.mpr hr.le) hH]
    _ = 2*Real.pi*r^2 := by rw [hval]; ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalOuterFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual principal inverse germ gives the exact outer-circle flux
for every sufficiently large radius. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principalInverseMean_eq {F : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) :
    principalInverseMean F z⁻¹ = z⁻¹*F z := by
  simp only [principalInverseMean,invertedPrincipalRemainder,
    Function.update_of_ne (inv_ne_zero hz),inv_inv]
  field_simp
  ring

 theorem eventually_principal_quadrantFlux {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (hnorm : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) :
    ∃ R₀ > 0, ∀ R ≥ R₀, quadrantFlux F 0 R = 2*Real.pi*R^2 := by
  have hH : AnalyticAt ℂ (principalInverseMean F) 0 :=
    analyticAt_const.add (analyticAt_id.mul (invertedPrincipalRemainder_analytic hF hnorm))
  obtain ⟨δ,hδ,hδH⟩ := hH.exists_ball_analyticOnNhd
  refine ⟨max 1 (δ⁻¹+1),lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro R hR
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  have hRδ : δ⁻¹ < R := by have := (le_max_right 1 (δ⁻¹+1)).trans hR; linarith
  have hinv : R⁻¹ < δ := (inv_lt_comm₀ hRp hδ).mpr hRδ
  have hA : AnalyticOnNhd ℂ (principalInverseMean F) (closedBall 0 R⁻¹) :=
    hδH.mono (closedBall_subset_ball hinv)
  have hc := hA.continuousOn
  have hd : DiffContOnCl ℂ (principalInverseMean F) (ball 0 |R⁻¹|) := by
    rw [abs_of_pos (inv_pos.mpr hRp)]
    exact DiffContOnCl.mk_ball (hA.differentiableOn.mono ball_subset_closedBall) hc
  have hm : Real.circleAverage (principalInverseMean F) 0 R⁻¹ = 1 := by
    simpa only [principalInverseMean,zero_mul,add_zero] using hd.circleAverage
  exact principal_quadrantFlux_of_inverse_mean hRp hc hm (fun _ hz => principalInverseMean_eq hz)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MatchedPrincipalFlux
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the principal outer flux to the actual selected field on
large circles wholly contained in the source domain. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem selected_principal_quadrantFlux (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hnorm : IsPrincipalNormalized f) :
    ∃ R₀ > 0, ∀ R ≥ R₀, quadrantFlux (D.selectedPlane hG hf) 0 R = 2*Real.pi*R^2 := by
  obtain ⟨A,hA,hbound⟩ := finite_domain_exterior_radius hG hinf
  have hmem : ∀ᶠ (z : ℂ) in cobounded ℂ, (z : Sphere) ∈ G := by
    have hm := OnePoint.tendsto_coe_infty (hG.mem_nhds hinf)
    change {z : ℂ | (z : Sphere) ∈ G} ∈ cobounded ℂ
    rw [Metric.cobounded_eq_cocompact]
    rw [coclosedCompact_eq_cocompact] at hm
    exact hm
  have hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ (fun z : ℂ => finiteCoord (f (z : Sphere))) z := by
    filter_upwards [hmem] with z hz
    exact (analyticAt_finite_map_of_conformal hG hf.1 hz
      (D.planeRelation_ne_infty hG hinf hf hnorm.1 (D.componentRelation_graph hf hz))).differentiableAt
  obtain ⟨B,hB,hflux⟩ := eventually_principal_quadrantFlux hd (principal_remainder_tendsto_zero hnorm.2)
  refine ⟨max B (A+1),lt_of_lt_of_le hB (le_max_left _ _),?_⟩
  intro R hR
  have hRA : A < R := by have := (le_max_right B (A+1)).trans hR; linarith
  have hRp : 0 < R := hA.trans hRA
  have hepoint (s t : Bool) (θ : ℝ) :
      D.selectedPlane hG hf (quadrantPoint 0 R s t θ) =
        finiteCoord (f (quadrantPoint 0 R s t θ : Sphere)) := by
    apply D.selectedPlane_eq_finite_part hG hf
    by_contra hz
    have hn := quadrantPoint_dist 0 R s t θ
    rw [dist_zero_right,abs_of_pos hRp] at hn
    have hb := hbound _ hz
    rw [hn] at hb
    exact (not_lt_of_ge hRA.le) hb
  have he : quadrantFlux (D.selectedPlane hG hf) 0 R =
      quadrantFlux (fun z : ℂ => finiteCoord (f (z : Sphere))) 0 R := by
    unfold quadrantFlux
    simp_rw [hepoint]
  exact he.trans (hflux R ((le_max_left _ _).trans hR))

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_NormalizedRigidityFromTrace
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite flux and the published exterior area theorem force
a principally normalized map to be the identity. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem normalized_identity_of_trace_oai [Countable D.IndexedMatchedPair]
    (harea : ExteriorOmittedAreaTheorem) (E : D.MatchedRoundDisks)
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hnorm : IsPrincipalNormalized f)
    (hH : IsCircleDomain (f '' G))
    (htrace : ∀ i : Fin 2, ∀ᵐ y ∂volume, volume ((fun x => (complexPlaneCoordinates.symm
      (D.selectedPlane hG.1 hf (complexCoordinateLine i y x))) i) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0) :
    ∀ p ∈ G, f p = p := by
  classical
  let U : Set ℂ := {z | (z : Sphere) ∈ G}
  let F : ℂ → ℂ := fun z => finiteCoord (f (z : Sphere))
  have hU : IsOpen U := hG.1.preimage OnePoint.continuous_coe
  obtain ⟨hUc,hUb⟩ := finite_part_connected_unbounded hG.2.1.isPreconnected
    (mem_interior_iff_mem_nhds.mpr (hG.1.mem_nhds hinf))
  have hUne : U.Nonempty := by
    by_contra h
    have he : U = ∅ := not_nonempty_iff_eq_empty.mp h
    apply hUb
    change IsBounded U
    rw [he]
    exact isBounded_empty
  obtain ⟨z₀,hz₀⟩ := hUne
  obtain ⟨A,hA,hAbound⟩ := finite_domain_exterior_radius hG.1 hinf
  obtain ⟨B,_,hBflux⟩ := D.selected_principal_quadrantFlux hG.1 hinf hf hnorm
  let R := max A (max B (‖z₀‖+1))
  have hAR : A ≤ R := le_max_left _ _
  have hBR : B ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hzR : ‖z₀‖ < R := by
    have h := (le_max_right B (‖z₀‖+1)).trans (le_max_right A (max B (‖z₀‖+1)))
    linarith
  have hR : 0 < R := hA.trans_le hAR
  have hExt : (closedBall (0 : ℂ) R)ᶜ ⊆ U := by
    intro z hz
    by_contra hg
    have hb := hAbound z hg
    have hz' : R < ‖z‖ := by simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hz
    linarith
  have hcontain (j : D.IndexedMatchedPair) : closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ ball 0 R := by
    intro z hz
    have hm : (z : Sphere) ∈ j.val.1 := by rw [E.source_eq j]; exact mem_image_of_mem _ hz
    rw [j.property.1.1.eq_component_of_mem hm] at hm
    have hb := hAbound z (connectedComponentIn_subset _ _ hm)
    rw [mem_ball,dist_zero_right]
    exact hb.trans_le hAR
  have hd := D.finite_part_differentiableOn hG.1 hinf hf hnorm.1
  have hi := D.finite_part_injOn hG.1 hinf hf hnorm.1
  have hareaR := harea F R hR (hd.mono hExt) (hi.mono hExt) hnorm.2
  have hinf' : OnePoint.infty ∈ f '' G := hnorm.1 ▸ mem_image_of_mem f hinf
  obtain ⟨hid,_⟩ := identity_of_disk_geometry_exterior_area_and_finite_flux
    E.sourceCenter E.targetCenter E.sourceRadius E.targetRadius R hU hUc hd hi hExt
    (principal_remainder_tendsto_zero hnorm.2) hR.le E.source_nonneg E.target_nonneg
    ⟨z₀,hz₀,by simpa only [mem_ball,dist_zero_right] using hzR⟩
    (fun j k hjk => (E.source_disjoint hjk).mono ball_subset_closedBall ball_subset_closedBall)
    (fun j => MatchedRoundDisks.source_disjoint_domain D E j)
    (fun j => ball_subset_closedBall.trans (hcontain j))
    (fun j k hjk => (E.target_disjoint hjk).mono ball_subset_closedBall ball_subset_closedBall)
    (fun j => MatchedRoundDisks.target_disjoint_image D E hG.1 hinf hf hnorm.1 j) hareaR (by
      intro S
      have h := D.actual_finite_flux_of_trace E hG hinf hf hnorm.1 hH hinf' hR
        (show R < R+1 by linarith) htrace
        (D.actual_local_derivative_integrable hG.1 hinf hf hnorm.1 (R+1)) hcontain S
      rw [hBflux R hBR] at h
      nlinarith only [h])
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact hnorm.1
  | coe z =>
    have hfinite := D.planeRelation_ne_infty hG.1 hinf hf hnorm.1 (D.componentRelation_graph hf hp)
    exact (CannonMobius.coe_coordinate hfinite).symm.trans
      (congrArg ((↑) : ℂ → Sphere) (hid z hp))

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.MatchedConformalEnds.normalized_identity_of_trace_oai := @OAI.CircleDomainRigidity.MatchedConformalEnds.normalized_identity_of_trace_oai
