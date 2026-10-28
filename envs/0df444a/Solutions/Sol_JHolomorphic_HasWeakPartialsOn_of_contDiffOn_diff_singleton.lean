-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.of_contDiffOn_diff_singleton
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:00:48.230001+00:00
-- url     : https://prove2.me/submissions/ece231c0-fed9-42c1-80c3-821283d470bd

import Definitions.Def_JHolomorphic_Setting
import Mathlib

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal

namespace A3S48WP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {U : Set ℂ} {z₀ : ℂ} {u : ℂ → E} {φ : ℂ → ℝ}

/-- the product-rule integrand -/
noncomputable def G (φ : ℂ → ℝ) (u : ℂ → E) (v : ℂ) (z : ℂ) : E :=
  fderiv ℝ φ z v • u z + φ z • fderiv ℝ u z v

lemma open_diff (hU : IsOpen U) : IsOpen (U \ {z₀}) := hU.sdiff isClosed_singleton

lemma notU (hsupp : tsupport φ ⊆ U) {z : ℂ} (hz : z ∉ U) : z ∉ tsupport φ :=
  fun h => hz (hsupp h)

lemma G_zero {v z : ℂ} (hz : z ∉ tsupport φ) : G φ u v z = 0 := by
  simp [G, fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]

lemma eventually_zero_of_notMem {f : ℂ → E} {z : ℂ} (hz : z ∉ tsupport φ)
    (hf : ∀ y, y ∉ tsupport φ → f y = 0) : f =ᶠ[𝓝 z] 0 := by
  have : (tsupport φ)ᶜ ∈ 𝓝 z := (isClosed_tsupport φ).isOpen_compl.mem_nhds hz
  filter_upwards [this] with y hy using hf y hy

lemma contAt_of_U (hU : IsOpen U) (hsupp : tsupport φ ⊆ U) {f : ℂ → E}
    (hf0 : ∀ y, y ∉ tsupport φ → f y = 0) (hf : ∀ z ∈ U, ContinuousAt f z) (z : ℂ) :
    ContinuousAt f z := by
  by_cases hz : z ∈ U
  · exact hf z hz
  · exact (continuousAt_const (y := (0:E))).congr
      (eventually_zero_of_notMem (notU hsupp hz) hf0).symm

variable (hU : IsOpen U) (hc : ContinuousOn u U) (hu : ContDiffOn ℝ 1 u (U \ {z₀}))
  (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ U)
include hU hc hu hφ hφc hsupp

lemma F_cont : Continuous (fun z => φ z • u z) := by
  refine continuous_iff_continuousAt.2 (contAt_of_U hU hsupp ?_ ?_)
  · intro y hy; simp [image_eq_zero_of_notMem_tsupport hy]
  · intro z hz
    exact hφ.continuous.continuousAt.smul (hc.continuousAt (hU.mem_nhds hz))

lemma A_cont (v : ℂ) : Continuous (fun z => fderiv ℝ φ z v • u z) := by
  refine continuous_iff_continuousAt.2 (contAt_of_U hU hsupp ?_ ?_)
  · intro y hy; simp [fderiv_of_notMem_tsupport ℝ hy]
  · intro z hz
    exact ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousAt.smul
      (hc.continuousAt (hU.mem_nhds hz))

lemma G_contAt (v : ℂ) {z : ℂ} (hz : z ≠ z₀) : ContinuousAt (G φ u v) z := by
  by_cases hzU : z ∈ U
  · have hmem : U \ {z₀} ∈ 𝓝 z := (open_diff hU).mem_nhds ⟨hzU, hz⟩
    have h1 : ContinuousAt (fun z => fderiv ℝ u z) z :=
      ((hu.continuousOn_fderiv_of_isOpen (open_diff hU) le_rfl)).continuousAt hmem
    exact (A_cont hU hc hu hφ hφc hsupp v).continuousAt.add
      (hφ.continuous.continuousAt.smul (h1.clm_apply continuousAt_const))
  · exact (continuousAt_const (y := (0:E))).congr
      (eventually_zero_of_notMem (notU hsupp hzU) (fun y hy => G_zero hy)).symm

lemma hasDeriv_line (v w : ℂ) (s : ℝ) (hz : w + (s:ℂ) * v ≠ z₀) :
    HasDerivAt (fun s : ℝ => φ (w + (s:ℂ) * v) • u (w + (s:ℂ) * v))
      (G φ u v (w + (s:ℂ) * v)) s := by
  set z := w + (s:ℂ) * v
  have hL : HasDerivAt (fun s : ℝ => w + (s:ℂ) * v) v s := by
    have := ((hasDerivAt_id s).ofReal_comp.mul_const v).const_add w
    simpa using this
  by_cases hzU : z ∈ U
  · have hmem : U \ {z₀} ∈ 𝓝 z := (open_diff hU).mem_nhds ⟨hzU, hz⟩
    have hud : HasFDerivAt u (fderiv ℝ u z) z :=
      ((hu.differentiableOn one_ne_zero).differentiableAt hmem).hasFDerivAt
    have hφd : HasFDerivAt φ (fderiv ℝ φ z) z :=
      (hφ.differentiable one_ne_zero z).hasFDerivAt
    have := (hφd.smul hud).comp_hasDerivAt s hL
    convert this using 1
    · rfl
    · simp only [G, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      exact add_comm _ _
  · have h0 := eventually_zero_of_notMem (notU hsupp hzU)
      (f := fun y => φ y • u y) (fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy])
    rw [G_zero (notU hsupp hzU)]
    refine (hasDerivAt_const s (0:E)).congr_of_eventuallyEq ?_
    have := hL.continuousAt.eventually h0
    filter_upwards [this] with y hy using hy

lemma compact_preimage (v w : ℂ) (hv : v ≠ 0) :
    IsCompact ((fun s : ℝ => w + (s:ℂ) * v) ⁻¹' tsupport φ) := by
  have hcont : Continuous (fun s : ℝ => w + (s:ℂ) * v) := by fun_prop
  obtain ⟨R, hR⟩ := hφc.isBounded.subset_closedBall 0
  refine Metric.isCompact_of_isClosed_isBounded ((isClosed_tsupport φ).preimage hcont) ?_
  refine (Metric.isBounded_closedBall (x := (0:ℝ)) (r := (‖w‖ + R) / ‖v‖)).subset ?_
  intro s hs
  have := hR hs
  simp only [mem_closedBall, dist_zero_right] at this ⊢
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [le_div_iff₀ hv']
  have h1 : ‖(s:ℂ) * v‖ ≤ ‖w‖ + ‖w + (s:ℂ) * v‖ := by
    calc ‖(s:ℂ) * v‖ = ‖-w + (w + (s:ℂ) * v)‖ := by ring_nf
      _ ≤ ‖-w‖ + ‖w + (s:ℂ) * v‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  rw [norm_mul, Complex.norm_real] at h1
  linarith

lemma line_zero (v w : ℂ) (hv : v ≠ 0) (hline : ∀ s : ℝ, w + (s:ℂ) * v ≠ z₀) :
    ∫ s : ℝ, G φ u v (w + (s:ℂ) * v) = 0 := by
  have hK := compact_preimage hU hc hu hφ hφc hsupp v w hv
  have hcont : Continuous (fun s : ℝ => w + (s:ℂ) * v) := by fun_prop
  refine integral_eq_zero_of_hasDerivAt_of_integrable
    (fun s => hasDeriv_line hU hc hu hφ hφc hsupp v w s (hline s)) ?_ ?_
  · refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact continuous_iff_continuousAt.2 fun s =>
        ContinuousAt.comp (f := fun s : ℝ => w + (s:ℂ) * v) (x := s)
          (G_contAt hU hc hu hφ hφc hsupp v (hline s)) hcont.continuousAt
    · refine HasCompactSupport.intro hK fun s hs => G_zero hs
  · refine Continuous.integrable_of_hasCompactSupport
      ((F_cont hU hc hu hφ hφc hsupp).comp hcont) ?_
    refine HasCompactSupport.intro hK fun s hs => ?_
    simp [image_eq_zero_of_notMem_tsupport hs]

lemma main (v : ℂ) (hv : v = 1 ∨ v = Complex.I)
    (hint : Integrable (fun z => φ z • fderiv ℝ u z v)) :
    ∫ z, fderiv ℝ φ z v • u z = -∫ z, φ z • fderiv ℝ u z v := by
  have hA : Integrable (fun z => fderiv ℝ φ z v • u z) := by
    refine Continuous.integrable_of_hasCompactSupport (A_cont hU hc hu hφ hφc hsupp v) ?_
    refine HasCompactSupport.intro hφc fun z hz => ?_
    simp [fderiv_of_notMem_tsupport ℝ hz]
  have hGi : Integrable (G φ u v) := hA.add hint
  have hG0 : ∫ z, G φ u v z = 0 := by
    have hmp := (Complex.volume_preserving_equiv_real_prod).symm
    rw [← hmp.integral_comp' (g := G φ u v)]
    have hGp : Integrable (fun p : ℝ × ℝ => G φ u v (Complex.measurableEquivRealProd.symm p))
        (volume.prod volume) := by
      have := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hGi
      simpa [Measure.volume_eq_prod, Function.comp_def, Complex.measurableEquivRealProd_symm_apply] using this
    rw [Measure.volume_eq_prod]
    rcases hv with rfl | rfl
    · rw [integral_prod_symm _ hGp]
      have : ∀ᵐ y : ℝ, y ≠ z₀.im := by
        simp [ae_iff, measure_singleton]
      refine (integral_congr_ae ?_).trans (integral_zero ℝ E)
      filter_upwards [this] with y hy
      have := line_zero hU hc hu hφ hφc hsupp 1 ((y:ℂ) * Complex.I) one_ne_zero
        (fun s h => hy (by have := congrArg Complex.im h; simpa using this))
      refine Eq.trans (integral_congr_ae (Eventually.of_forall fun x => ?_)) this
      simp only; congr 1; apply Complex.ext <;> simp [Complex.measurableEquivRealProd_symm_apply]
    · rw [integral_prod _ hGp]
      have : ∀ᵐ x : ℝ, x ≠ z₀.re := by
        simp [ae_iff, measure_singleton]
      refine (integral_congr_ae ?_).trans (integral_zero ℝ E)
      filter_upwards [this] with x hx
      have := line_zero hU hc hu hφ hφc hsupp Complex.I (x:ℂ) Complex.I_ne_zero
        (fun s h => hx (by have := congrArg Complex.re h; simpa using this))
      refine Eq.trans (integral_congr_ae (Eventually.of_forall fun y => ?_)) this
      simp only; congr 1; apply Complex.ext <;> simp [Complex.measurableEquivRealProd_symm_apply]
  have : ∫ z, G φ u v z = (∫ z, fderiv ℝ φ z v • u z) + ∫ z, φ z • fderiv ℝ u z v :=
    integral_add hA hint
  rw [hG0] at this
  rw [eq_neg_iff_add_eq_zero]; exact this.symm

end A3S48WP

namespace A3S48WP

lemma memLp_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set ℂ} {u : ℂ → E} {p : ℝ} (hp : 1 ≤ p)
    (hint : ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ p) < ⊤) (v : ℂ) (hv : ‖v‖ = 1) :
    MemLp (fun z => fderiv ℝ u z v) (ENNReal.ofReal p) (volume.restrict U) := by
  borelize E
  refine ⟨(measurable_fderiv_apply_const ℝ u v).aestronglyMeasurable, ?_⟩
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (lt_of_le_of_lt ?_ hint).ne
  refine lintegral_mono fun z => ?_
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow (norm_nonneg _) _ (by linarith)
  simpa [hv] using (fderiv ℝ u z).le_opNorm v

end A3S48WP

open A3S48WP in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) {u : ℂ → E} (hc : ContinuousOn u U) (hu : ContDiffOn ℝ 1 u (U \ {z₀}))
    {p : ℝ} (hp : 1 ≤ p) (hint : ∫⁻ z in U, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ p) < ⊤) :
    JHolomorphic.HasWeakPartialsOn U u (fun z => fderiv ℝ u z 1)
        (fun z => fderiv ℝ u z Complex.I) ∧
      MemLp (fun z => fderiv ℝ u z 1) (ENNReal.ofReal p) (volume.restrict U) ∧
      MemLp (fun z => fderiv ℝ u z Complex.I) (ENNReal.ofReal p) (volume.restrict U) := by
  have h1 := memLp_dir hp hint 1 (by simp)
  have hI := memLp_dir hp hint Complex.I (by simp)
  refine ⟨?_, h1, hI⟩
  intro φ hφ hφc hsupp
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hK : IsCompact (tsupport φ) := hφc
  haveI : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
    ⟨by simpa using hK.measure_lt_top⟩
  obtain ⟨Cφ, hCφ⟩ := hφ1.continuous.bounded_above_of_compact_support hφc
  have integ : ∀ v : ℂ, MemLp (fun z => fderiv ℝ u z v) (ENNReal.ofReal p) (volume.restrict U) →
      Integrable (fun z => φ z • fderiv ℝ u z v) := by
    intro v hv
    have hvK := hv.mono_measure (Measure.restrict_mono hsupp le_rfl)
    have hiK : Integrable (fun z => fderiv ℝ u z v) (volume.restrict (tsupport φ)) :=
      hvK.integrable (by simpa using hp)
    have : IntegrableOn (fun z => φ z • fderiv ℝ u z v) (tsupport φ) :=
      hiK.bdd_smul Cφ hφ1.continuous.aestronglyMeasurable (Eventually.of_forall hCφ)
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 this
    intro z hz
    by_contra h
    exact hz (by simp [image_eq_zero_of_notMem_tsupport h])
  exact ⟨main hU hc hu hφ1 hφc hsupp 1 (Or.inl rfl) (integ 1 h1),
    main hU hc hu hφ1 hφc hsupp Complex.I (Or.inr rfl) (integ _ hI)⟩
