-- Prove2me | solution 1 for K24.Global.exactLocalSobolevCompletenessAndRepresentatives
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T20:16:32.180996+00:00
-- url     : https://prove2.me/submissions/7b6515ef-3413-4bcf-8251-3baffdf430ad

import Definitions.Def_K24GlobalAnalysis

set_option autoImplicit false

noncomputable section

open MeasureTheory TemperedDistribution Filter FourierTransform K24.Global
open scoped ENNReal Topology SchwartzMap BoundedContinuousFunction Real ContDiff

namespace K24SOB2Proof

/-- Inverting the actual Bessel potential recovers a distribution from its
unique L2 representative, for every real order. -/
private def inverseBesselL2 (s : ℝ) (v : LocalL2) : LocalDistribution :=
  besselPotential SobolevModel ℂ (-s) (v : LocalDistribution)

@[simp] private theorem besselPotential_inverseBesselL2 (s : ℝ) (v : LocalL2) :
    besselPotential SobolevModel ℂ s (inverseBesselL2 s v) =
      (v : LocalDistribution) := by
  simp [inverseBesselL2]

private theorem inverseBesselL2_mem (s : ℝ) (v : LocalL2) :
    BesselMem s (inverseBesselL2 s v) :=
  ⟨v, besselPotential_inverseBesselL2 s v⟩

private theorem besselPotential_injective (s : ℝ) :
    Function.Injective (besselPotential SobolevModel ℂ s) := by
  intro T U h
  have hh := congrArg (besselPotential SobolevModel ℂ (-s)) h
  simpa using hh

@[simp] private theorem inverseBesselL2_representative {s : ℝ} {T : LocalDistribution}
    (h : BesselMem s T) : inverseBesselL2 s (besselRepresentative h) = T := by
  apply besselPotential_injective s
  rw [besselPotential_inverseBesselL2, besselRepresentative_spec h]

private theorem besselRepresentative_add {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselRepresentative (hT.add hU) = besselRepresentative hT + besselRepresentative hU := by
  apply besselRepresentative_unique
  rw [map_add, besselRepresentative_spec hT, besselRepresentative_spec hU]
  exact (map_add (Lp.toTemperedDistributionCLM ℂ (volume : Measure SobolevModel) 2) _ _).symm

private theorem besselRepresentative_sub {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselRepresentative (hT.sub hU) = besselRepresentative hT - besselRepresentative hU := by
  apply besselRepresentative_unique
  rw [map_sub, besselRepresentative_spec hT, besselRepresentative_spec hU]
  exact (map_sub (Lp.toTemperedDistributionCLM ℂ (volume : Measure SobolevModel) 2) _ _).symm

private theorem besselMem_real_smul {s : ℝ} {T : LocalDistribution}
    (hT : BesselMem s T) (c : ℝ) : BesselMem s (c • T) := by
  simpa only [Complex.coe_smul] using hT.smul (c : ℂ)

private theorem besselRepresentative_real_smul {s : ℝ} {T : LocalDistribution}
    (hT : BesselMem s T) (c : ℝ) :
    besselRepresentative (besselMem_real_smul hT c) = c • besselRepresentative hT := by
  apply besselRepresentative_unique
  rw [ContinuousLinearMap.map_smul_of_tower, besselRepresentative_spec hT]
  exact ((Lp.toTemperedDistributionCLM ℂ (volume : Measure SobolevModel) 2).map_smul_of_tower
    c _).symm

/-- The exact canonical Sobolev distance is the L2 distance between the
Bessel representatives. No infinite norm is converted to a real number. -/
private theorem besselSobolevENN_sub_eq {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselSobolevENN s (T - U) =
      ENNReal.ofReal ‖besselRepresentative hT - besselRepresentative hU‖ := by
  rw [besselSobolevENN_of_mem (hT.sub hU), besselRepresentative_sub]

/-- Completeness and all norm laws for the actual distributional Bessel
space, with the exact canonical extended norm, for every real order. -/
private theorem exact_bessel_sectionBanachSpace (s : ℝ) :
    SectionBanachSpace {T : LocalDistribution | BesselMem s T}
      (besselSobolevENN s) := by
  refine
    { zero_mem := memSobolev_fun_zero SobolevModel ℂ s 2
      add_mem := fun _ hT _ hU => hT.add hU
      smul_mem := fun c _ hT => besselMem_real_smul hT c
      finite := fun T hT => (besselSobolevENN_lt_top_iff s T).mpr hT
      zero_norm := besselSobolevENN_zero s
      definite := ?_
      triangle := ?_
      homogeneous := ?_
      complete := ?_ }
  · intro T hT hz
    rw [besselSobolevENN_of_mem hT, ENNReal.ofReal_eq_zero] at hz
    have hr : besselRepresentative hT = 0 := norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))
    apply besselPotential_injective s
    rw [besselRepresentative_spec hT, hr]
    simp [← Lp.toTemperedDistributionCLM_apply]
  · intro T hT U hU
    rw [besselSobolevENN_of_mem (hT.add hU), besselRepresentative_add hT hU,
      besselSobolevENN_of_mem hT, besselSobolevENN_of_mem hU,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  · intro c T hT
    rw [besselSobolevENN_of_mem (besselMem_real_smul hT c),
      besselRepresentative_real_smul, norm_smul, Real.norm_eq_abs,
      ENNReal.ofReal_mul (abs_nonneg c), besselSobolevENN_of_mem hT]
  · intro f hf hc
    let u : ℕ → LocalL2 := fun n => besselRepresentative (hf n)
    have hu : CauchySeq u := by
      rw [Metric.cauchySeq_iff]
      intro eps heps
      obtain ⟨N, hN⟩ := hc eps heps
      refine ⟨N, fun i hi j hj => ?_⟩
      have hij := hN i hi j hj
      rw [besselSobolevENN_sub_eq (hf i) (hf j)] at hij
      simpa only [dist_eq_norm] using (ENNReal.ofReal_lt_ofReal_iff heps).mp hij
    obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hu
    refine ⟨inverseBesselL2 s v, inverseBesselL2_mem s v, ?_⟩
    intro eps heps
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hv) eps heps
    refine ⟨N, fun i hi => ?_⟩
    rw [besselSobolevENN_sub_eq (hf i) (inverseBesselL2_mem s v),
      besselRepresentative_unique (inverseBesselL2_mem s v) v
        (besselPotential_inverseBesselL2 s v)]
    apply (ENNReal.ofReal_lt_ofReal_iff heps).mpr
    simpa only [dist_eq_norm] using hN i hi


/-- A bounded continuous function defines a tempered distribution through
its genuine L-infinity equivalence class, even on infinite-volume space. -/
private def boundedContinuousDistribution (g : SobolevModel →ᵇ ℂ) : LocalDistribution :=
  ((g.memLp_top.toLp g : Lp ℂ ⊤ (volume : Measure SobolevModel)) : LocalDistribution)

private theorem boundedContinuousDistribution_apply (g : SobolevModel →ᵇ ℂ)
    (φ : 𝓢(SobolevModel, ℂ)) :
    boundedContinuousDistribution g φ = ∫ x, φ x • g x := by
  rw [boundedContinuousDistribution, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [g.memLp_top.coeFn_toLp (μ := (volume : Measure SobolevModel))] with x hx
  rw [hx]

/-- The L1 inverse Fourier integral and the distributional inverse Fourier
transform are the same distribution. -/
private theorem inverseFourierL1_distribution
    (v : Lp ℂ 1 (volume : Measure SobolevModel)) :
    boundedContinuousDistribution (Real.Lp.fourierTransformInv v) =
      𝓕⁻ (v : LocalDistribution) := by
  ext φ
  rw [boundedContinuousDistribution_apply, TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply]
  simp only [Real.Lp.fourierTransformInv_apply, SchwartzMap.fourierInv_coe]
  have hflip : (-innerₗ SobolevModel).flip = -innerₗ SobolevModel := by
    ext x y
    simp [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := (volume : Measure SobolevModel)) (ν := (volume : Measure SobolevModel))
    (L := -innerₗ SobolevModel) Real.continuous_fourierChar
    (show Continuous (fun p : SobolevModel × SobolevModel => -inner ℝ p.1 p.2) from
      (continuous_fst.inner continuous_snd).neg) φ.integrable (L1.integrable_coeFn v)
  rw [hflip] at h
  exact h.symm

/-- Every distribution in real-order H^s, s > 2, has a bounded continuous
representative as a distribution. -/
private theorem besselMem_exists_boundedContinuous {s : ℝ} (hs : 2 < s)
    {T : LocalDistribution} (hT : BesselMem s T) :
    ∃ g : SobolevModel →ᵇ ℂ, boundedContinuousDistribution g = T := by
  have hdim : Module.finrank ℝ SobolevModel < 2 * s := by
    rw [finrank_euclideanSpace_fin]
    norm_num
    linarith
  obtain ⟨v, hv⟩ := hT.fourier_memL1 hdim
  refine ⟨Real.Lp.fourierTransformInv v, ?_⟩
  rw [inverseFourierL1_distribution, ← hv, fourierInv_fourier_eq]

/-- Equality of genuine Lp distributions is equality almost everywhere,
also when the two integrability exponents differ. -/
private theorem lp_distribution_eq_ae {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)]
    (f : Lp ℂ p (volume : Measure SobolevModel))
    (g : Lp ℂ q (volume : Measure SobolevModel))
    (h : (f : LocalDistribution) = (g : LocalDistribution)) :
    (f : SobolevModel → ℂ) =ᵐ[volume] g := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp f).locallyIntegrable hp.out) ((Lp.memLp g).locallyIntegrable hq.out)
  intro φ hφ hφc
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hs : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  have he := congrArg (fun D : LocalDistribution => D (hc.toSchwartzMap hs)) h
  simpa using he

/-- Above the exact dimension-four threshold, the bounded continuous
representative also has the required L2 membership and represents the
original distribution through that L2 class. -/
private theorem besselMem_exists_boundedContinuous_L2 {s : ℝ} (hs : 2 < s)
    {T : LocalDistribution} (hT : BesselMem s T) :
    ∃ g : SobolevModel →ᵇ ℂ, ∃ hg : MemLp (g : SobolevModel → ℂ) 2 volume,
      ((hg.toLp g : LocalL2) : LocalDistribution) = T := by
  obtain ⟨g, hg⟩ := besselMem_exists_boundedContinuous hs hT
  obtain ⟨w, hw⟩ := memSobolev_zero_iff.mp (hT.mono (by linarith : 0 ≤ s))
  have hc : ((g.memLp_top.toLp g : Lp ℂ ⊤ (volume : Measure SobolevModel)) :
      LocalDistribution) = (w : LocalDistribution) := hg.trans hw
  have hae : (g : SobolevModel → ℂ) =ᵐ[volume] w :=
    g.memLp_top.coeFn_toLp.symm.trans (lp_distribution_eq_ae _ w hc)
  have hL : MemLp (g : SobolevModel → ℂ) 2 volume := (Lp.memLp w).ae_eq hae.symm
  refine ⟨g, hL, ?_⟩
  have hgw : hL.toLp g = w := by
    apply Lp.ext
    exact hL.coeFn_toLp.trans hae
  rw [hgw, ← hw]

/-- The canonical distribution of a continuous local coefficient determines
that coefficient pointwise, rather than only up to almost-everywhere equality. -/
private theorem localFunctionDistribution_injective_continuous
    {f g : SobolevModel → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfl : MemLp (complexifyLocal f) 2 volume)
    (hgl : MemLp (complexifyLocal g) 2 volume)
    (heq : localFunctionDistribution f hfl = localFunctionDistribution g hgl) :
    f = g := by
  have hL : hfl.toLp (complexifyLocal f) = hgl.toLp (complexifyLocal g) :=
    localL2_distribution_injective heq
  have hae : complexifyLocal f =ᵐ[volume] complexifyLocal g :=
    (MemLp.toLp_eq_toLp_iff hfl hgl).mp hL
  have hreal : f =ᵐ[volume] g := by
    filter_upwards [hae] with x hx
    exact Complex.ofReal_injective hx
  exact MeasureTheory.Measure.eq_of_ae_eq hreal hf hg

/-- Faithful C0 realization for the original real-valued coefficient
definition. The representative is unique pointwise, agrees with the input
almost everywhere, and has exactly the original extended Sobolev norm. -/
private theorem localSobolevMem_unique_continuous_representative {s : ℝ} (hs : 2 < s)
    {f : SobolevModel → ℝ} (hf : LocalSobolevMem s f) :
    ∃! g : SobolevModel → ℝ,
      Continuous g ∧ f =ᵐ[volume] g ∧ LocalSobolevMem s g ∧
        localSobolevENN s g = localSobolevENN s f := by
  classical
  obtain ⟨hfl, hfS⟩ := hf
  obtain ⟨G, hG, hGT⟩ := besselMem_exists_boundedContinuous_L2 hs hfS
  have hL : hG.toLp G = hfl.toLp (complexifyLocal f) :=
    localL2_distribution_injective hGT
  have hae : (G : SobolevModel → ℂ) =ᵐ[volume] complexifyLocal f :=
    (MemLp.toLp_eq_toLp_iff hG hfl).mp hL
  let g : SobolevModel → ℝ := fun x => (G x).re
  have hgc : Continuous g := Complex.continuous_re.comp G.continuous
  have hfg : f =ᵐ[volume] g := by
    filter_upwards [hae] with x hx
    simpa [g, complexifyLocal] using (congrArg Complex.re hx).symm
  have hcg : complexifyLocal g =ᵐ[volume] complexifyLocal f := by
    filter_upwards [hfg] with x hx
    simp [complexifyLocal, hx]
  have hgl : MemLp (complexifyLocal g) 2 volume := hfl.ae_eq hcg.symm
  have hd : localFunctionDistribution g hgl = localFunctionDistribution f hfl := by
    unfold localFunctionDistribution
    rw [MemLp.toLp_congr hgl hfl hcg]
  have hgs : LocalSobolevMem s g := ⟨hgl, hd ▸ hfS⟩
  have hn : localSobolevENN s g = localSobolevENN s f := by
    simp only [localSobolevENN, dif_pos hgl, dif_pos hfl, hd]
  refine ⟨g, ⟨hgc, hfg, hgs, hn⟩, ?_⟩
  intro g' hg'
  exact MeasureTheory.Measure.eq_of_ae_eq (hg'.2.1.symm.trans hfg) hg'.1 hgc


private def besselDecay (s : ℝ) (x : SobolevModel) : ℂ :=
  ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)

private theorem besselDecay_memLp_two {s : ℝ} (hs : 2 < s) :
    MemLp (besselDecay s) 2 volume := by
  have hr : MemLp (fun x : SobolevModel => (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 volume := by
    constructor
    · exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow SobolevModel (-s / 2)).1.continuous.aestronglyMeasurable
    · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      suffices h : ∫⁻ x : SobolevModel, ENNReal.ofReal ‖(1 + ‖x‖ ^ 2) ^ (-s)‖ < ⊤ from by
        norm_cast
        simp_rw [ofReal_norm] at h
        simp_rw [← enorm_pow]
        convert h
        rw [← Real.rpow_mul_natCast (by positivity)]
        simp
      have hdim : (Module.finrank ℝ SobolevModel : ℝ) < 2 * s := by
        rw [finrank_euclideanSpace_fin]
        norm_num
        linarith
      apply ((integrable_rpow_neg_one_add_norm_sq hdim).congr _).lintegral_lt_top
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
      congr
      ring
  exact hr.ofReal

private theorem besselDecay_moment_le (s : ℝ) (x : SobolevModel) {n : ℕ} (hn : n ≤ 2) :
    ‖x‖ ^ n * ‖besselDecay s x‖ ≤ ‖besselDecay (s - 2) x‖ := by
  have hb : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hp : ‖x‖ ^ n ≤ 1 + ‖x‖ ^ 2 := by
    interval_cases n <;> norm_num <;> nlinarith [sq_nonneg (‖x‖ - 1)]
  simp only [besselDecay, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (le_of_lt hb) _)]
  calc
    _ ≤ (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) ^ (-s / 2) := by gcongr
    _ = (1 + ‖x‖ ^ 2) ^ (-(s - 2) / 2) := by
      conv_lhs => lhs; rw [← Real.rpow_one (1 + ‖x‖ ^ 2)]
      rw [← Real.rpow_add hb]
      congr 1
      ring

/-- One decay weight controls all three genuine Fourier moments needed for
C2; its L2 norm is finite for the exact real threshold s > 4. -/
private theorem besselDecay_moments {s : ℝ} (hs : 4 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : LocalL2,
      ∀ n : ℕ, n ≤ 2 →
        Integrable (fun x : SobolevModel => ‖x‖ ^ n * ‖besselDecay s x * u x‖) ∧
        (∫ x : SobolevModel, ‖x‖ ^ n * ‖besselDecay s x * u x‖) ≤ C * ‖u‖ := by
  let hw := besselDecay_memLp_two (by linarith : 2 < s - 2)
  let w : LocalL2 := hw.toLp (besselDecay (s - 2))
  refine ⟨‖w‖, norm_nonneg _, ?_⟩
  intro u n hn
  let v : Lp ℂ 1 (volume : Measure SobolevModel) := w • u
  have hae : (v : SobolevModel → ℂ) =ᵐ[volume]
      (fun x => besselDecay (s - 2) x * u x) := by
    filter_upwards [Lp.coeFn_lpSMul (r := 1) w u, hw.coeFn_toLp] with x hx hy
    simpa [v, w, hy, smul_eq_mul] using hx
  have hi : Integrable (fun x => besselDecay (s - 2) x * u x) :=
    (L1.integrable_coeFn v).congr hae
  have hnorm : (∫ x, ‖besselDecay (s - 2) x * u x‖) = ‖v‖ := by
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae (hae.symm.fun_comp norm)
  have hbound : ∀ x : SobolevModel,
      ‖x‖ ^ n * ‖besselDecay s x * u x‖ ≤ ‖besselDecay (s - 2) x * u x‖ := by
    intro x
    simp only [norm_mul]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (besselDecay_moment_le s x hn) (norm_nonneg _)
  have hm : AEStronglyMeasurable
      (fun x : SobolevModel => ‖x‖ ^ n * ‖besselDecay s x * u x‖) volume := by
    have hc : Continuous (besselDecay s) := Complex.continuous_ofReal.comp
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow SobolevModel (-s / 2)).1.continuous
    exact (continuous_norm.pow n).aestronglyMeasurable.mul
      (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u)).norm
  have him : Integrable
      (fun x : SobolevModel => ‖x‖ ^ n * ‖besselDecay s x * u x‖) := by
    apply hi.norm.mono' hm
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤
      ‖x‖ ^ n * ‖besselDecay s x * u x‖)] using hbound x
  refine ⟨him, ?_⟩
  exact (integral_mono him hi.norm hbound).trans
    (hnorm.trans_le (Lp.norm_smul_le w u))


/-- The inverse Fourier integral of the decayed L2 input has genuine C2
regularity and a uniform bound on all actual derivatives through order two. -/
private theorem inverseFourier_besselDecay_C2 {s : ℝ} (hs : 4 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : LocalL2,
      ContDiff ℝ 2 (𝓕⁻ (fun x : SobolevModel => besselDecay s x * u x)) ∧
      ∀ n : ℕ, n ≤ 2 → ∀ x : SobolevModel,
        ‖iteratedFDeriv ℝ n
          (𝓕⁻ (fun y : SobolevModel => besselDecay s y * u y)) x‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hmom⟩ := besselDecay_moments hs
  let L : SobolevModel →L[ℝ] SobolevModel →L[ℝ] ℝ := -innerSL ℝ
  let A : ℝ := 2 * Real.pi * ‖L‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨(1 + A) ^ 2 * C, by positivity, ?_⟩
  intro u
  let f : SobolevModel → ℂ := fun x => besselDecay s x * u x
  have hf : ∀ n : ℕ, (n : ℕ∞) ≤ 2 → Integrable
      (fun x : SobolevModel => ‖x‖ ^ n * ‖f x‖) := by
    intro n hn
    exact (hmom u n (by exact_mod_cast hn)).1
  have hfm : AEStronglyMeasurable f volume := by
    have hc : Continuous (besselDecay s) := Complex.continuous_ofReal.comp
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow SobolevModel (-s / 2)).1.continuous
    exact hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u)
  constructor
  · exact VectorFourier.contDiff_fourierIntegral L hf
  · intro n hn x
    have hn' : (n : ℕ∞) ≤ 2 := by exact_mod_cast hn
    change ‖iteratedFDeriv ℝ n
      (VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂ f) x‖ ≤ _
    rw [VectorFourier.iteratedFDeriv_fourierIntegral L hf hfm hn']
    have hi := VectorFourier.integrable_fourierPowSMulRight L (hf n hn') hfm
    have hp : A ^ n ≤ (1 + A) ^ 2 := by
      calc
        A ^ n ≤ (1 + A) ^ n := by gcongr; linarith
        _ ≤ (1 + A) ^ 2 := pow_le_pow_right₀ (by linarith) hn
    calc
      _ ≤ ∫ y : SobolevModel, ‖VectorFourier.fourierPowSMulRight L f y n‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      _ ≤ ∫ y : SobolevModel, A ^ n * (‖y‖ ^ n * ‖f y‖) := by
        apply integral_mono hi.norm ((hf n hn').const_mul (A ^ n))
        intro y
        simpa only [A, mul_assoc] using VectorFourier.norm_fourierPowSMulRight_le L f y n
      _ = A ^ n * ∫ y : SobolevModel, ‖y‖ ^ n * ‖f y‖ := integral_const_mul _ _
      _ ≤ A ^ n * (C * ‖u‖) := mul_le_mul_of_nonneg_left (hmom u n hn).2 (by positivity)
      _ ≤ ((1 + A) ^ 2 * C) * ‖u‖ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hp (by positivity)

/-- Quantitative C2 realization of the actual canonical Bessel distribution.
The constant is uniform in the distribution, and the right side is precisely
the norm of its canonical Bessel representative. -/
private theorem besselMem_C2_representative_bound {s : ℝ} (hs : 4 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : LocalDistribution) (hT : BesselMem s T),
      ∃ g : SobolevModel →ᵇ ℂ, ∃ hg : MemLp (g : SobolevModel → ℂ) 2 volume,
        ((hg.toLp g : LocalL2) : LocalDistribution) = T ∧
        ContDiff ℝ 2 (g : SobolevModel → ℂ) ∧
        ∀ n : ℕ, n ≤ 2 → ∀ x : SobolevModel,
          ‖iteratedFDeriv ℝ n (g : SobolevModel → ℂ) x‖ ≤ C * ‖besselRepresentative hT‖ := by
  obtain ⟨C, hC, hbound⟩ := inverseFourier_besselDecay_C2 hs
  refine ⟨C, hC, ?_⟩
  intro T hT
  let u : LocalL2 := 𝓕 (besselRepresentative hT)
  have hu : TemperedDistribution.smulLeftCLM ℂ
      (fun x : SobolevModel => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 T) =
      (u : LocalDistribution) := by
    have hh := congrArg (fun D : LocalDistribution => 𝓕 D) (besselRepresentative_spec hT)
    rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      Lp.fourier_toTemperedDistribution_eq] at hh
    exact hh
  let hd := besselDecay_memLp_two (by linarith : 2 < s)
  let v : Lp ℂ 1 (volume : Measure SobolevModel) := hd.toLp (besselDecay s) • u
  have hv : (v : LocalDistribution) = 𝓕 T := by
    dsimp [v]
    rw [Lp.toTemperedDistribution_smul_eq]
    · rw [← hu, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
        (by fun_prop) (by unfold besselDecay; fun_prop)]
      have he : (fun x : SobolevModel => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) *
          besselDecay s = fun _ => (1 : ℂ) := by
        ext x
        simp only [Pi.mul_apply, besselDecay]
        norm_cast
        rw [← Real.rpow_add (by positivity)]
        ring_nf
        simp
      rw [he]
      simp
    · unfold besselDecay
      fun_prop
  let g : SobolevModel →ᵇ ℂ := Real.Lp.fourierTransformInv v
  have hgT : boundedContinuousDistribution g = T := by
    rw [inverseFourierL1_distribution, hv, fourierInv_fourier_eq]
  have hvae : (v : SobolevModel → ℂ) =ᵐ[volume]
      (fun x => besselDecay s x * u x) := by
    filter_upwards [Lp.coeFn_lpSMul (r := 1) (hd.toLp (besselDecay s)) u,
      hd.coeFn_toLp] with x hx hy
    simpa [v, hy, smul_eq_mul] using hx
  have hgf : (g : SobolevModel → ℂ) =
      𝓕⁻ (fun x : SobolevModel => besselDecay s x * u x) := by
    ext x
    exact (Real.Lp.fourierTransformInv_apply v x).trans
      (Real.fourierInv_congr_ae hvae x)
  obtain ⟨w, hw⟩ := memSobolev_zero_iff.mp (hT.mono (by linarith : 0 ≤ s))
  have hae : (g : SobolevModel → ℂ) =ᵐ[volume] w :=
    g.memLp_top.coeFn_toLp.symm.trans
      (lp_distribution_eq_ae _ w (hgT.trans hw))
  have hgl : MemLp (g : SobolevModel → ℂ) 2 volume := (Lp.memLp w).ae_eq hae.symm
  have hgw : hgl.toLp g = w := Lp.ext (hgl.coeFn_toLp.trans hae)
  refine ⟨g, hgl, ?_, ?_, ?_⟩
  · rw [hgw, ← hw]
  · rw [hgf]
    exact (hbound u).1
  · intro n hn x
    rw [hgf]
    simpa only [u, Lp.norm_fourier_eq] using (hbound u).2 n hn x

/-- Quantitative faithful C2 realization in the original real coefficient
space, with the exact original extended Sobolev norm on the right side. -/
private theorem localSobolevMem_unique_C2_representative_bound {s : ℝ} (hs : 4 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SobolevModel → ℝ), LocalSobolevMem s f →
      ∃! g : SobolevModel → ℝ,
        ContDiff ℝ 2 g ∧ f =ᵐ[volume] g ∧ LocalSobolevMem s g ∧
          localSobolevENN s g = localSobolevENN s f ∧
          ∀ n : ℕ, n ≤ 2 → ∀ x : SobolevModel,
            ENNReal.ofReal ‖iteratedFDeriv ℝ n g x‖ ≤
              ENNReal.ofReal C * localSobolevENN s f := by
  classical
  obtain ⟨C, hC, hbound⟩ := besselMem_C2_representative_bound hs
  refine ⟨C, hC, ?_⟩
  intro f hf
  obtain ⟨hfl, hfS⟩ := hf
  obtain ⟨G, hG, hGT, hGC, hGb⟩ := hbound _ hfS
  have hL : hG.toLp G = hfl.toLp (complexifyLocal f) :=
    localL2_distribution_injective hGT
  have hae : (G : SobolevModel → ℂ) =ᵐ[volume] complexifyLocal f :=
    (MemLp.toLp_eq_toLp_iff hG hfl).mp hL
  let g : SobolevModel → ℝ := Complex.reCLM ∘ (G : SobolevModel → ℂ)
  have hgc : ContDiff ℝ 2 g := Complex.reCLM.contDiff.comp hGC
  have hfg : f =ᵐ[volume] g := by
    filter_upwards [hae] with x hx
    simpa [g, complexifyLocal] using (congrArg Complex.re hx).symm
  have hcg : complexifyLocal g =ᵐ[volume] complexifyLocal f := by
    filter_upwards [hfg] with x hx
    simp [complexifyLocal, hx]
  have hgl : MemLp (complexifyLocal g) 2 volume := hfl.ae_eq hcg.symm
  have hd : localFunctionDistribution g hgl = localFunctionDistribution f hfl := by
    unfold localFunctionDistribution
    rw [MemLp.toLp_congr hgl hfl hcg]
  have hgs : LocalSobolevMem s g := ⟨hgl, hd ▸ hfS⟩
  have hn : localSobolevENN s g = localSobolevENN s f := by
    simp only [localSobolevENN, dif_pos hgl, dif_pos hfl, hd]
  refine ⟨g, ⟨hgc, hfg, hgs, hn, ?_⟩, ?_⟩
  · intro n hn x
    have hb : ‖iteratedFDeriv ℝ n g x‖ ≤ C * ‖besselRepresentative hfS‖ := by
      calc
        _ ≤ ‖Complex.reCLM‖ * ‖iteratedFDeriv ℝ n (G : SobolevModel → ℂ) x‖ :=
          Complex.reCLM.norm_iteratedFDeriv_comp_left hGC.contDiffAt (by exact_mod_cast hn)
        _ = ‖iteratedFDeriv ℝ n (G : SobolevModel → ℂ) x‖ := by
          rw [Complex.reCLM_norm, one_mul]
        _ ≤ C * ‖besselRepresentative hfS‖ := hGb n hn x
    have hnorm : ENNReal.ofReal ‖besselRepresentative hfS‖ = localSobolevENN s f := by
      simp only [localSobolevENN, dif_pos hfl, besselSobolevENN_of_mem hfS]
    calc
      _ ≤ ENNReal.ofReal (C * ‖besselRepresentative hfS‖) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal C * localSobolevENN s f := by
        rw [ENNReal.ofReal_mul hC, hnorm]
  · intro g' hg'
    exact MeasureTheory.Measure.eq_of_ae_eq (hg'.2.1.symm.trans hfg)
      hg'.1.continuous hgc.continuous

/-- In particular an already continuous original coefficient is itself C2,
and its genuine derivatives satisfy the same uniform canonical-norm bound. -/
private theorem continuous_localSobolevMem_C2_bound {s : ℝ} (hs : 4 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SobolevModel → ℝ,
      Continuous f → LocalSobolevMem s f →
      ContDiff ℝ 2 f ∧ ∀ n : ℕ, n ≤ 2 → ∀ x : SobolevModel,
        ENNReal.ofReal ‖iteratedFDeriv ℝ n f x‖ ≤
          ENNReal.ofReal C * localSobolevENN s f := by
  obtain ⟨C, hC, h⟩ := localSobolevMem_unique_C2_representative_bound hs
  refine ⟨C, hC, ?_⟩
  intro f hfc hfs
  obtain ⟨g, hg, _⟩ := h f hfs
  have heq : f = g := MeasureTheory.Measure.eq_of_ae_eq hg.2.1 hfc hg.1.continuous
  subst g
  exact ⟨hg.1, hg.2.2.2.2⟩


end K24SOB2Proof

theorem solution :
  (∀ s : ℝ,
    K24.Global.SectionBanachSpace
      {T : K24.Global.LocalDistribution | K24.Global.BesselMem s T}
      (K24.Global.besselSobolevENN s)) ∧
  (∀ s : ℝ, 2 < s → ∀ f : K24.Global.SobolevModel → ℝ,
    K24.Global.LocalSobolevMem s f →
    ∃! g : K24.Global.SobolevModel → ℝ,
      Continuous g ∧ f =ᵐ[volume] g ∧ K24.Global.LocalSobolevMem s g ∧
        K24.Global.localSobolevENN s g = K24.Global.localSobolevENN s f) ∧
  (∀ s : ℝ, 4 < s → ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : K24.Global.SobolevModel → ℝ, K24.Global.LocalSobolevMem s f →
      ∃! g : K24.Global.SobolevModel → ℝ,
        ContDiff ℝ 2 g ∧ f =ᵐ[volume] g ∧ K24.Global.LocalSobolevMem s g ∧
          K24.Global.localSobolevENN s g = K24.Global.localSobolevENN s f ∧
          ∀ n : ℕ, n ≤ 2 → ∀ x : K24.Global.SobolevModel,
            ENNReal.ofReal ‖iteratedFDeriv ℝ n g x‖ ≤
              ENNReal.ofReal C * K24.Global.localSobolevENN s f) := by
  exact ⟨K24SOB2Proof.exact_bessel_sectionBanachSpace,
    (fun s hs f hf => K24SOB2Proof.localSobolevMem_unique_continuous_representative hs hf),
    (fun s hs => K24SOB2Proof.localSobolevMem_unique_C2_representative_bound hs)⟩

#check (solution :
  (∀ s : ℝ,
    K24.Global.SectionBanachSpace
      {T : K24.Global.LocalDistribution | K24.Global.BesselMem s T}
      (K24.Global.besselSobolevENN s)) ∧
  (∀ s : ℝ, 2 < s → ∀ f : K24.Global.SobolevModel → ℝ,
    K24.Global.LocalSobolevMem s f →
    ∃! g : K24.Global.SobolevModel → ℝ,
      Continuous g ∧ f =ᵐ[volume] g ∧ K24.Global.LocalSobolevMem s g ∧
        K24.Global.localSobolevENN s g = K24.Global.localSobolevENN s f) ∧
  (∀ s : ℝ, 4 < s → ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : K24.Global.SobolevModel → ℝ, K24.Global.LocalSobolevMem s f →
      ∃! g : K24.Global.SobolevModel → ℝ,
        ContDiff ℝ 2 g ∧ f =ᵐ[volume] g ∧ K24.Global.LocalSobolevMem s g ∧
          K24.Global.localSobolevENN s g = K24.Global.localSobolevENN s f ∧
          ∀ n : ℕ, n ≤ 2 → ∀ x : K24.Global.SobolevModel,
            ENNReal.ofReal ‖iteratedFDeriv ℝ n g x‖ ≤
              ENNReal.ofReal C * K24.Global.localSobolevENN s f))
#print axioms solution
