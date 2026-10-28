-- Prove2me | solution 1 for K24.Global.originalSobolevCutoffMultipliers
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T05:00:49.399997+00:00
-- url     : https://prove2.me/submissions/5d568ca5-c086-47e9-9184-1b283afb27aa

import Definitions.Def_K24GlobalStatement
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.LConvolution

set_option autoImplicit false
noncomputable section
open scoped ENNReal NNReal


/- Reused source body: K24SOB_ExactBesselBanach.lean. -/

set_option autoImplicit false


open MeasureTheory TemperedDistribution Filter
open scoped ENNReal Topology

namespace K24.Global

/-- Inverting the actual Bessel potential recovers a distribution from its
unique L2 representative, for every real order. -/
def inverseBesselL2 (s : ℝ) (v : LocalL2) : LocalDistribution :=
  besselPotential SobolevModel ℂ (-s) (v : LocalDistribution)

@[simp] theorem besselPotential_inverseBesselL2 (s : ℝ) (v : LocalL2) :
    besselPotential SobolevModel ℂ s (inverseBesselL2 s v) =
      (v : LocalDistribution) := by
  simp [inverseBesselL2]

theorem inverseBesselL2_mem (s : ℝ) (v : LocalL2) :
    BesselMem s (inverseBesselL2 s v) :=
  ⟨v, besselPotential_inverseBesselL2 s v⟩

theorem besselPotential_injective (s : ℝ) :
    Function.Injective (besselPotential SobolevModel ℂ s) := by
  intro T U h
  have hh := congrArg (besselPotential SobolevModel ℂ (-s)) h
  simpa using hh

@[simp] theorem inverseBesselL2_representative {s : ℝ} {T : LocalDistribution}
    (h : BesselMem s T) : inverseBesselL2 s (besselRepresentative h) = T := by
  apply besselPotential_injective s
  rw [besselPotential_inverseBesselL2, besselRepresentative_spec h]

theorem besselRepresentative_add {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselRepresentative (hT.add hU) = besselRepresentative hT + besselRepresentative hU := by
  apply besselRepresentative_unique
  rw [map_add, besselRepresentative_spec hT, besselRepresentative_spec hU]
  exact (map_add (Lp.toTemperedDistributionCLM ℂ (volume : Measure SobolevModel) 2) _ _).symm

theorem besselRepresentative_sub {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselRepresentative (hT.sub hU) = besselRepresentative hT - besselRepresentative hU := by
  apply besselRepresentative_unique
  rw [map_sub, besselRepresentative_spec hT, besselRepresentative_spec hU]
  exact (map_sub (Lp.toTemperedDistributionCLM ℂ (volume : Measure SobolevModel) 2) _ _).symm

theorem besselMem_real_smul {s : ℝ} {T : LocalDistribution}
    (hT : BesselMem s T) (c : ℝ) : BesselMem s (c • T) := by
  simpa only [Complex.coe_smul] using hT.smul (c : ℂ)

theorem besselRepresentative_real_smul {s : ℝ} {T : LocalDistribution}
    (hT : BesselMem s T) (c : ℝ) :
    besselRepresentative (besselMem_real_smul hT c) = c • besselRepresentative hT := by
  apply besselRepresentative_unique
  rw [ContinuousLinearMap.map_smul_of_tower, besselRepresentative_spec hT]
  exact ((Lp.toTemperedDistributionCLM ℂ (volume : Measure SobolevModel) 2).map_smul_of_tower
    c _).symm

/-- The exact canonical Sobolev distance is the L2 distance between the
Bessel representatives. No infinite norm is converted to a real number. -/
theorem besselSobolevENN_sub_eq {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselSobolevENN s (T - U) =
      ENNReal.ofReal ‖besselRepresentative hT - besselRepresentative hU‖ := by
  rw [besselSobolevENN_of_mem (hT.sub hU), besselRepresentative_sub]

/-- Completeness and all norm laws for the actual distributional Bessel
space, with the exact canonical extended norm, for every real order. -/
theorem exact_bessel_sectionBanachSpace (s : ℝ) :
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

end K24.Global

/- Reused source body: K24SOB_ContinuousRepresentative.lean. -/

set_option autoImplicit false


open MeasureTheory TemperedDistribution FourierTransform
open scoped ENNReal SchwartzMap BoundedContinuousFunction Real ContDiff

namespace K24.Global

/-- A bounded continuous function defines a tempered distribution through
its genuine L-infinity equivalence class, even on infinite-volume space. -/
def boundedContinuousDistribution (g : SobolevModel →ᵇ ℂ) : LocalDistribution :=
  ((g.memLp_top.toLp g : Lp ℂ ⊤ (volume : Measure SobolevModel)) : LocalDistribution)

theorem boundedContinuousDistribution_apply (g : SobolevModel →ᵇ ℂ)
    (φ : 𝓢(SobolevModel, ℂ)) :
    boundedContinuousDistribution g φ = ∫ x, φ x • g x := by
  rw [boundedContinuousDistribution, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [g.memLp_top.coeFn_toLp (μ := (volume : Measure SobolevModel))] with x hx
  rw [hx]

/-- The L1 inverse Fourier integral and the distributional inverse Fourier
transform are the same distribution. -/
theorem inverseFourierL1_distribution
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
theorem besselMem_exists_boundedContinuous {s : ℝ} (hs : 2 < s)
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
theorem lp_distribution_eq_ae {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)] [hq : Fact (1 ≤ q)]
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
theorem besselMem_exists_boundedContinuous_L2 {s : ℝ} (hs : 2 < s)
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
theorem localFunctionDistribution_injective_continuous
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
theorem localSobolevMem_unique_continuous_representative {s : ℝ} (hs : 2 < s)
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

end K24.Global

/- Reused source body: K24SOBGLOBAL_Local.lean. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 16
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology BoundedContinuousFunction ContDiff

namespace K24.Global.SobolevGlobal

/- The two Fourier-bound proofs below are reused verbatim from inspected
submission fa438d8e-f66d-42e9-84e0-aeaa8cab0dcd, contribution
ca14bf25-33e4-4e12-9470-b9e44767ab91, archived as
K24-existing-bessel-pending-solution.lean.txt. The parent later confirmed
ACCEPTED (verdict K24-existing-bessel-verdict.json); this bundle checks the
actual reused proof body anew. -/
theorem bessel_inverse_weight_memL2 {s : ℝ} (hs : 2 < s) :
    MemLp (fun x : SobolevModel => (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 volume := by
  have hdim : (Module.finrank ℝ SobolevModel : ℝ) < 2 * s := by
    have hd : Module.finrank ℝ SobolevModel = 4 := by simp [SobolevModel]
    rw [hd]
    exact_mod_cast (by linarith : (4 : ℝ) < 2 * s)
  constructor
  · have hg : (fun x : SobolevModel => (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
      fun_prop
    exact hg.1.continuous.aestronglyMeasurable
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    suffices h : ∫⁻ a : SobolevModel, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
      norm_cast
      simp_rw [ofReal_norm] at h
      simp_rw [← enorm_pow]
      convert h
      rw [← Real.rpow_mul_natCast (by positivity)]
      simp
    apply ((integrable_rpow_neg_one_add_norm_sq hdim).congr _).lintegral_lt_top
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
    congr
    ring

theorem bessel_fourier_L1_bound_proof (s : ℝ) (hs : 2 < s) :
    ∃ A : ℝ≥0, ∀ T : LocalDistribution, BesselMem s T →
    ∃ v : Lp ℂ 1 (volume : Measure SobolevModel),
      𝓕 T = (v : LocalDistribution) ∧
      ENNReal.ofReal ‖v‖ ≤ (A : ℝ≥0∞) * besselSobolevENN s T := by
  let w : SobolevModel → ℂ := fun x => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))
  have hw : MemLp w 2 volume := (bessel_inverse_weight_memL2 hs).ofReal
  let W : LocalL2 := hw.toLp w
  refine ⟨‖W‖₊, fun T hT => ?_⟩
  let u : LocalL2 := 𝓕 (besselRepresentative hT)
  have hu : smulLeftCLM ℂ (fun x : SobolevModel => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ))
      (𝓕 T) = (u : LocalDistribution) := by
    rw [← fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      besselRepresentative_spec hT, Lp.fourier_toTemperedDistribution_eq]
  let v : Lp ℂ 1 (volume : Measure SobolevModel) := W • u
  refine ⟨v, ?_, ?_⟩
  · have hv : (v : LocalDistribution) = smulLeftCLM ℂ w (u : LocalDistribution) :=
      Lp.toTemperedDistribution_smul_eq (by fun_prop) hw u
    rw [hv, ← hu, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert! (smulLeftCLM_const 1 (𝓕 T)).symm using 1
    · simp
    · congr
      ext x
      rw [Pi.mul_apply]
      dsimp [w]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
  · have hbound : ‖v‖ ≤ ‖W‖ * ‖besselRepresentative hT‖ := by
      calc
        ‖v‖ ≤ ‖W‖ * ‖u‖ := Lp.norm_smul_le W u
        _ = _ := by simp only [u, Lp.norm_fourier_eq]
    rw [besselSobolevENN_of_mem hT]
    calc
      ENNReal.ofReal ‖v‖ ≤ ENNReal.ofReal (‖W‖ * ‖besselRepresentative hT‖) :=
        ENNReal.ofReal_le_ofReal hbound
      _ = _ := by rw [ENNReal.ofReal_mul (norm_nonneg W), ofReal_norm]; rfl


theorem boundedContinuousDistribution_injective :
    Function.Injective boundedContinuousDistribution := by
  intro g h heq
  have hae := lp_distribution_eq_ae
    (g.memLp_top.toLp g : Lp ℂ ⊤ (volume : Measure SobolevModel))
    (h.memLp_top.toLp h : Lp ℂ ⊤ (volume : Measure SobolevModel)) heq
  have hfun : (g : SobolevModel → ℂ) = (h : SobolevModel → ℂ) :=
    MeasureTheory.Measure.eq_of_ae_eq
      (g.memLp_top.coeFn_toLp.symm.trans (hae.trans h.memLp_top.coeFn_toLp))
      g.continuous h.continuous
  exact DFunLike.coe_injective hfun

theorem norm_inverseFourierL1_le (v : Lp ℂ 1 (volume : Measure SobolevModel)) :
    ‖Real.Lp.fourierTransformInv v‖ ≤ ‖v‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg v)).mpr
  intro x
  rw [Real.Lp.fourierTransformInv_apply, Real.fourierInv_eq]
  calc
    _ ≤ ∫ y : SobolevModel, ‖Real.fourierChar (inner ℝ y x) • v y‖ :=
      norm_integral_le_integral_norm _
    _ = ‖v‖ := by simp_rw [Circle.norm_smul]; exact (L1.norm_eq_integral_norm v).symm

/-- Quantitative control on every faithful bounded continuous realization,
at the full exact C0 threshold s > 2. -/
theorem bessel_continuous_norm_bound {s : ℝ} (hs : 2 < s) :
    ∃ A : ℝ≥0, ∀ (T : LocalDistribution) (hT : BesselMem s T)
      (g : SobolevModel →ᵇ ℂ), boundedContinuousDistribution g = T →
      ‖g‖ ≤ (A : ℝ) * ‖besselRepresentative hT‖ := by
  obtain ⟨A, hA⟩ := bessel_fourier_L1_bound_proof s hs
  refine ⟨A, ?_⟩
  intro T hT g hg
  obtain ⟨v, hv, hb⟩ := hA T hT
  have heq : Real.Lp.fourierTransformInv v = g := by
    apply boundedContinuousDistribution_injective
    rw [inverseFourierL1_distribution, ← hv, fourierInv_fourier_eq, hg]
  have hvb : ‖v‖ ≤ (A : ℝ) * ‖besselRepresentative hT‖ := by
    rw [besselSobolevENN_of_mem hT, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul A.coe_nonneg] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  rw [← heq]
  exact (norm_inverseFourierL1_le v).trans hvb

theorem localFunctionDistribution_add (f g : SobolevModel → ℝ)
    (hf : MemLp (complexifyLocal f) 2 volume) (hg : MemLp (complexifyLocal g) 2 volume)
    (hfg : MemLp (complexifyLocal (f + g)) 2 volume) :
    localFunctionDistribution (f + g) hfg =
      localFunctionDistribution f hf + localFunctionDistribution g hg := by
  unfold localFunctionDistribution
  simp only [← Lp.toTemperedDistributionCLM_apply, ← map_add]
  congr 1
  apply Lp.ext
  filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
    Lp.coeFn_add (hf.toLp (complexifyLocal f)) (hg.toLp (complexifyLocal g))] with x hfgx hfx hgx hadd
  simp only [hfgx, hadd, Pi.add_apply, hfx, hgx, complexifyLocal, Complex.ofReal_add]

theorem localFunctionDistribution_sub (f g : SobolevModel → ℝ)
    (hf : MemLp (complexifyLocal f) 2 volume) (hg : MemLp (complexifyLocal g) 2 volume)
    (hfg : MemLp (complexifyLocal (f - g)) 2 volume) :
    localFunctionDistribution (f - g) hfg =
      localFunctionDistribution f hf - localFunctionDistribution g hg := by
  unfold localFunctionDistribution
  simp only [← Lp.toTemperedDistributionCLM_apply, ← map_sub]
  congr 1
  apply Lp.ext
  filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
    Lp.coeFn_sub (hf.toLp (complexifyLocal f)) (hg.toLp (complexifyLocal g))] with x hfgx hfx hgx hsub
  simp only [hfgx, hsub, Pi.sub_apply, hfx, hgx, complexifyLocal, Complex.ofReal_sub]

theorem localFunctionDistribution_smul (c : ℝ) (f : SobolevModel → ℝ)
    (hf : MemLp (complexifyLocal f) 2 volume)
    (hcf : MemLp (complexifyLocal (c • f)) 2 volume) :
    localFunctionDistribution (c • f) hcf = c • localFunctionDistribution f hf := by
  unfold localFunctionDistribution
  simp only [← Lp.toTemperedDistributionCLM_apply, ← ContinuousLinearMap.map_smul_of_tower]
  congr 1
  apply Lp.ext
  filter_upwards [hcf.coeFn_toLp, hf.coeFn_toLp,
    Lp.coeFn_smul c (hf.toLp (complexifyLocal f))] with x hcfx hfx hsmul
  simp only [hcfx, hsmul, Pi.smul_apply, hfx, complexifyLocal, smul_eq_mul,
    Complex.ofReal_mul, Complex.real_smul]

theorem localSobolevMem_add {s : ℝ} {f g : SobolevModel → ℝ}
    (hf : LocalSobolevMem s f) (hg : LocalSobolevMem s g) : LocalSobolevMem s (f + g) := by
  obtain ⟨hfl, hfs⟩ := hf
  obtain ⟨hgl, hgs⟩ := hg
  have hfg : MemLp (complexifyLocal (f + g)) 2 volume := by
    convert hfl.add hgl using 1
    ext x; simp [complexifyLocal]
  refine ⟨hfg, ?_⟩
  rw [localFunctionDistribution_add _ _ hfl hgl hfg]
  exact hfs.add hgs

theorem localSobolevMem_sub {s : ℝ} {f g : SobolevModel → ℝ}
    (hf : LocalSobolevMem s f) (hg : LocalSobolevMem s g) : LocalSobolevMem s (f - g) := by
  obtain ⟨hfl, hfs⟩ := hf
  obtain ⟨hgl, hgs⟩ := hg
  have hfg : MemLp (complexifyLocal (f - g)) 2 volume := by
    convert hfl.sub hgl using 1
    ext x; simp [complexifyLocal]
  refine ⟨hfg, ?_⟩
  rw [localFunctionDistribution_sub _ _ hfl hgl hfg]
  exact hfs.sub hgs

theorem localSobolevMem_smul {s : ℝ} {f : SobolevModel → ℝ}
    (hf : LocalSobolevMem s f) (c : ℝ) : LocalSobolevMem s (c • f) := by
  obtain ⟨hfl, hfs⟩ := hf
  have hcf : MemLp (complexifyLocal (c • f)) 2 volume := by
    convert hfl.const_smul c using 1
    ext x; simp [complexifyLocal]
  refine ⟨hcf, ?_⟩
  rw [localFunctionDistribution_smul _ _ hfl hcf]
  exact besselMem_real_smul hfs c

theorem localSobolevENN_add_le {s : ℝ} {f g : SobolevModel → ℝ}
    (hf : LocalSobolevMem s f) (hg : LocalSobolevMem s g) :
    localSobolevENN s (f + g) ≤ localSobolevENN s f + localSobolevENN s g := by
  obtain ⟨hfl, hfs⟩ := hf
  obtain ⟨hgl, hgs⟩ := hg
  obtain ⟨hfg, _⟩ := localSobolevMem_add ⟨hfl, hfs⟩ ⟨hgl, hgs⟩
  simp only [localSobolevENN, dif_pos hfl, dif_pos hgl, dif_pos hfg,
    localFunctionDistribution_add _ _ hfl hgl hfg]
  exact (exact_bessel_sectionBanachSpace s).triangle _ hfs _ hgs

theorem localSobolevENN_smul {s : ℝ} {f : SobolevModel → ℝ}
    (hf : LocalSobolevMem s f) (c : ℝ) :
    localSobolevENN s (c • f) = ENNReal.ofReal |c| * localSobolevENN s f := by
  obtain ⟨hfl, hfs⟩ := hf
  obtain ⟨hcf, _⟩ := localSobolevMem_smul ⟨hfl, hfs⟩ c
  simp only [localSobolevENN, dif_pos hfl, dif_pos hcf,
    localFunctionDistribution_smul _ _ hfl hcf]
  exact (exact_bessel_sectionBanachSpace s).homogeneous c _ hfs

theorem boundedContinuousDistribution_sub (f g : SobolevModel →ᵇ ℂ) :
    boundedContinuousDistribution (f - g) =
      boundedContinuousDistribution f - boundedContinuousDistribution g := by
  unfold boundedContinuousDistribution
  simp only [← Lp.toTemperedDistributionCLM_apply, ← map_sub]
  congr 1

theorem boundedContinuousDistribution_eq_L2 (g : SobolevModel →ᵇ ℂ)
    (hg : MemLp (g : SobolevModel → ℂ) 2 volume) :
    boundedContinuousDistribution g = ((hg.toLp g : LocalL2) : LocalDistribution) := by
  ext φ
  rw [boundedContinuousDistribution_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]

theorem eq_complexify_of_distribution_eq {f : SobolevModel → ℝ}
    (hf : Continuous f) (hfl : MemLp (complexifyLocal f) 2 volume)
    (g : SobolevModel →ᵇ ℂ)
    (hg : boundedContinuousDistribution g = localFunctionDistribution f hfl) :
    (g : SobolevModel → ℂ) = complexifyLocal f := by
  have hae := lp_distribution_eq_ae
    (g.memLp_top.toLp g : Lp ℂ ⊤ (volume : Measure SobolevModel))
    (hfl.toLp (complexifyLocal f)) hg
  exact MeasureTheory.Measure.eq_of_ae_eq
    (g.memLp_top.coeFn_toLp.symm.trans (hae.trans hfl.coeFn_toLp))
    g.continuous (Complex.continuous_ofReal.comp hf)

end K24.Global.SobolevGlobal

/- Reused source body: K24SOB2_FourierMoments.lean. -/

set_option autoImplicit false


open MeasureTheory TemperedDistribution FourierTransform
open scoped ENNReal SchwartzMap Real ContDiff

namespace K24.Global

def besselDecay (s : ℝ) (x : SobolevModel) : ℂ :=
  ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)

theorem besselDecay_memLp_two {s : ℝ} (hs : 2 < s) :
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

theorem besselDecay_moment_le (s : ℝ) (x : SobolevModel) {n : ℕ} (hn : n ≤ 2) :
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
theorem besselDecay_moments {s : ℝ} (hs : 4 < s) :
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

end K24.Global

/- Reused source body: K24SOBALG_Weights.lean. -/

set_option autoImplicit false
open MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal NNReal

namespace K24.Global.SobolevAlgebra

/-- The exact real-order weight used by the canonical Bessel potential. -/
def besselWeight (r : ℝ) (x : SobolevModel) : ℝ := (1 + ‖x‖ ^ 2) ^ (r / 2)

theorem besselWeight_pos (r : ℝ) (x : SobolevModel) : 0 < besselWeight r x := by
  unfold besselWeight
  positivity

theorem besselWeight_nonneg (r : ℝ) (x : SobolevModel) : 0 ≤ besselWeight r x :=
  (besselWeight_pos r x).le

@[fun_prop] theorem besselWeight_continuous (r : ℝ) : Continuous (besselWeight r) := by
  have h : (besselWeight r).HasTemperateGrowth := by
    unfold besselWeight
    fun_prop
  exact h.1.continuous

/-- A real-order Peetre estimate with an explicit constant and no rounding of the order. -/
theorem besselWeight_add_le (r : ℝ) (hr : 0 ≤ r) (x y : SobolevModel) :
    besselWeight r (x + y) ≤ (4 : ℝ) ^ (r / 2) *
      (besselWeight r x + besselWeight r y) := by
  have haux (a b : SobolevModel) (hab : ‖a‖ ≤ ‖b‖) :
      besselWeight r (a + b) ≤ (4 : ℝ) ^ (r / 2) * besselWeight r b := by
    have hn := norm_add_le a b
    have hsq : 1 + ‖a + b‖ ^ 2 ≤ 4 * (1 + ‖b‖ ^ 2) := by
      nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a + b)]
    unfold besselWeight
    calc
      _ ≤ (4 * (1 + ‖b‖ ^ 2)) ^ (r / 2) :=
        Real.rpow_le_rpow (by positivity) hsq (by positivity)
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  rcases le_total ‖x‖ ‖y‖ with hxy | hyx
  · exact (haux x y hxy).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (besselWeight_nonneg r x)) (by positivity))
  · rw [add_comm x y]
    exact (haux y x hyx).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (besselWeight_nonneg r y)) (by positivity))

/-- The convolution form of the same exact-weight estimate. -/
theorem besselWeight_sub_le (r : ℝ) (hr : 0 ≤ r) (x y : SobolevModel) :
    besselWeight r x ≤ (4 : ℝ) ^ (r / 2) *
      (besselWeight r y + besselWeight r (x - y)) := by
  simpa only [add_sub_cancel] using besselWeight_add_le r hr y (x - y)

end K24.Global.SobolevAlgebra

/- Reused source body: K24SOBALG_Representative.lean. -/

set_option autoImplicit false
open MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal NNReal SchwartzMap

namespace K24.Global.SobolevAlgebra

/-- Multiplying the Fourier L1 representative by the exact Bessel weight recovers
its canonical weighted L2 representative. The L1 estimate is the previously checked one. -/
theorem bessel_fourier_weighted_representative (r : ℝ) (hr : 2 < r) :
    ∃ A : ℝ≥0, ∀ (T : LocalDistribution) (hT : BesselMem r T),
      ∃ v : Lp ℂ 1 (volume : Measure SobolevModel),
        𝓕 T = (v : LocalDistribution) ∧
        MemLp (fun x => (besselWeight r x : ℂ) * v x) 2 volume ∧
        eLpNorm (fun x => (besselWeight r x : ℂ) * v x) 2 volume =
          besselSobolevENN r T ∧
        eLpNorm v 1 volume ≤ (A : ℝ≥0∞) * besselSobolevENN r T := by
  obtain ⟨A, hA⟩ := SobolevGlobal.bessel_fourier_L1_bound_proof r hr
  refine ⟨A, fun T hT => ?_⟩
  obtain ⟨v, hv, hvbound⟩ := hA T hT
  let u : LocalL2 := 𝓕 (besselRepresentative hT)
  have hu : smulLeftCLM ℂ (fun x : SobolevModel => (besselWeight r x : ℂ))
      (𝓕 T) = (u : LocalDistribution) := by
    change smulLeftCLM ℂ (fun x : SobolevModel => (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ))
      (𝓕 T) = _
    rw [← fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      besselRepresentative_spec hT, Lp.fourier_toTemperedDistribution_eq]
  let hd := besselDecay_memLp_two hr
  let v' : Lp ℂ 1 (volume : Measure SobolevModel) := hd.toLp (besselDecay r) • u
  have hv' : (v' : LocalDistribution) = 𝓕 T := by
    dsimp [v']
    rw [Lp.toTemperedDistribution_smul_eq (by unfold besselDecay; fun_prop)]
    rw [← hu, smulLeftCLM_smulLeftCLM_apply
      (by unfold besselWeight; fun_prop) (by unfold besselDecay; fun_prop)]
    have he : (fun x : SobolevModel => (besselWeight r x : ℂ)) * besselDecay r =
        fun _ => (1 : ℂ) := by
      ext x
      simp only [Pi.mul_apply, besselWeight, besselDecay]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
    rw [he]
    simp
  have hveq : (v : SobolevModel → ℂ) =ᵐ[volume] v' :=
    lp_distribution_eq_ae v v' (hv.symm.trans hv'.symm)
  have hvweighted : (fun x => (besselWeight r x : ℂ) * v x) =ᵐ[volume] u := by
    filter_upwards [hveq, Lp.coeFn_lpSMul (r := 1) (hd.toLp (besselDecay r)) u,
      hd.coeFn_toLp] with x hx hvx hdx
    rw [hx, hvx]
    change (besselWeight r x : ℂ) * ((hd.toLp (besselDecay r)) x * u x) = u x
    rw [hdx, ← mul_assoc]
    have hw : (besselWeight r x : ℂ) * besselDecay r x = 1 := by
      simp only [besselWeight, besselDecay]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
    rw [hw, one_mul]
  refine ⟨v, hv, (Lp.memLp u).ae_eq hvweighted.symm, ?_, ?_⟩
  · rw [eLpNorm_congr_ae hvweighted, ← Lp.enorm_def, ← ofReal_norm,
      show ‖u‖ = ‖besselRepresentative hT‖ from Lp.norm_fourier_eq _,
      besselSobolevENN_of_mem hT]
  · simpa only [← Lp.enorm_def, ← ofReal_norm] using hvbound

/-- An actual integrable Fourier function with finite weighted L2 norm defines
an H^r distribution, with equality of the canonical norm and that weighted norm. -/
theorem bessel_inverseFourier_norm {r : ℝ} {v : SobolevModel → ℂ}
    (hv : Integrable v volume)
    (hw : MemLp (fun x => (besselWeight r x : ℂ) * v x) 2 volume) :
    BesselMem r (𝓕⁻ (((memLp_one_iff_integrable.mpr hv).toLp v : Lp ℂ 1 volume) : LocalDistribution)) ∧
      besselSobolevENN r (𝓕⁻ (((memLp_one_iff_integrable.mpr hv).toLp v : Lp ℂ 1 volume) : LocalDistribution)) =
        eLpNorm (fun x => (besselWeight r x : ℂ) * v x) 2 volume := by
  let w : LocalL2 := hw.toLp (fun x => (besselWeight r x : ℂ) * v x)
  have hwT : smulLeftCLM ℂ (fun x : SobolevModel => (besselWeight r x : ℂ))
      (((memLp_one_iff_integrable.mpr hv).toLp v : Lp ℂ 1 volume) : LocalDistribution) = (w : LocalDistribution) := by
    ext φ
    rw [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
      Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [(memLp_one_iff_integrable.mpr hv).coeFn_toLp, hw.coeFn_toLp] with x hvx hwx
    simp only [w, hwx, hvx, SchwartzMap.smulLeftCLM_apply_apply
      (show (fun x : SobolevModel => (besselWeight r x : ℂ)).HasTemperateGrowth by
        unfold besselWeight; fun_prop), smul_eq_mul]
    ring
  have hrep : besselPotential SobolevModel ℂ r
      (𝓕⁻ (((memLp_one_iff_integrable.mpr hv).toLp v : Lp ℂ 1 volume) : LocalDistribution)) =
      ((𝓕⁻ w : LocalL2) : LocalDistribution) := by
    rw [besselPotential, TemperedDistribution.fourierMultiplierCLM_apply,
      fourier_fourierInv_eq]
    change 𝓕⁻ (smulLeftCLM ℂ (fun x : SobolevModel => (besselWeight r x : ℂ))
      (((memLp_one_iff_integrable.mpr hv).toLp v : Lp ℂ 1 volume) : LocalDistribution)) = _
    rw [hwT, Lp.fourierInv_toTemperedDistribution_eq]
  refine ⟨⟨𝓕⁻ w, hrep⟩, ?_⟩
  have hnorm : ‖𝓕⁻ w‖ = ‖w‖ := by
    rw [← Lp.norm_fourier_eq (𝓕⁻ w), fourier_fourierInv_eq]
  rw [besselSobolevENN_eq_of_rep _ hrep, hnorm, ofReal_norm]
  exact Lp.enorm_toLp hw

end K24.Global.SobolevAlgebra

/- Reused source body: K24SOBALG_ProductBridge.lean. -/

set_option autoImplicit false
open MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal NNReal SchwartzMap Convolution BoundedContinuousFunction

namespace K24.Global.SobolevAlgebra

/-- Inverse Fourier transform carries the genuine L1 convolution to the
pointwise product of its bounded continuous inverse transforms. -/
theorem inverseFourierL1_convolution
    (v w : Lp ℂ 1 (volume : Measure SobolevModel)) :
    ∃ hc : Integrable ((v : SobolevModel → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (w : SobolevModel → ℂ)) volume,
      Real.Lp.fourierTransformInv ((memLp_one_iff_integrable.mpr hc).toLp _) =
        Real.Lp.fourierTransformInv v * Real.Lp.fourierTransformInv w := by
  let c := (v : SobolevModel → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ]
    (w : SobolevModel → ℂ)
  have hc : Integrable c volume := (L1.integrable_coeFn v).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (L1.integrable_coeFn w)
  refine ⟨hc, ?_⟩
  ext x
  simp only [Real.Lp.fourierTransformInv_apply, BoundedContinuousFunction.mul_apply]
  rw [Real.fourierInv_congr_ae (memLp_one_iff_integrable.mpr hc).coeFn_toLp x]
  simp only [Real.fourierInv_eq_fourier_neg]
  exact Real.fourier_mul_convolution_eq (L1.integrable_coeFn v) (L1.integrable_coeFn w) (-x)

/-- Distributional form of the genuine convolution-product identity. -/
theorem inverseFourierL1_convolution_distribution
    (v w : Lp ℂ 1 (volume : Measure SobolevModel)) :
    ∃ hc : Integrable ((v : SobolevModel → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (w : SobolevModel → ℂ)) volume,
      boundedContinuousDistribution
          (Real.Lp.fourierTransformInv v * Real.Lp.fourierTransformInv w) =
        𝓕⁻ (((memLp_one_iff_integrable.mpr hc).toLp _ : Lp ℂ 1 volume) :
          LocalDistribution) := by
  obtain ⟨hc, he⟩ := inverseFourierL1_convolution v w
  exact ⟨hc, he ▸ inverseFourierL1_distribution _⟩

/-- The original Bessel membership of a bounded continuous realization implies
its actual square integrability. -/
theorem boundedContinuous_memLp_of_bessel {r : ℝ} (hr : 2 < r)
    (f : SobolevModel →ᵇ ℂ) (hf : BesselMem r (boundedContinuousDistribution f)) :
    MemLp (f : SobolevModel → ℂ) 2 volume := by
  obtain ⟨g, hg, he⟩ := besselMem_exists_boundedContinuous_L2 hr hf
  have hge : g = f := SobolevGlobal.boundedContinuousDistribution_injective
    ((SobolevGlobal.boundedContinuousDistribution_eq_L2 g hg).trans he)
  simpa only [hge] using hg

/-- A bounded continuous representative of a local coefficient, with equality
of its original distribution and exact original norm. -/
theorem localSobolev_boundedContinuous_realization {r : ℝ} (hr : 2 < r)
    {f : SobolevModel → ℝ} (hf : LocalSobolevMem r f) :
    ∃ F : SobolevModel →ᵇ ℂ,
      (F : SobolevModel → ℂ) =ᵐ[volume] complexifyLocal f ∧
      MemLp (F : SobolevModel → ℂ) 2 volume ∧
      BesselMem r (boundedContinuousDistribution F) ∧
      besselSobolevENN r (boundedContinuousDistribution F) = localSobolevENN r f := by
  obtain ⟨hfl, hfr⟩ := hf
  obtain ⟨F, hF, hFT⟩ := besselMem_exists_boundedContinuous_L2 hr hfr
  have hdist : boundedContinuousDistribution F = localFunctionDistribution f hfl :=
    (SobolevGlobal.boundedContinuousDistribution_eq_L2 F hF).trans hFT
  have hae : (F : SobolevModel → ℂ) =ᵐ[volume] complexifyLocal f := by
    exact hF.coeFn_toLp.symm.trans
      ((lp_distribution_eq_ae (hF.toLp F) (hfl.toLp (complexifyLocal f)) hFT).trans
        hfl.coeFn_toLp)
  refine ⟨F, hae, hF, hdist ▸ hfr, ?_⟩
  simp only [localSobolevENN, dif_pos hfl, hdist]

/-- Product membership and its exact norm descend from faithful complex
bounded continuous representatives to the original real local coefficients. -/
theorem localSobolev_product_descent {r : ℝ} {f g : SobolevModel → ℝ}
    (F G : SobolevModel →ᵇ ℂ)
    (hF : (F : SobolevModel → ℂ) =ᵐ[volume] complexifyLocal f)
    (hG : (G : SobolevModel → ℂ) =ᵐ[volume] complexifyLocal g)
    (hG2 : MemLp (G : SobolevModel → ℂ) 2 volume)
    (hprod : BesselMem r (boundedContinuousDistribution (F * G))) :
    LocalSobolevMem r (f * g) ∧
      localSobolevENN r (f * g) = besselSobolevENN r (boundedContinuousDistribution (F * G)) := by
  have hFG2 : MemLp ((F * G : SobolevModel →ᵇ ℂ) : SobolevModel → ℂ) 2 volume := by
    change MemLp (fun x => F x * G x) 2 volume
    exact hG2.mul (r := 2) F.memLp_top
  have hae : ((F * G : SobolevModel →ᵇ ℂ) : SobolevModel → ℂ) =ᵐ[volume]
      complexifyLocal (f * g) := by
    filter_upwards [hF, hG] with x hFx hGx
    simp only [BoundedContinuousFunction.mul_apply, hFx, hGx, complexifyLocal,
      Pi.mul_apply, Complex.ofReal_mul]
  have hfg2 : MemLp (complexifyLocal (f * g)) 2 volume := hFG2.ae_eq hae
  have hdist : localFunctionDistribution (f * g) hfg2 = boundedContinuousDistribution (F * G) := by
    rw [SobolevGlobal.boundedContinuousDistribution_eq_L2 (F * G) hFG2]
    unfold localFunctionDistribution
    congr 1
    exact MemLp.toLp_congr hfg2 hFG2 hae.symm
  refine ⟨⟨hfg2, hdist ▸ hprod⟩, ?_⟩
  simp only [localSobolevENN, dif_pos hfg2, hdist]

end K24.Global.SobolevAlgebra

/- Reused source body: K24SOBYOUNG_Young.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16
open MeasureTheory FourierTransform
open scoped ENNReal NNReal Convolution

namespace K24.Global.SobolevAlgebra

/-- Weighted Cauchy--Schwarz, including extended values. Adapted from the
initial scalar Young draft by the Sobolev algebra agent. -/
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) ^ (2 : ℕ) ≤
      (∫⁻ x, f x ∂μ) * (∫⁻ x, f x * g x ^ (2 : ℕ) ∂μ) := by
  have hh := ENNReal.lintegral_mul_norm_pow_le hf (hf.mul (hg.pow_const 2))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hid (x : α) : f x ^ (1 / 2 : ℝ) * (f x * g x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) =
      f x * g x := by
    calc
      _ = (f x * (f x * g x ^ (2 : ℕ))) ^ (1 / 2 : ℝ) :=
        (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)).symm
      _ = ((f x * g x) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by congr 1; ring
      _ = _ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
  change (∫⁻ x, f x ^ (1 / 2 : ℝ) * (f x * g x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ∂μ) ≤
    (∫⁻ x, f x ∂μ) ^ (1 / 2 : ℝ) *
      (∫⁻ x, f x * g x ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) at hh
  simp_rw [hid] at hh
  have hh2 := pow_le_pow_left' hh 2
  have hsqrt (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simpa only [mul_pow, hsqrt] using hh2

/-- The squared Young L1--L2 estimate for the actual nonnegative convolution. -/
theorem lintegral_convolution_sq_le {f g : SobolevModel → ℝ≥0∞}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    (∫⁻ x, (∫⁻ y, f y * g (x - y)) ^ (2 : ℕ)) ≤
      (∫⁻ y, f y) ^ (2 : ℕ) * (∫⁻ x, g x ^ (2 : ℕ)) := by
  have hprod : AEMeasurable
      (fun z : SobolevModel × SobolevModel => f z.2 * g (z.1 - z.2) ^ (2 : ℕ))
      (volume.prod volume) :=
    hf.comp_snd.mul ((hg.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)).pow_const 2)
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, f y) * (∫⁻ y, f y * g (x - y) ^ (2 : ℕ)) := by
      apply lintegral_mono
      intro x
      exact lintegral_mul_sq_le hf (hg.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_left_of_right_invariant volume x))
    _ = (∫⁻ y, f y) * ∫⁻ x, ∫⁻ y, f y * g (x - y) ^ (2 : ℕ) :=
      lintegral_const_mul'' _ hprod.lintegral_prod_right'
    _ = (∫⁻ y, f y) * ∫⁻ y, ∫⁻ x, f y * g (x - y) ^ (2 : ℕ) := by
      rw [lintegral_lintegral_swap hprod]
    _ = (∫⁻ y, f y) * ∫⁻ y, f y * ∫⁻ x, g x ^ (2 : ℕ) := by
      congr 1
      apply lintegral_congr
      intro y
      have hgm : AEMeasurable (fun x => g (x - y) ^ (2 : ℕ)) volume :=
        (hg.comp_quasiMeasurePreserving
          (measurePreserving_sub_right volume y).quasiMeasurePreserving).pow_const 2
      rw [lintegral_const_mul'' _ hgm]
      congr 1
      exact lintegral_sub_right_eq_self (fun x => g x ^ (2 : ℕ)) y
    _ = _ := by
      rw [lintegral_mul_const'' _ hf]
      ring

theorem eLpNorm_two_sq (f : SobolevModel → ℂ) :
    (eLpNorm f 2 volume) ^ (2 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) := by
  simpa only [NNReal.coe_ofNat, ENNReal.rpow_two, ENNReal.coe_ofNat] using
    (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume)
      (by norm_num : (2 : ℝ≥0) ≠ 0))

/-- Young's inequality for the actual complex convolution in the original
Lp seminorms. No assumed Lp-valued integral or translation measurability is used. -/
theorem eLpNorm_convolution_one_two_le {f g : SobolevModel → ℂ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    eLpNorm (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) 2 volume ≤
      eLpNorm f 1 volume * eLpNorm g 2 volume := by
  apply (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp
  rw [eLpNorm_two_sq]
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, ‖f y‖ₑ * ‖g (x - y)‖ₑ) ^ (2 : ℕ) := by
      apply lintegral_mono
      intro x
      apply pow_le_pow_left'
      simpa only [convolution_def, ContinuousLinearMap.mul_apply', enorm_mul] using
        enorm_integral_le_lintegral_enorm (fun y => f y * g (x - y))
    _ ≤ (∫⁻ y, ‖f y‖ₑ) ^ (2 : ℕ) * (∫⁻ x, ‖g x‖ₑ ^ (2 : ℕ)) :=
      lintegral_convolution_sq_le hf.enorm hg.enorm
    _ = _ := by rw [mul_pow, eLpNorm_one_eq_lintegral_enorm, eLpNorm_two_sq]

end K24.Global.SobolevAlgebra


/- Reused source body: K24SOBYOUNG_Genuine.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16
open MeasureTheory FourierTransform Filter
open scoped ENNReal NNReal Convolution

namespace K24.Global.SobolevAlgebra

/-- The actual complex convolution is L2 for L1 and L2 inputs. Joint
measurability of its scalar integrand is established from the actual inputs. -/
theorem memLp_convolution_one_two {f g : SobolevModel → ℂ}
    (hf : MemLp f 1 volume) (hg : MemLp g 2 volume) :
    MemLp (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) 2 volume := by
  refine ⟨?_, ?_⟩
  · exact (hf.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.mul ℂ ℂ) hg.aestronglyMeasurable).integral_prod_right'
  · exact (eLpNorm_convolution_one_two_le hf.aestronglyMeasurable
      hg.aestronglyMeasurable).trans_lt (ENNReal.mul_lt_top hf.2 hg.2)

/-- The integral defining the convolution actually exists almost everywhere.
This rules out relying on the totalized value of a nonintegrable integral. -/
theorem convolutionExistsAt_one_two_ae {f g : SobolevModel → ℂ}
    (hf : MemLp f 1 volume) (hg : MemLp g 2 volume) :
    ∀ᵐ x ∂volume, ConvolutionExistsAt f g x (ContinuousLinearMap.mul ℂ ℂ) volume := by
  have hprod := hf.aestronglyMeasurable.convolution_integrand
    (ContinuousLinearMap.mul ℂ ℂ) hg.aestronglyMeasurable
  have hmeas : AEMeasurable
      (fun x : SobolevModel => (∫⁻ y, ‖f y‖ₑ * ‖g (x - y)‖ₑ) ^ (2 : ℕ)) volume := by
    have hh := hprod.enorm.lintegral_prod_right'
    simp only [ContinuousLinearMap.mul_apply', enorm_mul] at hh
    exact hh.pow_const 2
  have hfinite : (∫⁻ x, (∫⁻ y, ‖f y‖ₑ * ‖g (x - y)‖ₑ) ^ (2 : ℕ)) < ⊤ := by
    apply (lintegral_convolution_sq_le hf.aestronglyMeasurable.enorm
      hg.aestronglyMeasurable.enorm).trans_lt
    rw [← eLpNorm_one_eq_lintegral_enorm, ← eLpNorm_two_sq]
    exact ENNReal.mul_lt_top (by simpa only [ENNReal.pow_lt_top_iff] using Or.inl hf.2)
      (by simpa only [ENNReal.pow_lt_top_iff] using Or.inl hg.2)
  filter_upwards [ae_lt_top' hmeas hfinite.ne] with x hx
  refine ⟨hf.aestronglyMeasurable.convolution_integrand_snd
    (ContinuousLinearMap.mul ℂ ℂ) hg.aestronglyMeasurable x, ?_⟩
  have hx' : (∫⁻ y, ‖f y‖ₑ * ‖g (x - y)‖ₑ) < ⊤ := by
    simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hx
  simpa only [hasFiniteIntegral_iff_enorm, ContinuousLinearMap.mul_apply', enorm_mul] using hx'

/-- A genuine L2 representative of the convolution, with the exact Young
constant one in the original Lp seminorms and actual a.e. scalar equality. -/
theorem convolution_has_L2_representative {f g : SobolevModel → ℂ}
    (hf : MemLp f 1 volume) (hg : MemLp g 2 volume) :
    ∃ v : LocalL2,
      (v : SobolevModel → ℂ) =ᵐ[volume] (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ∧
      ENNReal.ofReal ‖v‖ ≤ eLpNorm f 1 volume * eLpNorm g 2 volume ∧
      ∀ᵐ x ∂volume, ConvolutionExistsAt f g x (ContinuousLinearMap.mul ℂ ℂ) volume := by
  let h := memLp_convolution_one_two hf hg
  refine ⟨h.toLp _, h.coeFn_toLp, ?_, convolutionExistsAt_one_two_ae hf hg⟩
  rw [ofReal_norm, Lp.enorm_toLp]
  exact eLpNorm_convolution_one_two_le hf.aestronglyMeasurable hg.aestronglyMeasurable

end K24.Global.SobolevAlgebra


/- Reused source body: K24SOBYOUNG_ENN.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped ENNReal NNReal Convolution

namespace K24.Global.SobolevAlgebra

theorem enn_sqrt_sq (a : ℝ≥0∞) : (a ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem eLpNorm_two_eq_lintegral_sq (f : SobolevModel → ℂ) :
    eLpNorm f 2 volume = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  rw [← eLpNorm_two_sq, enn_sqrt_sq]

theorem enn_convolution_comm (f g : SobolevModel → ℝ≥0∞) (x : SobolevModel) :
    (∫⁻ y, f y * g (x - y)) = ∫⁻ y, g y * f (x - y) := by
  rw [← lintegral_sub_left_eq_self (fun y => f y * g (x - y)) x]
  simp only [sub_sub_cancel, mul_comm]

/-- Square-root form of the actual nonnegative Young bound. -/
theorem lintegral_convolution_l2_le {f g : SobolevModel → ℝ≥0∞}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    (∫⁻ x, (∫⁻ y, f y * g (x - y)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤
      (∫⁻ y, f y) * (∫⁻ x, g x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  have hh := ENNReal.rpow_le_rpow (lintegral_convolution_sq_le hf hg)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), enn_sqrt_sq] at hh

theorem lintegral_l2_add_le {f g : SobolevModel → ℝ≥0∞}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    (∫⁻ x, (f x + g x) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤
      (∫⁻ x, f x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) +
      (∫⁻ x, g x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  simpa only [Pi.add_apply, ENNReal.rpow_two] using
    (ENNReal.lintegral_Lp_add_le hf hg (by norm_num : (1 : ℝ) ≤ 2))

theorem lintegral_l2_const_mul (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (f : SobolevModel → ℝ≥0∞) :
    (∫⁻ x, (c * f x) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) =
      c * (∫⁻ x, f x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  simp_rw [mul_pow]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hc),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), enn_sqrt_sq]

theorem aemeasurable_enn_convolution {f g : SobolevModel → ℝ≥0∞}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    AEMeasurable (fun x => ∫⁻ y, f y * g (x - y)) volume := by
  have hh : AEMeasurable (fun z : SobolevModel × SobolevModel => f z.2 * g (z.1 - z.2))
      (volume.prod volume) :=
    hf.comp_snd.mul (hg.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  exact hh.lintegral_prod_right'

end K24.Global.SobolevAlgebra


/- Reused source body: K24SOBYOUNG_Weighted.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16
open MeasureTheory FourierTransform Filter
open scoped ENNReal NNReal Convolution

namespace K24.Global.SobolevAlgebra

theorem enorm_besselWeight_mul (r : ℝ) (f : SobolevModel → ℂ) (x : SobolevModel) :
    ‖(besselWeight r x : ℂ) * f x‖ₑ = ENNReal.ofReal (besselWeight r x) * ‖f x‖ₑ := by
  rw [enorm_mul]
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (besselWeight_nonneg r x)]

/-- The exact real-order Peetre inequality bounds the actual weighted
convolution pointwise by two nonnegative convolutions. -/
theorem enorm_besselWeight_convolution_le (r : ℝ) (hr : 0 ≤ r)
    {f g : SobolevModel → ℂ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (x : SobolevModel) :
    ‖(besselWeight r x : ℂ) * (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖ₑ ≤
      ENNReal.ofReal ((4 : ℝ) ^ (r / 2)) *
        ((∫⁻ y, ‖(besselWeight r y : ℂ) * f y‖ₑ * ‖g (x - y)‖ₑ) +
         (∫⁻ y, ‖f y‖ₑ * ‖(besselWeight r (x - y) : ℂ) * g (x - y)‖ₑ)) := by
  have hWf : AEStronglyMeasurable (fun y => (besselWeight r y : ℂ) * f y) volume :=
    (Complex.continuous_ofReal.comp (besselWeight_continuous r)).aestronglyMeasurable.mul hf
  have hleft : AEMeasurable
      (fun y => ‖(besselWeight r y : ℂ) * f y‖ₑ * ‖g (x - y)‖ₑ) volume :=
    hWf.enorm.mul (hg.enorm.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_left_of_right_invariant volume x))
  rw [enorm_besselWeight_mul]
  calc
    _ ≤ ENNReal.ofReal (besselWeight r x) * (∫⁻ y, ‖f y‖ₑ * ‖g (x - y)‖ₑ) := by
      apply mul_le_mul (le_refl _) ?_ bot_le bot_le
      simpa only [convolution_def, ContinuousLinearMap.mul_apply', enorm_mul] using
        enorm_integral_le_lintegral_enorm (fun y => f y * g (x - y))
    _ = ∫⁻ y, ENNReal.ofReal (besselWeight r x) * (‖f y‖ₑ * ‖g (x - y)‖ₑ) :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal ((4 : ℝ) ^ (r / 2)) *
        (‖(besselWeight r y : ℂ) * f y‖ₑ * ‖g (x - y)‖ₑ +
          ‖f y‖ₑ * ‖(besselWeight r (x - y) : ℂ) * g (x - y)‖ₑ) := by
      apply lintegral_mono
      intro y
      have hw : ENNReal.ofReal (besselWeight r x) ≤ ENNReal.ofReal ((4 : ℝ) ^ (r / 2)) *
          (ENNReal.ofReal (besselWeight r y) + ENNReal.ofReal (besselWeight r (x - y))) := by
        simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 ^ (r / 2)),
          ENNReal.ofReal_add (besselWeight_nonneg r y) (besselWeight_nonneg r (x - y))] using
          ENNReal.ofReal_le_ofReal (besselWeight_sub_le r hr x y)
      calc
        _ ≤ (ENNReal.ofReal ((4 : ℝ) ^ (r / 2)) *
            (ENNReal.ofReal (besselWeight r y) + ENNReal.ofReal (besselWeight r (x - y)))) *
            (‖f y‖ₑ * ‖g (x - y)‖ₑ) := mul_le_mul hw (le_refl _) bot_le bot_le
        _ = _ := by simp only [enorm_besselWeight_mul]; ring
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hleft]

/-- Weighted Young for the canonical real-order Bessel weight. The sole
constant is the checked Peetre constant; no rounding of the order occurs. -/
theorem eLpNorm_besselWeight_convolution_le (r : ℝ) (hr : 0 ≤ r)
    {f g : SobolevModel → ℂ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    eLpNorm (fun x => (besselWeight r x : ℂ) *
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x) 2 volume ≤
      ENNReal.ofReal ((4 : ℝ) ^ (r / 2)) *
        (eLpNorm (fun x => (besselWeight r x : ℂ) * f x) 2 volume * eLpNorm g 1 volume +
          eLpNorm f 1 volume * eLpNorm (fun x => (besselWeight r x : ℂ) * g x) 2 volume) := by
  let F : SobolevModel → ℂ := fun x => (besselWeight r x : ℂ) * f x
  let G : SobolevModel → ℂ := fun x => (besselWeight r x : ℂ) * g x
  let A : SobolevModel → ℝ≥0∞ := fun x => ∫⁻ y, ‖F y‖ₑ * ‖g (x - y)‖ₑ
  let B : SobolevModel → ℝ≥0∞ := fun x => ∫⁻ y, ‖f y‖ₑ * ‖G (x - y)‖ₑ
  let c : ℝ≥0∞ := ENNReal.ofReal ((4 : ℝ) ^ (r / 2))
  have hF : AEStronglyMeasurable F volume :=
    (Complex.continuous_ofReal.comp (besselWeight_continuous r)).aestronglyMeasurable.mul hf
  have hG : AEStronglyMeasurable G volume :=
    (Complex.continuous_ofReal.comp (besselWeight_continuous r)).aestronglyMeasurable.mul hg
  have hA : AEMeasurable A volume := aemeasurable_enn_convolution hF.enorm hg.enorm
  have hB : AEMeasurable B volume := aemeasurable_enn_convolution hf.enorm hG.enorm
  have hAbound : (∫⁻ x, A x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤
      eLpNorm F 2 volume * eLpNorm g 1 volume := by
    have heq : A = fun x => ∫⁻ y, ‖g y‖ₑ * ‖F (x - y)‖ₑ := by
      funext x
      exact enn_convolution_comm (fun y => ‖F y‖ₑ) (fun y => ‖g y‖ₑ) x
    rw [heq]
    have hh := lintegral_convolution_l2_le hg.enorm hF.enorm
    simpa only [← eLpNorm_one_eq_lintegral_enorm, ← eLpNorm_two_eq_lintegral_sq, mul_comm]
      using hh
  have hBbound : (∫⁻ x, B x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤
      eLpNorm f 1 volume * eLpNorm G 2 volume := by
    have hh := lintegral_convolution_l2_le hf.enorm hG.enorm
    simpa only [← eLpNorm_one_eq_lintegral_enorm, ← eLpNorm_two_eq_lintegral_sq] using hh
  rw [eLpNorm_two_eq_lintegral_sq]
  calc
    _ ≤ (∫⁻ x, (c * (A x + B x)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply lintegral_mono
      intro x
      exact pow_le_pow_left' (enorm_besselWeight_convolution_le r hr hf hg x) 2
    _ = c * (∫⁻ x, (A x + B x) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) :=
      lintegral_l2_const_mul c ENNReal.ofReal_ne_top (fun x => A x + B x)
    _ ≤ c * ((∫⁻ x, A x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) +
        (∫⁻ x, B x ^ (2 : ℕ)) ^ (1 / 2 : ℝ)) :=
      mul_le_mul (le_refl c) (lintegral_l2_add_le hA hB) bot_le bot_le
    _ ≤ _ := mul_le_mul (le_refl c) (add_le_add hAbound hBbound) bot_le bot_le

end K24.Global.SobolevAlgebra


/- Reused source body: K24SOBALG_Algebra.lean. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory FourierTransform TemperedDistribution
open scoped ENNReal NNReal SchwartzMap Convolution BoundedContinuousFunction

namespace K24.Global.SobolevAlgebra

/-- Algebra estimate for faithful bounded continuous realizations of the exact
Bessel spaces in dimension four, for every real order above two. -/
theorem bessel_boundedContinuous_algebra (r : ℝ) (hr : 2 < r) :
    ∃ A : ℝ≥0, ∀ F G : SobolevModel →ᵇ ℂ,
      BesselMem r (boundedContinuousDistribution F) →
      BesselMem r (boundedContinuousDistribution G) →
      BesselMem r (boundedContinuousDistribution (F * G)) ∧
        besselSobolevENN r (boundedContinuousDistribution (F * G)) ≤
          (A : ℝ≥0∞) * besselSobolevENN r (boundedContinuousDistribution F) *
            besselSobolevENN r (boundedContinuousDistribution G) := by
  obtain ⟨A, hA⟩ := bessel_fourier_weighted_representative r hr
  let C : ℝ≥0 := ⟨(4 : ℝ) ^ (r / 2), by positivity⟩
  refine ⟨2 * C * A, fun F G hF hG => ?_⟩
  obtain ⟨v, hv, hv2, hvnorm, hv1⟩ := hA _ hF
  obtain ⟨w, hw, hw2, hwnorm, hw1⟩ := hA _ hG
  have hFv : Real.Lp.fourierTransformInv v = F := by
    apply SobolevGlobal.boundedContinuousDistribution_injective
    rw [inverseFourierL1_distribution, ← hv, fourierInv_fourier_eq]
  have hGw : Real.Lp.fourierTransformInv w = G := by
    apply SobolevGlobal.boundedContinuousDistribution_injective
    rw [inverseFourierL1_distribution, ← hw, fourierInv_fourier_eq]
  obtain ⟨hc, hcDist⟩ := inverseFourierL1_convolution_distribution v w
  rw [hFv, hGw] at hcDist
  let c : SobolevModel → ℂ := (v : SobolevModel → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ]
    (w : SobolevModel → ℂ)
  have hbound : eLpNorm (fun x => (besselWeight r x : ℂ) * c x) 2 volume ≤
      ((2 * C * A : ℝ≥0) : ℝ≥0∞) *
        besselSobolevENN r (boundedContinuousDistribution F) *
        besselSobolevENN r (boundedContinuousDistribution G) := by
    calc
      _ ≤ ENNReal.ofReal ((4 : ℝ) ^ (r / 2)) *
          (eLpNorm (fun x => (besselWeight r x : ℂ) * v x) 2 volume *
              eLpNorm w 1 volume + eLpNorm v 1 volume *
                eLpNorm (fun x => (besselWeight r x : ℂ) * w x) 2 volume) :=
        eLpNorm_besselWeight_convolution_le r (by linarith)
          (Lp.memLp v).aestronglyMeasurable (Lp.memLp w).aestronglyMeasurable
      _ ≤ (C : ℝ≥0∞) *
          (besselSobolevENN r (boundedContinuousDistribution F) *
              ((A : ℝ≥0∞) * besselSobolevENN r (boundedContinuousDistribution G)) +
            ((A : ℝ≥0∞) * besselSobolevENN r (boundedContinuousDistribution F)) *
              besselSobolevENN r (boundedContinuousDistribution G)) := by
        have hC : ENNReal.ofReal ((4 : ℝ) ^ (r / 2)) = (C : ℝ≥0∞) :=
          by exact ENNReal.ofReal_coe_nnreal (p := C)
        rw [hC, hvnorm, hwnorm]
        exact mul_le_mul le_rfl
          (add_le_add (mul_le_mul le_rfl hw1 bot_le bot_le)
            (mul_le_mul hv1 le_rfl bot_le bot_le)) bot_le bot_le
      _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]; ring
  have hfin : ((2 * C * A : ℝ≥0) : ℝ≥0∞) *
        besselSobolevENN r (boundedContinuousDistribution F) *
        besselSobolevENN r (boundedContinuousDistribution G) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((besselSobolevENN_lt_top_iff _ _).mpr hF))
      ((besselSobolevENN_lt_top_iff _ _).mpr hG)
  have hcw : MemLp (fun x => (besselWeight r x : ℂ) * c x) 2 volume :=
    ⟨(Complex.continuous_ofReal.comp (besselWeight_continuous r)).aestronglyMeasurable.mul
      hc.aestronglyMeasurable, hbound.trans_lt hfin⟩
  obtain ⟨hmem, hnorm⟩ := bessel_inverseFourier_norm hc hcw
  rw [← hcDist] at hmem hnorm
  exact ⟨hmem, hnorm.trans_le hbound⟩

/-- The exact real-order local Sobolev space in dimension four is an algebra
for every real r > 2, with one finite constant depending only on r. -/
theorem localSobolev_algebra (r : ℝ) (hr : 2 < r) :
    ∃ A : ℝ≥0, ∀ f g : SobolevModel → ℝ,
      LocalSobolevMem r f → LocalSobolevMem r g →
      LocalSobolevMem r (f * g) ∧
        localSobolevENN r (f * g) ≤
          (A : ℝ≥0∞) * localSobolevENN r f * localSobolevENN r g := by
  obtain ⟨A, hA⟩ := bessel_boundedContinuous_algebra r hr
  refine ⟨A, fun f g hf hg => ?_⟩
  obtain ⟨F, hFae, hF2, hF, hFnorm⟩ := localSobolev_boundedContinuous_realization hr hf
  obtain ⟨G, hGae, hG2, hG, hGnorm⟩ := localSobolev_boundedContinuous_realization hr hg
  obtain ⟨hFG, hFGbound⟩ := hA F G hF hG
  obtain ⟨hfg, hfgnorm⟩ := localSobolev_product_descent F G hFae hGae hG2 hFG
  refine ⟨hfg, ?_⟩
  rw [hfgnorm]
  simpa only [hFnorm, hGnorm] using hFGbound

end K24.Global.SobolevAlgebra

/- Source: K24SOBCUTOFF_Decay.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff

namespace K24.Global.SobolevCutoff

private theorem norm_iteratedFDeriv_le_of_derivativeENorm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SobolevModel → F) (n : ℕ) (B : ℝ≥0)
    (hb : derivativeENorm n Set.univ f ≤ (B : ℝ≥0∞)) (x : SobolevModel) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (B : ℝ) := by
  have hh : (‖iteratedFDerivWithin ℝ n f Set.univ x‖₊ : ℝ≥0∞) ≤ (B : ℝ≥0∞) :=
    (le_iSup (fun y : (Set.univ : Set SobolevModel) =>
      (‖iteratedFDerivWithin ℝ n f Set.univ y‖₊ : ℝ≥0∞)) ⟨x, Set.mem_univ x⟩).trans hb
  rw [iteratedFDerivWithin_univ] at hh
  exact_mod_cast hh

/-- Every derivative integral is controlled by the original derivative bound
and the volume of the fixed-radius support ball, independently of its center. -/
private theorem derivative_integral_bound (f : SobolevModel → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : SobolevModel) (R : ℝ) (hsupp : tsupport f ⊆ Metric.ball c R)
    (n : ℕ) (B : ℝ≥0) (hb : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ (B : ℝ)) :
    (∫ x, ‖iteratedFDeriv ℝ n f x‖) ≤
      (B : ℝ) * (volume (Metric.ball (0 : SobolevModel) R)).toReal := by
  have hcont : Continuous (iteratedFDeriv ℝ n f) :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hint : Integrable (fun x => ‖iteratedFDeriv ℝ n f x‖) :=
    (hcont.integrable_of_hasCompactSupport (hc.iteratedFDeriv n)).norm
  have hconst : Integrable ((Metric.ball c R).indicator (fun _ : SobolevModel => (B : ℝ))) := by
    have hh : IntegrableOn (fun _ : SobolevModel => (B : ℝ)) (Metric.ball c R) :=
      integrableOn_const (measure_ball_lt_top.ne)
    exact (integrable_indicator_iff measurableSet_ball).mpr hh
  have hpoint (x : SobolevModel) : ‖iteratedFDeriv ℝ n f x‖ ≤
      (Metric.ball c R).indicator (fun _ : SobolevModel => (B : ℝ)) x := by
    by_cases hx : x ∈ Metric.ball c R
    · simpa only [Set.indicator_of_mem hx] using hb x
    · rw [Set.indicator_of_notMem hx]
      have hz : iteratedFDeriv ℝ n f x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro ht
        exact hx (hsupp (tsupport_iteratedFDeriv_subset n ht))
      simp only [hz, norm_zero, le_refl]
  calc
    _ ≤ ∫ x, (Metric.ball c R).indicator (fun _ : SobolevModel => (B : ℝ)) x :=
      integral_mono hint hconst hpoint
    _ = _ := by
      rw [integral_indicator_const _ measurableSet_ball]
      simp only [smul_eq_mul, measureReal_def, Measure.addHaar_ball_center, mul_comm]

/-- The exact Fourier integral has controlled polynomial decay from the
original uniform derivative and compact support data. -/
private theorem fourier_decay_bound (f : SobolevModel → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : SobolevModel) (R : ℝ) (hsupp : tsupport f ⊆ Metric.ball c R)
    (m : ℕ) (B : ℝ≥0)
    (hb : ∀ n ≤ m, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ (B : ℝ))
    (ξ : SobolevModel) :
    ‖ξ‖ ^ m * ‖𝓕 f ξ‖ ≤
      (2 : ℝ) ^ m * (m + 1) * (B : ℝ) *
        (volume (Metric.ball (0 : SobolevModel) R)).toReal := by
  have hint (k n : ℕ) (_hk : k ≤ (0 : ℕ∞)) (_hn : n ≤ (m : ℕ∞)) :
      Integrable (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
    have hk : k = 0 := by exact_mod_cast (show (k : ℕ∞) = 0 from le_antisymm _hk bot_le)
    subst k
    simpa only [pow_zero, one_mul] using
      ((hf.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).integrable_of_hasCompactSupport
        (hc.iteratedFDeriv n)).norm
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (K := 0) (N := (m : ℕ∞)) (hf.of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))) hint
    (k := 0) (n := m) (by simp) (by simp) ξ
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, zero_add] at h
  have hs : ∑ p ∈ Finset.range 1 ×ˢ Finset.range (m + 1),
      ∫ x : SobolevModel, ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f x‖ ≤
      (m + 1) * ((B : ℝ) * (volume (Metric.ball (0 : SobolevModel) R)).toReal) := by
    calc
      _ ≤ ∑ p ∈ Finset.range 1 ×ˢ Finset.range (m + 1),
          (B : ℝ) * (volume (Metric.ball (0 : SobolevModel) R)).toReal := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : p.1 = 0 := by
          have := (Finset.mem_product.mp hp).1
          simpa only [Finset.mem_range, Nat.lt_one_iff] using this
        have hpm : p.2 ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp
          (Finset.mem_product.mp hp).2)
        simp only [hp0, pow_zero, one_mul]
        exact derivative_integral_bound f hf hc c R hsupp p.2 B (hb p.2 hpm)
      _ = _ := by simp
  have h' := mul_le_mul_of_nonneg_left hs (show 0 ≤ (2 : ℝ) ^ m by positivity)
  apply le_trans h
  convert h' using 1 <;> ring

private def decayConstant (m : ℕ) (R : ℝ) : ℝ :=
  (2 : ℝ) ^ ((m : ℝ) / 2) * (1 + (2 : ℝ) ^ m * (m + 1)) *
    (volume (Metric.ball (0 : SobolevModel) R)).toReal

private theorem decayConstant_nonneg (m : ℕ) (R : ℝ) : 0 ≤ decayConstant m R := by
  unfold decayConstant
  positivity

private theorem besselWeight_nat_le (m : ℕ) (ξ : SobolevModel) :
    SobolevAlgebra.besselWeight m ξ ≤
      (2 : ℝ) ^ ((m : ℝ) / 2) * (1 + ‖ξ‖ ^ m) := by
  have hp : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
  have heq : (‖ξ‖ ^ 2) ^ ((m : ℝ) / 2) = ‖ξ‖ ^ m := by
    rw [← Real.rpow_natCast ‖ξ‖ 2, ← Real.rpow_mul (norm_nonneg ξ)]
    convert Real.rpow_natCast ‖ξ‖ m using 1 <;> ring
  unfold SobolevAlgebra.besselWeight
  by_cases hn : ‖ξ‖ ≤ 1
  · have hbase : 1 + ‖ξ‖ ^ 2 ≤ 2 := by nlinarith [norm_nonneg ξ]
    exact (Real.rpow_le_rpow (by positivity) hbase hp).trans
      (le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg (norm_nonneg ξ) m]))
  · have hbase : 1 + ‖ξ‖ ^ 2 ≤ 2 * ‖ξ‖ ^ 2 := by nlinarith [norm_nonneg ξ]
    calc
      _ ≤ (2 * ‖ξ‖ ^ 2) ^ ((m : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) hbase hp
      _ = (2 : ℝ) ^ ((m : ℝ) / 2) * ‖ξ‖ ^ m := by
        rw [Real.mul_rpow (by positivity) (by positivity), heq]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- A bound for the exact integer Bessel weight of the Fourier transform,
used only as an intermediate estimate before the real-order conclusion. -/
private theorem weighted_fourier_point_bound (f : SobolevModel → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : SobolevModel) (R : ℝ) (hsupp : tsupport f ⊆ Metric.ball c R)
    (m : ℕ) (B : ℝ≥0)
    (hb : ∀ n ≤ m, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ (B : ℝ))
    (ξ : SobolevModel) :
    SobolevAlgebra.besselWeight m ξ * ‖𝓕 f ξ‖ ≤ decayConstant m R * (B : ℝ) := by
  have hzero := fourier_decay_bound f hf hc c R hsupp 0 B
    (fun n hn => hb n (hn.trans (Nat.zero_le m))) ξ
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, mul_one] at hzero
  have hm := fourier_decay_bound f hf hc c R hsupp m B hb ξ
  calc
    _ ≤ ((2 : ℝ) ^ ((m : ℝ) / 2) * (1 + ‖ξ‖ ^ m)) * ‖𝓕 f ξ‖ :=
      mul_le_mul_of_nonneg_right (besselWeight_nat_le m ξ) (norm_nonneg _)
    _ = (2 : ℝ) ^ ((m : ℝ) / 2) * (‖𝓕 f ξ‖ + ‖ξ‖ ^ m * ‖𝓕 f ξ‖) := by ring
    _ ≤ (2 : ℝ) ^ ((m : ℝ) / 2) *
        ((B : ℝ) * (volume (Metric.ball (0 : SobolevModel) R)).toReal +
        (2 : ℝ) ^ m * (m + 1) * (B : ℝ) *
          (volume (Metric.ball (0 : SobolevModel) R)).toReal) :=
      mul_le_mul_of_nonneg_left (add_le_add hzero hm) (by positivity)
    _ = _ := by unfold decayConstant; ring

end K24.Global.SobolevCutoff


/- Source: K24SOBCUTOFF_Bessel.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory FourierTransform TemperedDistribution Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff

namespace K24.Global.SobolevCutoff
open SobolevAlgebra

private theorem schwartz_bessel_norm_eq_weighted (r : ℝ) (φ : 𝓢(SobolevModel, ℂ)) :
    besselSobolevENN r (φ : LocalDistribution) =
      eLpNorm (fun ξ => (besselWeight r ξ : ℂ) * 𝓕 φ ξ) 2 volume := by
  have hw : MemLp (fun ξ => (besselWeight r ξ : ℂ) * 𝓕 φ ξ) 2 volume := by
    let ψ := SchwartzMap.smulLeftCLM ℂ (fun ξ => (besselWeight r ξ : ℂ)) (𝓕 φ)
    have heq : (ψ : SobolevModel → ℂ) = fun ξ => (besselWeight r ξ : ℂ) * 𝓕 φ ξ := by
      ext ξ
      exact SchwartzMap.smulLeftCLM_apply_apply
        (by unfold besselWeight; fun_prop) _ _
    rw [← heq]
    exact ψ.memLp 2 volume
  have hint : Integrable ((𝓕 φ : 𝓢(SobolevModel, ℂ)) : SobolevModel → ℂ) :=
    (𝓕 φ).integrable
  have hh := bessel_inverseFourier_norm hint hw
  have heq : (((memLp_one_iff_integrable.mpr hint).toLp
      ((𝓕 φ : 𝓢(SobolevModel, ℂ)) : SobolevModel → ℂ) : Lp ℂ 1 volume) : LocalDistribution) =
        ((𝓕 φ : 𝓢(SobolevModel, ℂ)) : LocalDistribution) := by
    change (((𝓕 φ).toLp 1 volume : Lp ℂ 1 volume) : LocalDistribution) = _
    exact Lp.toTemperedDistribution_toLp_eq _
  rw [heq, ← fourier_toTemperedDistributionCLM_eq, fourierInv_fourier_eq] at hh
  exact hh.2

private theorem weight_split_decay {r : ℝ} {m : ℕ} (hrm : r + 3 ≤ (m : ℝ))
    (ξ : SobolevModel) :
    besselWeight r ξ ≤ besselWeight m ξ * ‖besselDecay 3 ξ‖ := by
  have hweight : besselWeight (r + 3) ξ ≤ besselWeight m ξ := by
    unfold besselWeight
    exact Real.rpow_le_rpow_of_exponent_le (by simp) (by linarith)
  have heq : besselWeight r ξ = besselWeight (r + 3) ξ * ‖besselDecay 3 ξ‖ := by
    simp only [besselWeight, besselDecay, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity), ← Real.rpow_add (by positivity)]
    congr 1
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hweight (norm_nonneg _)

/-- The radius/derivative constant is finite and independent of chart centers.
Only the final Sobolev order is real; the integer `m` records the original
available cutoff derivatives. -/
private def cutoffConstant (m : ℕ) (R : ℝ) : ℝ≥0 :=
  ⟨decayConstant m R * (eLpNorm (besselDecay 3) 2 volume).toReal,
    mul_nonneg (decayConstant_nonneg m R) ENNReal.toReal_nonneg⟩

private theorem compact_localSobolev_bound (f : SobolevModel → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : SobolevModel) (R : ℝ) (hsupp : tsupport f ⊆ Metric.ball c R)
    (m : ℕ) (B : ℝ≥0)
    (hb : ∀ n ≤ m, derivativeENorm n Set.univ f ≤ (B : ℝ≥0∞))
    (r : ℝ) (hrm : r + 3 ≤ (m : ℝ)) :
    LocalSobolevMem r f ∧ localSobolevENN r f ≤
      (cutoffConstant m R : ℝ≥0∞) * (B : ℝ≥0∞) := by
  have hfc : ContDiff ℝ ∞ (complexifyLocal f) := Complex.ofRealCLM.contDiff.comp hf
  have hcc : HasCompactSupport (complexifyLocal f) := hc.comp_left rfl
  have hsuppc : tsupport (complexifyLocal f) ⊆ Metric.ball c R := by
    have heq : Function.support (complexifyLocal f) = Function.support f := by
      ext x
      simp [Function.mem_support, complexifyLocal]
    simpa only [tsupport, heq] using hsupp
  let φ : 𝓢(SobolevModel, ℂ) := hcc.toSchwartzMap hfc
  have hφ : (φ : SobolevModel → ℂ) = complexifyLocal f := rfl
  have hbcomplex (n : ℕ) (hn : n ≤ m) (x : SobolevModel) :
      ‖iteratedFDeriv ℝ n (complexifyLocal f) x‖ ≤ (B : ℝ) := by
    have heq := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (x := x) hf.contDiffAt
      (show (n : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    change ‖iteratedFDeriv ℝ n (complexifyLocal f) x‖ = ‖iteratedFDeriv ℝ n f x‖ at heq
    rw [heq]
    exact norm_iteratedFDeriv_le_of_derivativeENorm f n B (hb n hn) x
  have hpoint (ξ : SobolevModel) :
      ‖(besselWeight r ξ : ℂ) * 𝓕 φ ξ‖ ≤
        ‖(decayConstant m R * (B : ℝ)) • besselDecay 3 ξ‖ := by
    have hbound := weighted_fourier_point_bound (complexifyLocal f) hfc hcc c R hsuppc
      m B hbcomplex ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (besselWeight_nonneg r ξ), norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (decayConstant_nonneg m R) B.coe_nonneg)]
    calc
      besselWeight r ξ * ‖𝓕 φ ξ‖ ≤
          (besselWeight m ξ * ‖besselDecay 3 ξ‖) * ‖𝓕 φ ξ‖ :=
        mul_le_mul_of_nonneg_right (weight_split_decay hrm ξ) (norm_nonneg _)
      _ = (besselWeight m ξ * ‖𝓕 φ ξ‖) * ‖besselDecay 3 ξ‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
  have hd := besselDecay_memLp_two (by norm_num : (2 : ℝ) < 3)
  have hnorm : eLpNorm (fun ξ => (besselWeight r ξ : ℂ) * 𝓕 φ ξ) 2 volume ≤
      (cutoffConstant m R : ℝ≥0∞) * (B : ℝ≥0∞) := by
    calc
      _ ≤ eLpNorm ((decayConstant m R * (B : ℝ)) • besselDecay 3) 2 volume :=
        eLpNorm_mono hpoint
      _ = _ := by
        rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (decayConstant_nonneg m R) B.coe_nonneg),
          ENNReal.ofReal_mul (decayConstant_nonneg m R)]
        rw [← show ENNReal.ofReal ((cutoffConstant m R : ℝ≥0) : ℝ) =
          (cutoffConstant m R : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal]
        change ENNReal.ofReal (decayConstant m R) * ENNReal.ofReal (B : ℝ) *
            eLpNorm (besselDecay 3) 2 volume =
          ENNReal.ofReal (decayConstant m R * (eLpNorm (besselDecay 3) 2 volume).toReal) *
            (B : ℝ≥0∞)
        rw [ENNReal.ofReal_mul (decayConstant_nonneg m R),
          ENNReal.ofReal_toReal hd.2.ne, ENNReal.ofReal_coe_nnreal]
        ring
  have hfl : MemLp (complexifyLocal f) 2 volume := φ.memLp 2 volume
  have hdist : localFunctionDistribution f hfl = (φ : LocalDistribution) := by
    change ((φ.toLp 2 volume : LocalL2) : LocalDistribution) = _
    exact Lp.toTemperedDistribution_toLp_eq φ
  have hmem : BesselMem r (localFunctionDistribution f hfl) := by
    rw [hdist]
    exact φ.memSobolev
  refine ⟨⟨hfl, hmem⟩, ?_⟩
  rw [localSobolevENN, dif_pos hfl, hdist, schwartz_bessel_norm_eq_weighted]
  exact hnorm

end K24.Global.SobolevCutoff


/- Source: K24SOBCUTOFF_Multiplier.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped NNReal ENNReal Topology ContDiff Manifold

namespace K24.Global.SobolevCutoff

/-- The original `Bcut`, radius, and derivative-order hypotheses imply a
genuine real-order multiplier estimate, with its constant chosen before the
function, support-ball center, and derivative bound. -/
private theorem compact_multiplier (r : ℝ) (hr : 2 < r) (m : ℕ)
    (hrm : r + 3 ≤ (m : ℝ)) (R : ℝ) :
    ∃ K : ℝ≥0, ∀ (χ : SobolevModel → ℝ),
      ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∃ c : SobolevModel, tsupport χ ⊆ Metric.ball c R) →
      ∀ B : ℝ≥0,
        (∀ n ≤ m, derivativeENorm n Set.univ χ ≤ (B : ℝ≥0∞)) →
        ∀ f : SobolevModel → ℝ, LocalSobolevMem r f →
          LocalSobolevMem r (χ * f) ∧ localSobolevENN r (χ * f) ≤
            (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN r f := by
  obtain ⟨A, hA⟩ := SobolevAlgebra.localSobolev_algebra r hr
  refine ⟨A * cutoffConstant m R, fun χ hχ hc hsupp B hb f hf => ?_⟩
  obtain ⟨c, hc⟩ := hsupp
  obtain ⟨hχr, hχbound⟩ := compact_localSobolev_bound χ hχ ‹HasCompactSupport χ›
    c R hc m B hb r hrm
  obtain ⟨hmem, hbound⟩ := hA χ f hχr hf
  refine ⟨hmem, hbound.trans ?_⟩
  calc
    _ ≤ (A : ℝ≥0∞) * ((cutoffConstant m R : ℝ≥0∞) * (B : ℝ≥0∞)) *
        localSobolevENN r f := by gcongr
    _ = _ := by simp only [ENNReal.coe_mul]; ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable {C : BoundedLocalCover M}

/-- No support-size premise is added: the actual partition cutoff support
and the original cover's uniform outer radius supply it. -/
private theorem partition_cutoff_bound (P : SobolevPartition C) (m : ℕ) (B : ℝ≥0)
    (hb : P.CutoffDerivativeBounds m B) (r : ℝ) (hrm : r + 3 ≤ (m : ℝ))
    (ν : C.Index) :
    LocalSobolevMem r (P.cutoff ν) ∧ localSobolevENN r (P.cutoff ν) ≤
      (cutoffConstant m C.numerics.outerRadius : ℝ≥0∞) * (B : ℝ≥0∞) := by
  obtain ⟨c, hc⟩ := C.uniformOuterRadius ν.1 ν.2
  exact compact_localSobolev_bound (P.cutoff ν) (P.cutoffSmooth ν) (P.cutoffCompact ν)
    c C.numerics.outerRadius ((P.cutoffSupport ν).trans hc) m B (hb ν) r hrm

/-- The original collar localizers satisfy the identical quantitative bound. -/
private theorem localizer_cutoff_bound (L : SobolevLocalizers C) (m : ℕ) (B : ℝ≥0)
    (hb : L.DerivativeBounds m B) (r : ℝ) (hrm : r + 3 ≤ (m : ℝ))
    (ν : C.Index) :
    LocalSobolevMem r (L.cutoff ν) ∧ localSobolevENN r (L.cutoff ν) ≤
      (cutoffConstant m C.numerics.outerRadius : ℝ≥0∞) * (B : ℝ≥0∞) := by
  obtain ⟨c, hc⟩ := C.uniformOuterRadius ν.1 ν.2
  exact compact_localSobolev_bound (L.cutoff ν) (L.smooth ν) (L.compactSupport ν)
    c C.numerics.outerRadius ((L.support ν).trans hc) m B (hb ν) r hrm

universe u

/-- Uniform actual partition and collar localization at every real order
`r>2` with `r+3≤m`. The constant precedes every manifold, cover, and cutoff. -/
private theorem uniform_original_cutoff_multiplier (r : ℝ) (hr : 2 < r) (m : ℕ)
    (hrm : r + 3 ≤ (m : ℝ)) (R : ℝ) :
    ∃ K : ℝ≥0,
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
        (C : BoundedLocalCover M), C.numerics.outerRadius = R →
        ∀ (P : SobolevPartition C) (L : SobolevLocalizers C) (B : ℝ≥0),
          P.CutoffDerivativeBounds m B → L.DerivativeBounds m B →
          ∀ (ν : C.Index) (f : SobolevModel → ℝ), LocalSobolevMem r f →
            (LocalSobolevMem r (P.localize ν f) ∧
              localSobolevENN r (P.localize ν f) ≤
                (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN r f) ∧
            (LocalSobolevMem r (L.cutoff ν * f) ∧
              localSobolevENN r (L.cutoff ν * f) ≤
                (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN r f) := by
  obtain ⟨K, hK⟩ := compact_multiplier r hr m hrm R
  refine ⟨K, fun M _ _ C hR P L B hP hL ν f hf => ?_⟩
  obtain ⟨c, hc⟩ := C.uniformOuterRadius ν.1 ν.2
  rw [hR] at hc
  constructor
  · rw [P.localize_eq_cutoff_mul]
    exact hK (P.cutoff ν) (P.cutoffSmooth ν) (P.cutoffCompact ν)
      ⟨c, (P.cutoffSupport ν).trans hc⟩ B (hP ν) f hf
  · exact hK (L.cutoff ν) (L.smooth ν) (L.compactSupport ν)
      ⟨c, (L.support ν).trans hc⟩ B (hL ν) f hf

/-- The original real `s>4, m≥s+2` hypothesis supplies both intermediate and
target cutoff multipliers, with no rounding or change of the Sobolev norm. -/
private theorem original_intermediate_target_cutoff_multipliers
    (s : ℝ) (hs : 4 < s) (m : ℕ) (hm : s + 2 ≤ (m : ℝ)) (R : ℝ) :
    ∃ K₁ K₂ : ℝ≥0,
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
        (C : BoundedLocalCover M), C.numerics.outerRadius = R →
        ∀ (P : SobolevPartition C) (L : SobolevLocalizers C) (B : ℝ≥0),
          P.CutoffDerivativeBounds m B → L.DerivativeBounds m B →
          ∀ (ν : C.Index) (f : SobolevModel → ℝ),
            (LocalSobolevMem (s - 1) f →
              (LocalSobolevMem (s - 1) (P.localize ν f) ∧
                localSobolevENN (s - 1) (P.localize ν f) ≤
                  (K₁ : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - 1) f) ∧
              (LocalSobolevMem (s - 1) (L.cutoff ν * f) ∧
                localSobolevENN (s - 1) (L.cutoff ν * f) ≤
                  (K₁ : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - 1) f)) ∧
            (LocalSobolevMem (s - 2) f →
              (LocalSobolevMem (s - 2) (P.localize ν f) ∧
                localSobolevENN (s - 2) (P.localize ν f) ≤
                  (K₂ : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - 2) f) ∧
              (LocalSobolevMem (s - 2) (L.cutoff ν * f) ∧
                localSobolevENN (s - 2) (L.cutoff ν * f) ≤
                  (K₂ : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - 2) f)) := by
  obtain ⟨K₁, h₁⟩ := uniform_original_cutoff_multiplier (s - 1) (by linarith) m
    (by linarith) R
  obtain ⟨K₂, h₂⟩ := uniform_original_cutoff_multiplier (s - 2) (by linarith) m
    (by linarith) R
  refine ⟨K₁, K₂, fun M _ _ C hR P L B hP hL ν f => ?_⟩
  exact ⟨h₁ M C hR P L B hP hL ν f, h₂ M C hR P L B hP hL ν f⟩

end K24.Global.SobolevCutoff


/- Source: K24SOBDERIV_Multiplier.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped ENNReal NNReal SchwartzMap BoundedContinuousFunction Topology

namespace K24.Global.SobolevDerivative

/-- Quantitative form of the bounded Fourier multiplier theorem, for the
unchanged canonical Bessel norm at every real order. -/
private theorem bessel_fourierMultiplier_bound {s : ℝ} {T : LocalDistribution}
    (hT : BesselMem s T) (g : SobolevModel → ℂ)
    (hg : g.HasTemperateGrowth) (K : ℝ≥0) (hK : ∀ x, ‖g x‖ ≤ (K : ℝ)) :
    BesselMem s (fourierMultiplierCLM ℂ g T) ∧
    besselSobolevENN s (fourierMultiplierCLM ℂ g T) ≤
      (K : ℝ≥0∞) * besselSobolevENN s T := by
  let G : SobolevModel →ᵇ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup g hg.1.continuous K hK
  let Gp : Lp ℂ ⊤ (volume : Measure SobolevModel) := G.memLp_top.toLp G
  let U : LocalL2 := 𝓕 (besselRepresentative hT)
  let W : LocalL2 := Gp • U
  have hU : smulLeftCLM ℂ (fun x : SobolevModel => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ))
      (𝓕 T) = (U : LocalDistribution) := by
    rw [← fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      besselRepresentative_spec hT, Lp.fourier_toTemperedDistribution_eq]
  have hW : smulLeftCLM ℂ (fun x : SobolevModel => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ))
      (𝓕 (fourierMultiplierCLM ℂ g T)) = (W : LocalDistribution) := by
    rw [Lp.toTemperedDistribution_smul_eq (by exact hg), ← hU,
      fourierMultiplierCLM_apply, fourier_fourierInv_eq,
      smulLeftCLM_smulLeftCLM_apply hg (by fun_prop),
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by exact hg)]
    congr 2
    ext x
    rw [mul_comm]
    rfl
  have hV : besselPotential SobolevModel ℂ s (fourierMultiplierCLM ℂ g T) =
      ((𝓕⁻ W : LocalL2) : LocalDistribution) := by
    rw [besselPotential, fourierMultiplierCLM_apply, hW,
      Lp.fourierInv_toTemperedDistribution_eq]
  have hGp : ‖Gp‖ ≤ (K : ℝ) := by
    dsimp [Gp]
    rw [Lp.norm_toLp]
    have hb : eLpNorm (G : SobolevModel → ℂ) ⊤ volume ≤ (K : ℝ≥0∞) := by
      simpa [G] using (eLpNorm_le_of_ae_bound (μ := (volume : Measure SobolevModel))
        (p := ⊤) (Eventually.of_forall hK))
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top hb
  refine ⟨⟨𝓕⁻ W, hV⟩, ?_⟩
  have hInvNorm : ‖𝓕⁻ W‖ = ‖W‖ := by
    simpa only [fourier_fourierInv_eq] using (Lp.norm_fourier_eq (𝓕⁻ W)).symm
  rw [besselSobolevENN_eq_of_rep (𝓕⁻ W) hV, hInvNorm,
    besselSobolevENN_of_mem hT]
  have hb : ‖W‖ ≤ (K : ℝ) * ‖besselRepresentative hT‖ := by
    calc
      ‖W‖ ≤ ‖Gp‖ * ‖U‖ := Lp.norm_smul_le Gp U
      _ ≤ (K : ℝ) * ‖U‖ := mul_le_mul_of_nonneg_right hGp (norm_nonneg U)
      _ = _ := by simp only [U, Lp.norm_fourier_eq]
  convert ENNReal.ofReal_le_ofReal hb using 1
  rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]

end K24.Global.SobolevDerivative


/- Source: K24SOBDERIV_Order.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped ENNReal NNReal SchwartzMap Topology Real LineDeriv

namespace K24.Global.SobolevDerivative

private theorem bessel_norm_potential (s r : ℝ) (T : LocalDistribution)
    (hT : BesselMem (r + s) T) :
    besselSobolevENN s (besselPotential SobolevModel ℂ r T) =
      besselSobolevENN (r + s) T := by
  have h : BesselMem s (besselPotential SobolevModel ℂ r T) :=
    memSobolev_besselPotential_iff.mpr hT
  have heq : besselRepresentative h = besselRepresentative hT := by
    apply besselRepresentative_unique
    rw [besselPotential_besselPotential_apply, besselRepresentative_spec hT]
  rw [besselSobolevENN_of_mem h, besselSobolevENN_of_mem hT, heq]

private theorem bessel_norm_complex_smul {s : ℝ} {T : LocalDistribution}
    (hT : BesselMem s T) (c : ℂ) :
    besselSobolevENN s (c • T) = ENNReal.ofReal ‖c‖ * besselSobolevENN s T := by
  have heq : besselRepresentative (hT.smul c) = c • besselRepresentative hT := by
    apply besselRepresentative_unique
    rw [map_smul, besselRepresentative_spec hT]
    exact ((Lp.toTemperedDistributionCLM ℂ (volume : Measure SobolevModel) 2).map_smul
      c _).symm
  rw [besselSobolevENN_of_mem (hT.smul c), heq, norm_smul,
    ENNReal.ofReal_mul (norm_nonneg c), besselSobolevENN_of_mem hT]

/-- Lowering a real Sobolev order contracts the exact canonical Bessel norm. -/
private theorem bessel_lower_order {s r : ℝ} (hrs : r ≤ s) {T : LocalDistribution}
    (hT : BesselMem s T) :
    BesselMem r T ∧ besselSobolevENN r T ≤ besselSobolevENN s T := by
  have hm : BesselMem r T := hT.mono hrs
  have hb := bessel_fourierMultiplier_bound hT
    (fun x : SobolevModel => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((r - s) / 2)))
    (by fun_prop) 1 (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith))
  have hn := bessel_norm_potential s (r - s) T (by simpa using hm)
  refine ⟨hm, ?_⟩
  have hh := hb.2
  change besselSobolevENN s (besselPotential SobolevModel ℂ (r - s) T) ≤
    (1 : ℝ≥0∞) * besselSobolevENN s T at hh
  rw [hn] at hh
  simpa using hh

private theorem normalized_derivative_symbol_bound (m x : SobolevModel) :
    ‖Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))‖ ≤ ‖m‖ := by
  apply le_of_sq_le_sq _ (by positivity)
  simp only [Complex.ofReal_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h₁ : |(1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)| ^ 2 = (1 + ‖x‖ ^ 2)⁻¹ := by
    field_simp
    norm_cast
    rw [Real.rpow_neg (by positivity), sq_abs, inv_pow]
    field_simp
    calc
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]; simp
      _ = _ := by simp
  have h₂ : |inner ℝ x m| ^ 2 ≤ ‖m‖ ^ 2 * (1 + ‖x‖ ^ 2) := by
    grw [abs_real_inner_le_norm]
    rw [mul_pow, mul_comm]
    gcongr
    simp
  grw [h₁, h₂]
  apply le_of_eq
  field_simp

/-- The original Fourier normalization gives the explicit 2π factor. -/
private theorem bessel_directional_derivative {s : ℝ} {T : LocalDistribution}
    (hT : BesselMem s T) (m : SobolevModel) :
    BesselMem (s - 1) (∂_{m} T) ∧
    besselSobolevENN (s - 1) (∂_{m} T) ≤
      ENNReal.ofReal (2 * Real.pi * ‖m‖) * besselSobolevENN s T := by
  have hm : BesselMem (s - 1) (∂_{m} T) := hT.lineDerivOp
  let g : SobolevModel → ℂ := fun x =>
    Complex.ofReal (inner ℝ x m * (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))
  have hg : g.HasTemperateGrowth := by dsimp [g]; fun_prop
  have hb := bessel_fourierMultiplier_bound hT g hg ‖m‖₊
    (fun x => normalized_derivative_symbol_bound m x)
  have hn := bessel_norm_potential s (-1) (∂_{m} T) (by convert hm using 1 <;> ring)
  have hnorm : besselSobolevENN (s - 1) (∂_{m} T) =
      ENNReal.ofReal (2 * Real.pi) *
        besselSobolevENN s (fourierMultiplierCLM ℂ g T) := by
    rw [← show -1 + s = s - 1 by ring, ← hn,
      besselPotential_neg_one_lineDerivOp_eq, bessel_norm_complex_smul hb.1]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  refine ⟨hm, ?_⟩
  rw [hnorm]
  calc
    _ ≤ ENNReal.ofReal (2 * Real.pi) * ((‖m‖₊ : ℝ≥0∞) * besselSobolevENN s T) := by
      gcongr
      exact hb.2
    _ = _ := by
      rw [show (‖m‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖m‖ from
          (ENNReal.ofReal_coe_nnreal (p := ‖m‖₊)).symm,
        ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end K24.Global.SobolevDerivative


/- Source: K24SOBCUTOFF2_Plancherel.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform TemperedDistribution Filter LineDeriv
open scoped NNReal ENNReal SchwartzMap Topology ContDiff LineDeriv BigOperators

namespace K24.Global.SobolevCutoffSource
open SobolevCutoff SobolevAlgebra

private def coordinateDerivative (m : ℕ) (i : Fin 4) (φ : 𝓢(SobolevModel, ℂ)) :
    𝓢(SobolevModel, ℂ) := ∂^{fun _ : Fin m => basisVector i} φ

private theorem coordinateDerivative_succ (m : ℕ) (i : Fin 4) (φ : 𝓢(SobolevModel, ℂ)) :
    coordinateDerivative (m + 1) i φ = ∂_{basisVector i} (coordinateDerivative m i φ) := by
  rw [coordinateDerivative, iteratedLineDerivOp_succ_left]
  rfl

private theorem coordinateDerivative_fourier_norm (m : ℕ) (i : Fin 4)
    (φ : 𝓢(SobolevModel, ℂ)) (ξ : SobolevModel) :
    ‖𝓕 (coordinateDerivative m i φ) ξ‖ =
      (2 * Real.pi) ^ m * |ξ i| ^ m * ‖𝓕 φ ξ‖ := by
  induction m with
  | zero => simp [coordinateDerivative]
  | succ m ih =>
    rw [coordinateDerivative_succ, SchwartzMap.fourier_lineDerivOp_eq]
    have hg : (fun x : SobolevModel => inner ℝ x (basisVector i)).HasTemperateGrowth := by
      fun_prop
    simp only [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg, norm_smul]
    rw [ih]
    simp only [basisVector, EuclideanSpace.inner_single_right, conj_trivial,
      mul_one, Real.norm_eq_abs, Complex.norm_mul, Complex.norm_ofNat,
      Complex.norm_real, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, pow_succ]
    ring

private theorem coordinate_power_fourier_le (m : ℕ) (i : Fin 4)
    (φ : 𝓢(SobolevModel, ℂ)) (ξ : SobolevModel) :
    |ξ i| ^ m * ‖𝓕 φ ξ‖ ≤ ‖𝓕 (coordinateDerivative m i φ) ξ‖ := by
  rw [coordinateDerivative_fourier_norm]
  have hpi : 1 ≤ (2 * Real.pi) ^ m := one_le_pow₀ (by linarith [Real.pi_gt_three])
  calc
    _ = 1 * (|ξ i| ^ m * ‖𝓕 φ ξ‖) := (one_mul _).symm
    _ ≤ (2 * Real.pi) ^ m * (|ξ i| ^ m * ‖𝓕 φ ξ‖) :=
      mul_le_mul_of_nonneg_right hpi (by positivity)
    _ = _ := by ring

private theorem coordinateDerivative_norm_le (m : ℕ) (i : Fin 4)
    (φ : 𝓢(SobolevModel, ℂ)) (x : SobolevModel) :
    ‖coordinateDerivative m i φ x‖ ≤ ‖iteratedFDeriv ℝ m φ x‖ := by
  rw [coordinateDerivative, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  have h := (iteratedFDeriv ℝ m φ x).le_opNorm (fun _ : Fin m => basisVector i)
  simpa [basisVector, PiLp.norm_single] using h

private theorem norm_le_sum_abs_coordinates (ξ : SobolevModel) : ‖ξ‖ ≤ ∑ i : Fin 4, |ξ i| := by
  have heq : ∑ i : Fin 4, EuclideanSpace.single i (ξ i) = ξ := by
    ext j
    simp
  calc
    ‖ξ‖ = ‖∑ i : Fin 4, EuclideanSpace.single i (ξ i)‖ := congrArg norm heq.symm
    _ ≤ ∑ i : Fin 4, ‖EuclideanSpace.single i (ξ i)‖ := norm_sum_le _ _
    _ = _ := by simp [PiLp.norm_single, Real.norm_eq_abs]

private theorem norm_pow_le_coordinate_powers (m : ℕ) (hm : 1 ≤ m) (ξ : SobolevModel) :
    ‖ξ‖ ^ m ≤ (4 : ℝ) ^ ((m : ℝ) - 1) * ∑ i : Fin 4, |ξ i| ^ m := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (Finset.univ : Finset (Fin 4)) (f := fun i => |ξ i|)
    (show (1 : ℝ) ≤ m by exact_mod_cast hm) (fun _ _ => abs_nonneg _)
  have hn : ‖ξ‖ ^ m ≤ (∑ i : Fin 4, |ξ i|) ^ m :=
    pow_le_pow_left₀ (norm_nonneg ξ) (norm_le_sum_abs_coordinates ξ) m
  apply hn.trans
  simpa only [Real.rpow_natCast, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] using h

private def polynomialConstant (m : ℕ) : ℝ :=
  (2 : ℝ) ^ ((m : ℝ) / 2) * (4 : ℝ) ^ ((m : ℝ) - 1)

private theorem polynomialConstant_nonneg (m : ℕ) : 0 ≤ polynomialConstant m := by
  unfold polynomialConstant
  positivity

private theorem weighted_fourier_le_derivatives (m : ℕ) (hm : 1 ≤ m)
    (φ : 𝓢(SobolevModel, ℂ)) (ξ : SobolevModel) :
    besselWeight m ξ * ‖𝓕 φ ξ‖ ≤ polynomialConstant m *
      (‖𝓕 φ ξ‖ + ∑ i : Fin 4, ‖𝓕 (coordinateDerivative m i φ) ξ‖) := by
  have hfour : 1 ≤ (4 : ℝ) ^ ((m : ℝ) - 1) :=
    Real.one_le_rpow (by norm_num) (by
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith)
  have hweight : besselWeight m ξ ≤ polynomialConstant m *
      (1 + ∑ i : Fin 4, |ξ i| ^ m) := by
    calc
      _ ≤ (2 : ℝ) ^ ((m : ℝ) / 2) * (1 + ‖ξ‖ ^ m) := besselWeight_nat_le m ξ
      _ ≤ (2 : ℝ) ^ ((m : ℝ) / 2) *
          ((4 : ℝ) ^ ((m : ℝ) - 1) +
            (4 : ℝ) ^ ((m : ℝ) - 1) * ∑ i : Fin 4, |ξ i| ^ m) :=
        mul_le_mul_of_nonneg_left (add_le_add hfour (norm_pow_le_coordinate_powers m hm ξ))
          (by positivity)
      _ = _ := by unfold polynomialConstant; ring
  calc
    _ ≤ (polynomialConstant m * (1 + ∑ i : Fin 4, |ξ i| ^ m)) * ‖𝓕 φ ξ‖ :=
      mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
    _ = polynomialConstant m * (‖𝓕 φ ξ‖ + ∑ i : Fin 4, |ξ i| ^ m * ‖𝓕 φ ξ‖) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (Finset.sum_le_sum fun i _ => coordinate_power_fourier_le m i φ ξ))
      (polynomialConstant_nonneg m)

private theorem schwartz_fourier_eLpNorm_two (φ : 𝓢(SobolevModel, ℂ)) :
    eLpNorm ((𝓕 φ : 𝓢(SobolevModel, ℂ)) : SobolevModel → ℂ) 2 volume = eLpNorm φ 2 volume := by
  rw [← Lp.enorm_toLp ((𝓕 φ).memLp 2 volume), ← Lp.enorm_toLp (φ.memLp 2 volume),
    ← ofReal_norm, ← ofReal_norm]
  change ENNReal.ofReal ‖(𝓕 φ).toLp 2 volume‖ = ENNReal.ofReal ‖φ.toLp 2 volume‖
  rw [SchwartzMap.norm_fourier_toL2_eq]

end K24.Global.SobolevCutoffSource


/- Source: K24SOBCUTOFF2_Bessel.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory FourierTransform TemperedDistribution Filter LineDeriv
open scoped NNReal ENNReal SchwartzMap Topology ContDiff LineDeriv BigOperators

namespace K24.Global.SobolevCutoffSource
open SobolevCutoff SobolevAlgebra

private def ballL2Constant (R : ℝ) : ℝ≥0 :=
  ((volume (Metric.ball (0 : SobolevModel) R)) ^ (1 / 2 : ℝ)).toNNReal

private theorem coe_ballL2Constant (R : ℝ) :
    (ballL2Constant R : ℝ≥0∞) = (volume (Metric.ball (0 : SobolevModel) R)) ^ (1 / 2 : ℝ) := by
  unfold ballL2Constant
  exact ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne)

private theorem supported_eLpNorm_two_le (f : SobolevModel → ℂ) (c : SobolevModel)
    (R : ℝ) (hsupp : Function.support f ⊆ Metric.ball c R) (B : ℝ≥0)
    (hb : ∀ x, ‖f x‖ ≤ (B : ℝ)) :
    eLpNorm f 2 volume ≤ (B : ℝ≥0∞) * (ballL2Constant R : ℝ≥0∞) := by
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp, coe_ballL2Constant]
  calc
    _ ≤ eLpNorm (fun _ : SobolevModel => (B : ℝ)) 2 (volume.restrict (Metric.ball c R)) :=
      eLpNorm_mono_real hb
    _ = _ := by
      rw [eLpNorm_const' _ (by norm_num) (by norm_num)]
      simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg B.coe_nonneg,
        ENNReal.ofReal_coe_nnreal, Measure.restrict_apply_univ, ENNReal.toReal_ofNat,
        Measure.addHaar_ball_center]

private def sourceCutoffConstant (m : ℕ) (R : ℝ) : ℝ≥0 :=
  5 * Real.toNNReal (polynomialConstant m) * ballL2Constant R

private theorem schwartz_integer_bessel_bound (φ : 𝓢(SobolevModel, ℂ))
    (c : SobolevModel) (R : ℝ) (hsupp : tsupport φ ⊆ Metric.ball c R)
    (m : ℕ) (hm : 1 ≤ m) (B : ℝ≥0)
    (hb : ∀ n ≤ m, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ (B : ℝ)) :
    besselSobolevENN m (φ : LocalDistribution) ≤
      (sourceCutoffConstant m R : ℝ≥0∞) * (B : ℝ≥0∞) := by
  let F : SobolevModel → ℝ := fun ξ => ‖𝓕 φ ξ‖
  let G : Fin 4 → SobolevModel → ℝ := fun i ξ => ‖𝓕 (coordinateDerivative m i φ) ξ‖
  have hF : Continuous F := (𝓕 φ).continuous.norm
  have hG (i : Fin 4) : Continuous (G i) := (𝓕 (coordinateDerivative m i φ)).continuous.norm
  have hsum : Continuous (∑ i : Fin 4, G i) := by
    have heq : (∑ i : Fin 4, G i) = fun x => ∑ i : Fin 4, G i x := by
      ext x
      simp only [Finset.sum_apply]
    rw [heq]
    exact continuous_finsetSum Finset.univ (fun i _ => hG i)
  have hFnorm : eLpNorm F 2 volume ≤ (B : ℝ≥0∞) * (ballL2Constant R : ℝ≥0∞) := by
    rw [show F = fun ξ => ‖𝓕 φ ξ‖ from rfl, eLpNorm_norm, schwartz_fourier_eLpNorm_two]
    apply supported_eLpNorm_two_le _ c R (fun x hx => hsupp (subset_tsupport _ hx)) B
    intro x
    simpa only [norm_iteratedFDeriv_zero] using hb 0 (Nat.zero_le m) x
  have hGnorm (i : Fin 4) : eLpNorm (G i) 2 volume ≤
      (B : ℝ≥0∞) * (ballL2Constant R : ℝ≥0∞) := by
    rw [show G i = fun ξ => ‖𝓕 (coordinateDerivative m i φ) ξ‖ from rfl,
      eLpNorm_norm, schwartz_fourier_eLpNorm_two]
    have hsuppD : Function.support (coordinateDerivative m i φ : SobolevModel → ℂ) ⊆
        Metric.ball c R := by
      intro x hx
      exact hsupp (SchwartzMap.tsupport_iteratedLineDerivOp_subset _ φ (subset_tsupport _ hx))
    exact supported_eLpNorm_two_le _ c R hsuppD B
      (fun x => (coordinateDerivative_norm_le m i φ x).trans (hb m le_rfl x))
  have hFG : eLpNorm (F + ∑ i : Fin 4, G i) 2 volume ≤
      eLpNorm F 2 volume + ∑ i : Fin 4, eLpNorm (G i) 2 volume :=
    (eLpNorm_add_le hF.aestronglyMeasurable hsum.aestronglyMeasurable (by norm_num)).trans
      (add_le_add le_rfl (eLpNorm_sum_le (fun i _ => (hG i).aestronglyMeasurable) (by norm_num)))
  rw [schwartz_bessel_norm_eq_weighted]
  calc
    _ ≤ eLpNorm ((polynomialConstant m) • (F + ∑ i : Fin 4, G i)) 2 volume := by
      apply eLpNorm_mono_real
      intro ξ
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (besselWeight_nonneg (m : ℝ) ξ)]
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Finset.sum_apply, F, G] using
        weighted_fourier_le_derivatives m hm φ ξ
    _ = ENNReal.ofReal (polynomialConstant m) * eLpNorm (F + ∑ i : Fin 4, G i) 2 volume := by
      rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs,
        abs_of_nonneg (polynomialConstant_nonneg m)]
    _ ≤ ENNReal.ofReal (polynomialConstant m) *
        (eLpNorm F 2 volume + ∑ i : Fin 4, eLpNorm (G i) 2 volume) := by gcongr
    _ ≤ ENNReal.ofReal (polynomialConstant m) *
        ((B : ℝ≥0∞) * (ballL2Constant R : ℝ≥0∞) +
          ∑ i : Fin 4, (B : ℝ≥0∞) * (ballL2Constant R : ℝ≥0∞)) := by
      exact mul_le_mul le_rfl (add_le_add hFnorm (Finset.sum_le_sum fun i _ => hGnorm i))
        bot_le bot_le
    _ = _ := by
      simp only [sourceCutoffConstant, ENNReal.coe_mul, ENNReal.coe_ofNat,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change ENNReal.ofReal (polynomialConstant m) *
          ((B : ℝ≥0∞) * (ballL2Constant R : ℝ≥0∞) +
            4 * ((B : ℝ≥0∞) * (ballL2Constant R : ℝ≥0∞))) =
        5 * ENNReal.ofReal (polynomialConstant m) * (ballL2Constant R : ℝ≥0∞) * (B : ℝ≥0∞)
      ring

/-- The actual source-order Bessel norm is controlled at every real order
`s≤m`, including the endpoint allowed by the original `m≥s+2`. -/
private theorem compact_source_localSobolev_bound (f : SobolevModel → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : SobolevModel) (R : ℝ) (hsupp : tsupport f ⊆ Metric.ball c R)
    (m : ℕ) (hm : 1 ≤ m) (B : ℝ≥0)
    (hb : ∀ n ≤ m, derivativeENorm n Set.univ f ≤ (B : ℝ≥0∞))
    (s : ℝ) (hsm : s ≤ (m : ℝ)) :
    LocalSobolevMem s f ∧ localSobolevENN s f ≤
      (sourceCutoffConstant m R : ℝ≥0∞) * (B : ℝ≥0∞) := by
  have hfc : ContDiff ℝ ∞ (complexifyLocal f) := Complex.ofRealCLM.contDiff.comp hf
  have hcc : HasCompactSupport (complexifyLocal f) := hc.comp_left rfl
  have hsuppc : tsupport (complexifyLocal f) ⊆ Metric.ball c R := by
    have heq : Function.support (complexifyLocal f) = Function.support f := by
      ext x
      simp [Function.mem_support, complexifyLocal]
    simpa only [tsupport, heq] using hsupp
  let φ : 𝓢(SobolevModel, ℂ) := hcc.toSchwartzMap hfc
  have hbcomplex (n : ℕ) (hn : n ≤ m) (x : SobolevModel) :
      ‖iteratedFDeriv ℝ n φ x‖ ≤ (B : ℝ) := by
    have heq := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (x := x) hf.contDiffAt
      (show (n : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    change ‖iteratedFDeriv ℝ n φ x‖ = ‖iteratedFDeriv ℝ n f x‖ at heq
    rw [heq]
    exact norm_iteratedFDeriv_le_of_derivativeENorm f n B (hb n hn) x
  have hmemb : BesselMem (m : ℝ) (φ : LocalDistribution) := φ.memSobolev
  have hlower := SobolevDerivative.bessel_lower_order hsm hmemb
  have hnorm := schwartz_integer_bessel_bound φ c R hsuppc m hm B hbcomplex
  have hfl : MemLp (complexifyLocal f) 2 volume := φ.memLp 2 volume
  have hdist : localFunctionDistribution f hfl = (φ : LocalDistribution) := by
    change ((φ.toLp 2 volume : LocalL2) : LocalDistribution) = _
    exact Lp.toTemperedDistribution_toLp_eq φ
  refine ⟨⟨hfl, hdist ▸ hlower.1⟩, ?_⟩
  rw [localSobolevENN, dif_pos hfl, hdist]
  exact hlower.2.trans hnorm

end K24.Global.SobolevCutoffSource


/- Source: K24SOBCUTOFF2_Multiplier.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped NNReal ENNReal Topology ContDiff Manifold

namespace K24.Global.SobolevCutoffSource

private theorem compact_source_multiplier (s : ℝ) (hs : 2 < s) (m : ℕ)
    (hm : 1 ≤ m) (hsm : s ≤ (m : ℝ)) (R : ℝ) :
    ∃ K : ℝ≥0, ∀ (χ : SobolevModel → ℝ),
      ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∃ c : SobolevModel, tsupport χ ⊆ Metric.ball c R) →
      ∀ B : ℝ≥0,
        (∀ n ≤ m, derivativeENorm n Set.univ χ ≤ (B : ℝ≥0∞)) →
        ∀ f : SobolevModel → ℝ, LocalSobolevMem s f →
          LocalSobolevMem s (χ * f) ∧ localSobolevENN s (χ * f) ≤
            (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN s f := by
  obtain ⟨A, hA⟩ := SobolevAlgebra.localSobolev_algebra s hs
  refine ⟨A * sourceCutoffConstant m R, fun χ hχ hc hsupp B hb f hf => ?_⟩
  obtain ⟨c, hsupport⟩ := hsupp
  obtain ⟨hχs, hχbound⟩ := compact_source_localSobolev_bound χ hχ hc
    c R hsupport m hm B hb s hsm
  obtain ⟨hmem, hbound⟩ := hA χ f hχs hf
  refine ⟨hmem, hbound.trans ?_⟩
  calc
    _ ≤ (A : ℝ≥0∞) * ((sourceCutoffConstant m R : ℝ≥0∞) * (B : ℝ≥0∞)) *
        localSobolevENN s f := by gcongr
    _ = _ := by simp only [ENNReal.coe_mul]; ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable {C : BoundedLocalCover M}

private theorem original_partition_source_bound (P : SobolevPartition C)
    (s : ℝ) (hs : 4 < s) (m : ℕ) (hm : s + 2 ≤ (m : ℝ))
    (B : ℝ≥0) (hb : P.CutoffDerivativeBounds m B) (ν : C.Index) :
    LocalSobolevMem s (P.cutoff ν) ∧ localSobolevENN s (P.cutoff ν) ≤
      (sourceCutoffConstant m C.numerics.outerRadius : ℝ≥0∞) * (B : ℝ≥0∞) := by
  obtain ⟨c, hc⟩ := C.uniformOuterRadius ν.1 ν.2
  have hm1 : 1 ≤ m := by
    have hh : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast hh
  exact compact_source_localSobolev_bound (P.cutoff ν) (P.cutoffSmooth ν) (P.cutoffCompact ν)
    c C.numerics.outerRadius ((P.cutoffSupport ν).trans hc) m hm1 B (hb ν) s (by linarith)

private theorem original_localizer_source_bound (L : SobolevLocalizers C)
    (s : ℝ) (hs : 4 < s) (m : ℕ) (hm : s + 2 ≤ (m : ℝ))
    (B : ℝ≥0) (hb : L.DerivativeBounds m B) (ν : C.Index) :
    LocalSobolevMem s (L.cutoff ν) ∧ localSobolevENN s (L.cutoff ν) ≤
      (sourceCutoffConstant m C.numerics.outerRadius : ℝ≥0∞) * (B : ℝ≥0∞) := by
  obtain ⟨c, hc⟩ := C.uniformOuterRadius ν.1 ν.2
  have hm1 : 1 ≤ m := by
    have hh : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast hh
  exact compact_source_localSobolev_bound (L.cutoff ν) (L.smooth ν) (L.compactSupport ν)
    c C.numerics.outerRadius ((L.support ν).trans hc) m hm1 B (hb ν) s (by linarith)

universe u

/-- Actual original source-order localization, including all allowed integer
endpoints. The norm and real order are exactly the canonical ones. -/
private theorem original_source_cutoff_multiplier
    (s : ℝ) (hs : 4 < s) (m : ℕ) (hm : s + 2 ≤ (m : ℝ)) (R : ℝ) :
    ∃ K : ℝ≥0,
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
        (C : BoundedLocalCover M), C.numerics.outerRadius = R →
        ∀ (P : SobolevPartition C) (L : SobolevLocalizers C) (B : ℝ≥0),
          P.CutoffDerivativeBounds m B → L.DerivativeBounds m B →
          ∀ (ν : C.Index) (f : SobolevModel → ℝ), LocalSobolevMem s f →
            (LocalSobolevMem s (P.localize ν f) ∧
              localSobolevENN s (P.localize ν f) ≤
                (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN s f) ∧
            (LocalSobolevMem s (L.cutoff ν * f) ∧
              localSobolevENN s (L.cutoff ν * f) ≤
                (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN s f) := by
  have hm1 : 1 ≤ m := by
    have hh : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast hh
  obtain ⟨K, hK⟩ := compact_source_multiplier s (by linarith) m hm1 (by linarith) R
  refine ⟨K, fun M _ _ C hR P L B hP hL ν f hf => ?_⟩
  obtain ⟨c, hc⟩ := C.uniformOuterRadius ν.1 ν.2
  rw [hR] at hc
  constructor
  · rw [P.localize_eq_cutoff_mul]
    exact hK (P.cutoff ν) (P.cutoffSmooth ν) (P.cutoffCompact ν)
      ⟨c, (P.cutoffSupport ν).trans hc⟩ B (hP ν) f hf
  · exact hK (L.cutoff ν) (L.smooth ν) (L.compactSupport ν)
      ⟨c, (L.support ν).trans hc⟩ B (hL ν) f hf

end K24.Global.SobolevCutoffSource


/- Final new three-order assembly. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped NNReal ENNReal Topology ContDiff Manifold

namespace K24.Global.SobolevCutoffAll
universe u

/-- A single uniform multiplier constant for all three original real-order
Sobolev levels. It is chosen before every manifold, cover, and cutoff. -/
private theorem original_three_order_cutoff_multiplier
    (s : ℝ) (hs : 4 < s) (m : ℕ) (hm : s + 2 ≤ (m : ℝ)) (R : ℝ) :
    ∃ K : ℝ≥0,
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
        (C : BoundedLocalCover M), C.numerics.outerRadius = R →
        ∀ (P : SobolevPartition C) (L : SobolevLocalizers C) (B : ℝ≥0),
          P.CutoffDerivativeBounds m B → L.DerivativeBounds m B →
          ∀ j : ℕ, j ≤ 2 →
            ∀ (ν : C.Index) (f : SobolevModel → ℝ), LocalSobolevMem (s - j) f →
              (LocalSobolevMem (s - j) (P.localize ν f) ∧
                localSobolevENN (s - j) (P.localize ν f) ≤
                  (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - j) f) ∧
              (LocalSobolevMem (s - j) (L.cutoff ν * f) ∧
                localSobolevENN (s - j) (L.cutoff ν * f) ≤
                  (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - j) f) := by
  obtain ⟨K₀, h₀⟩ := SobolevCutoffSource.original_source_cutoff_multiplier s hs m hm R
  obtain ⟨K₁, K₂, h₁₂⟩ := SobolevCutoff.original_intermediate_target_cutoff_multipliers s hs m hm R
  let K : ℝ≥0 := K₀ + K₁ + K₂
  have hK₀ : K₀ ≤ K :=
    (le_add_of_nonneg_right (show 0 ≤ K₁ from zero_le)).trans
      (le_add_of_nonneg_right (show 0 ≤ K₂ from zero_le))
  have hK₁ : K₁ ≤ K :=
    (le_add_of_nonneg_left (show 0 ≤ K₀ from zero_le)).trans
      (le_add_of_nonneg_right (show 0 ≤ K₂ from zero_le))
  have hK₂ : K₂ ≤ K := le_add_of_nonneg_left (show 0 ≤ K₀ + K₁ from zero_le)
  refine ⟨K, fun M _ _ C hR P L B hP hL j hj ν f hf => ?_⟩
  have enlarge (r : ℝ) (K' : ℝ≥0) (hK' : K' ≤ K)
      (h : (LocalSobolevMem r (P.localize ν f) ∧
          localSobolevENN r (P.localize ν f) ≤
            (K' : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN r f) ∧
        (LocalSobolevMem r (L.cutoff ν * f) ∧
          localSobolevENN r (L.cutoff ν * f) ≤
            (K' : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN r f)) :
      (LocalSobolevMem r (P.localize ν f) ∧
          localSobolevENN r (P.localize ν f) ≤
            (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN r f) ∧
        (LocalSobolevMem r (L.cutoff ν * f) ∧
          localSobolevENN r (L.cutoff ν * f) ≤
            (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN r f) := by
    have hh : (K' : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN r f ≤
        (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN r f := by gcongr
    exact ⟨⟨h.1.1, h.1.2.trans hh⟩, ⟨h.2.1, h.2.2.trans hh⟩⟩
  interval_cases j
  · simpa only [Nat.cast_zero, sub_zero] using enlarge s K₀ hK₀
      (h₀ M C hR P L B hP hL ν f (by simpa only [Nat.cast_zero, sub_zero] using hf))
  · simpa only [Nat.cast_one] using enlarge (s - 1) K₁ hK₁
      ((h₁₂ M C hR P L B hP hL ν f).1 (by simpa only [Nat.cast_one] using hf))
  · simpa only [Nat.cast_ofNat] using enlarge (s - 2) K₂ hK₂
      ((h₁₂ M C hR P L B hP hL ν f).2 (by simpa only [Nat.cast_ofNat] using hf))

end K24.Global.SobolevCutoffAll


open K24.Global
universe u

theorem solution :
  ∀ (s : ℝ), 4 < s → ∀ m : ℕ, s + 2 ≤ (m : ℝ) → ∀ R : ℝ,
    ∃ K : ℝ≥0,
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
        (C : BoundedLocalCover M), C.numerics.outerRadius = R →
        ∀ (P : SobolevPartition C) (L : SobolevLocalizers C) (B : ℝ≥0),
          P.CutoffDerivativeBounds m B → L.DerivativeBounds m B →
          ∀ j : ℕ, j ≤ 2 →
            ∀ (ν : C.Index) (f : SobolevModel → ℝ), LocalSobolevMem (s - j) f →
              (LocalSobolevMem (s - j) (P.localize ν f) ∧
                localSobolevENN (s - j) (P.localize ν f) ≤
                  (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - j) f) ∧
              (LocalSobolevMem (s - j) (L.cutoff ν * f) ∧
                localSobolevENN (s - j) (L.cutoff ν * f) ≤
                  (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - j) f) := by
  intro s hs m hm R
  exact K24.Global.SobolevCutoffAll.original_three_order_cutoff_multiplier s hs m hm R

#check (solution :
  ∀ (s : ℝ), 4 < s → ∀ m : ℕ, s + 2 ≤ (m : ℝ) → ∀ R : ℝ,
    ∃ K : ℝ≥0,
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
        (C : BoundedLocalCover M), C.numerics.outerRadius = R →
        ∀ (P : SobolevPartition C) (L : SobolevLocalizers C) (B : ℝ≥0),
          P.CutoffDerivativeBounds m B → L.DerivativeBounds m B →
          ∀ j : ℕ, j ≤ 2 →
            ∀ (ν : C.Index) (f : SobolevModel → ℝ), LocalSobolevMem (s - j) f →
              (LocalSobolevMem (s - j) (P.localize ν f) ∧
                localSobolevENN (s - j) (P.localize ν f) ≤
                  (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - j) f) ∧
              (LocalSobolevMem (s - j) (L.cutoff ν * f) ∧
                localSobolevENN (s - j) (L.cutoff ν * f) ≤
                  (K : ℝ≥0∞) * (B : ℝ≥0∞) * localSobolevENN (s - j) f))
#print axioms solution
