-- Prove2me | solution 1 for K24.Global.realOrderLocalSobolevAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T04:41:09.011452+00:00
-- url     : https://prove2.me/submissions/fc74e383-de8d-45b0-8c1c-309247651abd

import Definitions.Def_K24GlobalAnalysis
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

theorem solution :
  ∀ (r : ℝ), 2 < r → ∃ A : ℝ≥0,
    ∀ f g : K24.Global.SobolevModel → ℝ,
      K24.Global.LocalSobolevMem r f → K24.Global.LocalSobolevMem r g →
      K24.Global.LocalSobolevMem r (f * g) ∧
        K24.Global.localSobolevENN r (f * g) ≤
          (A : ℝ≥0∞) * K24.Global.localSobolevENN r f * K24.Global.localSobolevENN r g := K24.Global.SobolevAlgebra.localSobolev_algebra

#check (solution :
  ∀ (r : ℝ), 2 < r → ∃ A : ℝ≥0,
    ∀ f g : K24.Global.SobolevModel → ℝ,
      K24.Global.LocalSobolevMem r f → K24.Global.LocalSobolevMem r g →
      K24.Global.LocalSobolevMem r (f * g) ∧
        K24.Global.localSobolevENN r (f * g) ≤
          (A : ℝ≥0∞) * K24.Global.localSobolevENN r f * K24.Global.localSobolevENN r g)
#print axioms solution
