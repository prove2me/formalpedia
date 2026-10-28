-- Prove2me | solution 1 for K24.Global.realOrderSobolevInverseFrechet
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T05:03:32.058935+00:00
-- url     : https://prove2.me/submissions/297b23e6-8f4d-4201-ba87-0cadf7b4f142

import Definitions.Def_K24GlobalStatement
import Mathlib.Topology.MetricSpace.Contracting
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

/- Reused frozen source: K24SOB2_Embedding.lean. -/

set_option autoImplicit false


open MeasureTheory TemperedDistribution FourierTransform
open scoped ENNReal SchwartzMap Real ContDiff BoundedContinuousFunction

namespace K24.Global

/-- The inverse Fourier integral of the decayed L2 input has genuine C2
regularity and a uniform bound on all actual derivatives through order two. -/
theorem inverseFourier_besselDecay_C2 {s : ℝ} (hs : 4 < s) :
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
theorem besselMem_C2_representative_bound {s : ℝ} (hs : 4 < s) :
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
theorem localSobolevMem_unique_C2_representative_bound {s : ℝ} (hs : 4 < s) :
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
theorem continuous_localSobolevMem_C2_bound {s : ℝ} (hs : 4 < s) :
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

end K24.Global

/- Reused frozen source: K24SOBGLOBAL_LocalComplete.lean. -/

set_option autoImplicit false


open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology BoundedContinuousFunction ContDiff

namespace K24.Global.SobolevGlobal

/-- Actual continuous real coefficients have complete canonical Sobolev norm
at the exact real threshold s > 2. The conclusion also records pointwise
convergence, so overlapping tensor charts can be glued faithfully. -/
theorem localSobolev_Cauchy_limit {s : ℝ} (hs : 2 < s)
    (f : ℕ → SobolevModel → ℝ) (hfc : ∀ n, Continuous (f n))
    (hf : ∀ n, LocalSobolevMem s (f n))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      localSobolevENN s (f i - f j) < ENNReal.ofReal eps) :
    ∃ g : SobolevModel → ℝ, Continuous g ∧ LocalSobolevMem s g ∧
      (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
        localSobolevENN s (f i - g) < ENNReal.ofReal eps) ∧
      ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  classical
  choose hL2 hB using hf
  let D : ℕ → LocalDistribution := fun n => localFunctionDistribution (f n) (hL2 n)
  have hDC : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      besselSobolevENN s (D i - D j) < ENNReal.ofReal eps := by
    intro eps heps
    obtain ⟨N, hN⟩ := hc eps heps
    refine ⟨N, ?_⟩
    intro i hi j hj
    have hsub : MemLp (complexifyLocal (f i - f j)) 2 volume := by
      convert (hL2 i).sub (hL2 j) using 1
      ext x; simp [complexifyLocal]
    rw [← localFunctionDistribution_sub _ _ (hL2 i) (hL2 j) hsub]
    simpa only [localSobolevENN, dif_pos hsub] using hN i hi j hj
  obtain ⟨T, hT, hconv⟩ := (exact_bessel_sectionBanachSpace s).complete D hB hDC
  obtain ⟨G, hGL2, hGT⟩ := besselMem_exists_boundedContinuous_L2 hs hT
  have hGD : boundedContinuousDistribution G = T :=
    (boundedContinuousDistribution_eq_L2 G hGL2).trans hGT
  choose F hF using fun n => besselMem_exists_boundedContinuous hs (hB n)
  have hFeq : ∀ n, (F n : SobolevModel → ℂ) = complexifyLocal (f n) :=
    fun n => eq_complexify_of_distribution_eq (hfc n) (hL2 n) (F n) (hF n)
  obtain ⟨A, hA⟩ := bessel_continuous_norm_bound hs
  have hFG : Tendsto F atTop (𝓝 G) := by
    apply Metric.tendsto_atTop.mpr
    intro eps heps
    have hden : 0 < (A : ℝ) + 1 := by positivity
    obtain ⟨N, hN⟩ := hconv (eps / (A + 1)) (div_pos heps hden)
    refine ⟨N, ?_⟩
    intro i hi
    have hdi : BesselMem s (D i - T) := (hB i).sub hT
    have hn : ‖besselRepresentative hdi‖ < eps / (A + 1) := by
      apply (ENNReal.ofReal_lt_ofReal_iff (div_pos heps hden)).mp
      simpa only [besselSobolevENN_of_mem hdi] using hN i hi
    have hb : ‖F i - G‖ ≤ (A : ℝ) * ‖besselRepresentative hdi‖ := by
      apply hA (D i - T) hdi (F i - G)
      rw [boundedContinuousDistribution_sub, hF i, hGD]
    rw [dist_eq_norm]
    have hh := (lt_div_iff₀ hden).mp hn
    nlinarith [norm_nonneg (besselRepresentative hdi)]
  have hpoint (x : SobolevModel) : Tendsto (fun n => F n x) atTop (𝓝 (G x)) :=
    ((BoundedContinuousFunction.evalCLM ℂ x).continuous.tendsto G).comp hFG
  have hreal : ∀ x : SobolevModel, (G x).im = 0 := by
    intro x
    have hh := Complex.continuous_im.continuousAt.tendsto.comp (hpoint x)
    simp only [Function.comp_def] at hh
    have hz : (fun n => (F n x).im) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      rw [hFeq n]
      simp [complexifyLocal]
    rw [hz] at hh
    exact (tendsto_nhds_unique hh tendsto_const_nhds)
  let g : SobolevModel → ℝ := fun x => (G x).re
  have hgc : Continuous g := Complex.continuous_re.comp G.continuous
  have hcomplex : complexifyLocal g = (G : SobolevModel → ℂ) := by
    funext x
    apply Complex.ext <;> simp [g, complexifyLocal, hreal]
  have hgl : MemLp (complexifyLocal g) 2 volume := hcomplex ▸ hGL2
  have hgd : localFunctionDistribution g hgl = T := by
    unfold localFunctionDistribution
    simpa only [hcomplex] using hGT
  refine ⟨g, hgc, ⟨hgl, hgd ▸ hT⟩, ?_, ?_⟩
  · intro eps heps
    obtain ⟨N, hN⟩ := hconv eps heps
    refine ⟨N, ?_⟩
    intro i hi
    have hsub : MemLp (complexifyLocal (f i - g)) 2 volume := by
      convert (hL2 i).sub hgl using 1
      ext x; simp [complexifyLocal]
    rw [localSobolevENN, dif_pos hsub,
      localFunctionDistribution_sub _ _ (hL2 i) hgl hsub, hgd]
    exact hN i hi
  · intro x
    have hh := Complex.continuous_re.continuousAt.tendsto.comp (hpoint x)
    simpa [Function.comp_def, hFeq, complexifyLocal, g] using hh

/-- If a pointwise limit of a Cauchy sequence is already specified by fiber
reconstruction, that same function is the canonical Sobolev limit. -/
theorem localSobolev_Cauchy_pointwise_limit {s : ℝ} (hs : 2 < s)
    (f : ℕ → SobolevModel → ℝ) (g : SobolevModel → ℝ)
    (hfc : ∀ n, Continuous (f n)) (hf : ∀ n, LocalSobolevMem s (f n))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      localSobolevENN s (f i - f j) < ENNReal.ofReal eps)
    (hpoint : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Continuous g ∧ LocalSobolevMem s g ∧
      ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
        localSobolevENN s (f i - g) < ENNReal.ofReal eps := by
  obtain ⟨g', hgc, hgm, hconv, hpoint'⟩ := localSobolev_Cauchy_limit hs f hfc hf hc
  have heq : g' = g := funext fun x => tendsto_nhds_unique (hpoint' x) (hpoint x)
  subst g'
  exact ⟨hgc, hgm, hconv⟩

end K24.Global.SobolevGlobal

/- Reused frozen source: K24SOBGLOBAL_LocalNorm.lean. -/

set_option autoImplicit false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace K24.Global.SobolevGlobal

def localBesselRepresentative {s : ℝ} {f : SobolevModel → ℝ}
    (hf : LocalSobolevMem s f) : LocalL2 := besselRepresentative hf.choose_spec

theorem localSobolevENN_eq_norm {s : ℝ} {f : SobolevModel → ℝ}
    (hf : LocalSobolevMem s f) :
    localSobolevENN s f = ENNReal.ofReal ‖localBesselRepresentative hf‖ := by
  rw [localSobolevENN, dif_pos hf.choose, besselSobolevENN_of_mem hf.choose_spec]
  rfl

theorem localSobolevENN_sub_eq_norm {s : ℝ} {f g : SobolevModel → ℝ}
    (hf : LocalSobolevMem s f) (hg : LocalSobolevMem s g) :
    localSobolevENN s (f - g) =
      ENNReal.ofReal ‖localBesselRepresentative hf - localBesselRepresentative hg‖ := by
  have hsub := (localSobolevMem_sub hf hg).choose
  rw [localSobolevENN, dif_pos hsub,
    localFunctionDistribution_sub _ _ hf.choose hg.choose hsub,
    besselSobolevENN_sub_eq hf.choose_spec hg.choose_spec]
  rfl

theorem localBesselRepresentative_tendsto {s : ℝ}
    {f : ℕ → SobolevModel → ℝ} {g : SobolevModel → ℝ}
    (hf : ∀ n, LocalSobolevMem s (f n)) (hg : LocalSobolevMem s g)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      localSobolevENN s (f i - g) < ENNReal.ofReal eps) :
    Tendsto (fun n => localBesselRepresentative (hf n)) atTop
      (𝓝 (localBesselRepresentative hg)) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨N, hN⟩ := hc eps heps
  refine ⟨N, fun i hi => ?_⟩
  have hh := hN i hi
  rw [localSobolevENN_sub_eq_norm (hf i) hg] at hh
  simpa only [dist_eq_norm] using (ENNReal.ofReal_lt_ofReal_iff heps).mp hh

theorem localSobolevENN_tendsto {s : ℝ}
    {f : ℕ → SobolevModel → ℝ} {g : SobolevModel → ℝ}
    (hf : ∀ n, LocalSobolevMem s (f n)) (hg : LocalSobolevMem s g)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      localSobolevENN s (f i - g) < ENNReal.ofReal eps) :
    Tendsto (fun n => localSobolevENN s (f n)) atTop (𝓝 (localSobolevENN s g)) := by
  simp_rw [localSobolevENN_eq_norm (hf _), localSobolevENN_eq_norm hg]
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (localBesselRepresentative_tendsto hf hg hc).norm

theorem localSobolevENN_sub_tendsto {s : ℝ}
    {f : ℕ → SobolevModel → ℝ} {g u : SobolevModel → ℝ}
    (hf : ∀ n, LocalSobolevMem s (f n)) (hg : LocalSobolevMem s g)
    (hu : LocalSobolevMem s u)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      localSobolevENN s (f i - g) < ENNReal.ofReal eps) :
    Tendsto (fun n => localSobolevENN s (u - f n)) atTop
      (𝓝 (localSobolevENN s (u - g))) := by
  simp_rw [localSobolevENN_sub_eq_norm hu (hf _), localSobolevENN_sub_eq_norm hu hg]
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_const_nhds.sub (localBesselRepresentative_tendsto hf hg hc)).norm

theorem localSobolevENN_definite_continuous {s : ℝ} {f : SobolevModel → ℝ}
    (hfc : Continuous f) (hf : LocalSobolevMem s f)
    (hz : localSobolevENN s f = 0) : f = 0 := by
  have hfl := hf.choose
  have hzl : MemLp (complexifyLocal (0 : SobolevModel → ℝ)) 2 volume := by
    change MemLp (fun _ : SobolevModel => (0 : ℂ)) 2 volume
    exact MemLp.zero'
  apply localFunctionDistribution_injective_continuous hfc continuous_const hfl hzl
  have hdist : localFunctionDistribution f hfl = 0 := by
    apply (exact_bessel_sectionBanachSpace s).definite _ hf.choose_spec
    simpa only [localSobolevENN, dif_pos hfl] using hz
  rw [hdist]
  unfold localFunctionDistribution
  rw [← Lp.toTemperedDistributionCLM_apply]
  change (0 : LocalDistribution) = (Lp.toTemperedDistributionCLM ℂ volume 2) (0 : LocalL2)
  exact (map_zero _).symm

end K24.Global.SobolevGlobal

/- Exact original-norm adapter from frozen K24SOBPERP_Functional.lean. -/
namespace K24.Global.SectionBanachSpace

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}

/-- The submodule consists of the original admissible sections. -/
def submodule (h : SectionBanachSpace S nx) : Submodule ℝ X where
  carrier := S
  zero_mem' := h.zero_mem
  add_mem' := fun hu hv => h.add_mem _ hu _ hv
  smul_mem' := fun c _ hu => h.smul_mem c _ hu

/-- The real norm is obtained from the finite, supplied section norm. -/
@[instance_reducible]
def sectionNorm (h : SectionBanachSpace S nx) : Norm h.submodule :=
  ⟨fun u => (nx u).toReal⟩

theorem normCore (h : SectionBanachSpace S nx) :
    letI := h.sectionNorm
    NormedSpace.Core ℝ h.submodule := by
  letI := h.sectionNorm
  refine
    { norm_nonneg := fun _ => ENNReal.toReal_nonneg
      norm_smul := ?_
      norm_triangle := ?_
      norm_eq_zero_iff := ?_ }
  · intro c u
    change (nx (c • (u : X))).toReal = ‖c‖ * (nx u).toReal
    rw [h.homogeneous c u u.property, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]
  · intro u v
    change (nx ((u : X) + v)).toReal ≤ (nx u).toReal + (nx v).toReal
    calc
      _ ≤ (nx u + nx v).toReal := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨(h.finite u u.property).ne,
          (h.finite v v.property).ne⟩) (h.triangle u u.property v v.property)
      _ = _ := ENNReal.toReal_add (h.finite u u.property).ne (h.finite v v.property).ne
  · intro u
    change (nx u).toReal = 0 ↔ u = 0
    constructor
    · intro hu
      apply Subtype.ext
      exact h.definite u u.property
        ((ENNReal.toReal_eq_zero_iff _).mp hu |>.resolve_right (h.finite u u.property).ne)
    · intro hu
      subst u
      simp [h.zero_norm]

/-- A normed group on the original section submodule, with its given norm. -/
abbrev normedAddCommGroup (h : SectionBanachSpace S nx) :
    NormedAddCommGroup h.submodule :=
  letI := h.sectionNorm
  NormedAddCommGroup.ofCore h.normCore

/-- The scalar action remains the original pointwise scalar action. -/
abbrev normedSpace (h : SectionBanachSpace S nx) :
    letI := h.normedAddCommGroup
    NormedSpace ℝ h.submodule :=
  letI := h.normedAddCommGroup
  NormedSpace.ofCore h.normCore

theorem norm_eq_toReal (h : SectionBanachSpace S nx) (u : h.submodule) :
    letI := h.normedAddCommGroup
    ‖u‖ = (nx u).toReal := rfl

theorem ofReal_norm (h : SectionBanachSpace S nx) (u : h.submodule) :
    letI := h.normedAddCommGroup
    ENNReal.ofReal ‖u‖ = nx u :=
  ENNReal.ofReal_toReal (h.finite u u.property).ne

/-- The explicit section Cauchy-sequence axiom supplies completeness of the
actual section norm, without completing or enlarging the section space. -/
theorem completeSpace (h : SectionBanachSpace S nx) :
    letI := h.normedAddCommGroup
    CompleteSpace h.submodule := by
  letI := h.normedAddCommGroup
  apply Metric.complete_of_cauchySeq_tendsto
  intro f hf
  obtain ⟨v, hv, hlim⟩ := h.complete (fun n => f n) (fun n => (f n).property) (by
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    have hij := hN i hi j hj
    rw [dist_eq_norm] at hij
    have hh := (ENNReal.ofReal_lt_ofReal_iff heps).mpr hij
    rwa [h.ofReal_norm (f i - f j)] at hh)
  refine ⟨⟨v, hv⟩, Metric.tendsto_atTop.mpr ?_⟩
  intro eps heps
  obtain ⟨N, hN⟩ := hlim eps heps
  refine ⟨N, fun i hi => ?_⟩
  rw [dist_eq_norm]
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
  rw [h.ofReal_norm]
  exact hN i hi

end K24.Global.SectionBanachSpace

/- Exact ENNReal square-sum laws from frozen K24SOBGLOBAL_NormLaws.lean. -/
namespace K24.Global.SobolevGlobal
theorem enorm_l2_add_le {ι : Type*} (f g : ι → ℝ≥0∞) :
    (∑' i, (f i + g i) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤
      (∑' i, f i ^ (2 : ℕ)) ^ (1 / 2 : ℝ) +
      (∑' i, g i ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  rw [one_div, ENNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 2)]
  apply ENNReal.summable.tsum_le_of_sum_le
  intro t
  apply (ENNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 2)).mp
  have hm := ENNReal.Lp_add_le (s := t) (f := f) (g := g) (by norm_num : (1 : ℝ) ≤ 2)
  simp only [ENNReal.rpow_two, one_div] at hm
  refine hm.trans (add_le_add ?_ ?_)
  · exact ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum t) (by positivity)
  · exact ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum t) (by positivity)

theorem enorm_l2_mul {ι : Type*} (c : ℝ≥0∞) (f : ι → ℝ≥0∞) :
    (∑' i, (c * f i) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) =
      c * (∑' i, f i ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  simp_rw [mul_pow]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num


end K24.Global.SobolevGlobal

/- Reused checked source: K24SOBINV_Matrix.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped NNReal ENNReal BigOperators

namespace K24.Global.SobolevInverse
open SobolevGlobal SobolevAlgebra

theorem matrixSobolevENN_sq (r : ℝ) (F : FourSpace → Mat4) :
    matrixSobolevENN r F ^ (2 : ℕ) =
      ∑ i : Fin 4, ∑ j : Fin 4, localSobolevENN r (fun x => F x i j) ^ (2 : ℕ) := by
  unfold matrixSobolevENN
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Every actual matrix entry is controlled by the original matrix norm. -/
theorem localSobolevENN_le_matrix (r : ℝ) (F : FourSpace → Mat4) (i j : Fin 4) :
    localSobolevENN r (fun x => F x i j) ≤ matrixSobolevENN r F := by
  apply (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp
  rw [matrixSobolevENN_sq]
  have hrow : localSobolevENN r (fun x => F x i j) ^ (2 : ℕ) ≤
      ∑ k : Fin 4, localSobolevENN r (fun x => F x i k) ^ (2 : ℕ) :=
    Finset.single_le_sum
      (f := fun k : Fin 4 => localSobolevENN r (fun x => F x i k) ^ (2 : ℕ))
      (fun _ _ => bot_le) (Finset.mem_univ j)
  exact hrow.trans (Finset.single_le_sum
    (f := fun i : Fin 4 => ∑ j : Fin 4, localSobolevENN r (fun x => F x i j) ^ (2 : ℕ))
    (fun _ _ => bot_le) (Finset.mem_univ i))

theorem matrix_entry_mem_of_finite {r : ℝ} {F : FourSpace → Mat4}
    (hF : matrixSobolevENN r F < ⊤) (i j : Fin 4) :
    LocalSobolevMem r (fun x => F x i j) :=
  (localSobolevENN_lt_top_iff _ _).mp ((localSobolevENN_le_matrix r F i j).trans_lt hF)

/-- Four by four matrices have sixteen entries, so a uniform entry bound
gives the exact elementary factor four in their original square-sum norm. -/
theorem matrixSobolevENN_le_four_mul {r : ℝ} {F : FourSpace → Mat4}
    (K : ℝ≥0∞) (hF : ∀ i j, localSobolevENN r (fun x => F x i j) ≤ K) :
    matrixSobolevENN r F ≤ 4 * K := by
  apply (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp
  rw [matrixSobolevENN_sq]
  calc
    _ ≤ ∑ _i : Fin 4, ∑ _j : Fin 4, K ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left' (hF i j) 2
    _ = _ := by simp; ring

/-- Finite sums preserve original local membership and obey the original
triangle inequality, before any new normed-space structure is introduced. -/
theorem localSobolev_finset_sum {ι : Type*} (r : ℝ) (S : Finset ι)
    (f : ι → FourSpace → ℝ) (hf : ∀ i ∈ S, LocalSobolevMem r (f i)) :
    LocalSobolevMem r (∑ i ∈ S, f i) ∧
      localSobolevENN r (∑ i ∈ S, f i) ≤ ∑ i ∈ S, localSobolevENN r (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact ⟨(localSobolevENN_lt_top_iff r 0).mp (by simp), by simp⟩
  | @insert a S ha ih =>
      have hfa := hf a (Finset.mem_insert_self a S)
      have hfs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      simp only [Finset.sum_insert ha]
      exact ⟨localSobolevMem_add hfa hfs.1,
        (localSobolevENN_add_le hfa hfs.1).trans (add_le_add le_rfl hfs.2)⟩

/-- Actual finite matrix contraction using the real-order local Sobolev
algebra. The explicit dimension constant is 64: sixteen triple-product
summands per entry and four from the matrix square-sum norm. -/
theorem matrixSobolev_triple_product (r : ℝ) (A : ℝ≥0)
    (hA : ∀ f g : FourSpace → ℝ, LocalSobolevMem r f → LocalSobolevMem r g →
      LocalSobolevMem r (f * g) ∧ localSobolevENN r (f * g) ≤
        (A : ℝ≥0∞) * localSobolevENN r f * localSobolevENN r g)
    (F G H : FourSpace → Mat4)
    (hF : ∀ i j, LocalSobolevMem r (fun x => F x i j))
    (hG : ∀ i j, LocalSobolevMem r (fun x => G x i j))
    (hH : ∀ i j, LocalSobolevMem r (fun x => H x i j)) :
    (∀ i j, LocalSobolevMem r (fun x => (F x * G x * H x) i j)) ∧
      matrixSobolevENN r (fun x => F x * G x * H x) ≤
        ((64 * A ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) *
          matrixSobolevENN r F * matrixSobolevENN r G * matrixSobolevENN r H := by
  let Q : ℝ≥0∞ := (A : ℝ≥0∞) ^ (2 : ℕ) *
    matrixSobolevENN r F * matrixSobolevENN r G * matrixSobolevENN r H
  have hterm (i j k l : Fin 4) :
      LocalSobolevMem r (fun x => F x i l * G x l k * H x k j) ∧
      localSobolevENN r (fun x => F x i l * G x l k * H x k j) ≤ Q := by
    obtain ⟨hFG, hFGb⟩ := hA (fun x => F x i l) (fun x => G x l k) (hF i l) (hG l k)
    obtain ⟨hFGH, hFGHb⟩ := hA _ (fun x => H x k j) hFG (hH k j)
    refine ⟨hFGH, hFGHb.trans ?_⟩
    calc
      _ ≤ (A : ℝ≥0∞) * ((A : ℝ≥0∞) * localSobolevENN r (fun x => F x i l) *
          localSobolevENN r (fun x => G x l k)) * localSobolevENN r (fun x => H x k j) :=
        mul_le_mul (mul_le_mul le_rfl hFGb bot_le bot_le) le_rfl bot_le bot_le
      _ ≤ (A : ℝ≥0∞) * ((A : ℝ≥0∞) * matrixSobolevENN r F * matrixSobolevENN r G) *
          matrixSobolevENN r H := by
        gcongr
        · exact localSobolevENN_le_matrix r F i l
        · exact localSobolevENN_le_matrix r G l k
        · exact localSobolevENN_le_matrix r H k j
      _ = Q := by dsimp [Q]; ring
  have hentry (i j : Fin 4) :
      LocalSobolevMem r (fun x => (F x * G x * H x) i j) ∧
      localSobolevENN r (fun x => (F x * G x * H x) i j) ≤ 16 * Q := by
    have hrow (k : Fin 4) := localSobolev_finset_sum r Finset.univ
      (fun l : Fin 4 => fun x => F x i l * G x l k * H x k j)
      (fun l _ => (hterm i j k l).1)
    have hsum := localSobolev_finset_sum r Finset.univ
      (fun k : Fin 4 => ∑ l : Fin 4, fun x => F x i l * G x l k * H x k j)
      (fun k _ => (hrow k).1)
    have heq : (fun x => (F x * G x * H x) i j) =
        ∑ k : Fin 4, ∑ l : Fin 4, fun x => F x i l * G x l k * H x k j := by
      funext x
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.sum_apply]
    rw [heq]
    refine ⟨hsum.1, hsum.2.trans ?_⟩
    calc
      _ ≤ ∑ k : Fin 4, ∑ l : Fin 4,
          localSobolevENN r (fun x => F x i l * G x l k * H x k j) :=
        Finset.sum_le_sum (fun k _ => (hrow k).2)
      _ ≤ ∑ _k : Fin 4, ∑ _l : Fin 4, Q := by
        exact Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => (hterm i j k l).2))
      _ = 16 * Q := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
  refine ⟨fun i j => (hentry i j).1, ?_⟩
  calc
    _ ≤ 4 * (16 * Q) := matrixSobolevENN_le_four_mul _ (fun i j => (hentry i j).2)
    _ = _ := by dsimp [Q]; ring

end K24.Global.SobolevInverse


/- Reused checked source: K24SOBMATRIX_Algebra.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped NNReal ENNReal BigOperators
namespace K24.Global.SobolevMatrix
open SobolevGlobal SobolevAlgebra SobolevInverse

/-- Finiteness of the original Frobenius square-sum norm follows from the
sixteen actual original local Sobolev membership witnesses. -/
theorem matrixSobolevENN_finite_of_mem {r : ℝ} {F : FourSpace → Mat4}
    (hF : ∀ i j, LocalSobolevMem r (fun x => F x i j)) : matrixSobolevENN r F < ⊤ := by
  unfold matrixSobolevENN
  apply (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mpr
  apply ENNReal.sum_lt_top.mpr
  intro i _
  apply ENNReal.sum_lt_top.mpr
  intro j _
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using
    (localSobolevENN_lt_top_iff _ _).mpr (hF i j)

/-- Exact original matrix norm triangle inequality. -/
theorem matrixSobolevENN_add_le {r : ℝ} {F G : FourSpace → Mat4}
    (hF : ∀ i j, LocalSobolevMem r (fun x => F x i j))
    (hG : ∀ i j, LocalSobolevMem r (fun x => G x i j)) :
    matrixSobolevENN r (F + G) ≤ matrixSobolevENN r F + matrixSobolevENN r G := by
  calc
    _ ≤ (∑ i : Fin 4, ∑ j : Fin 4,
        (localSobolevENN r (fun x => F x i j) +
          localSobolevENN r (fun x => G x i j)) ^ (2 : ℕ)) ^ (1/2 : ℝ) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left' (localSobolevENN_add_le (hF i j) (hG i j)) 2
    _ ≤ _ := by
      simpa only [matrixSobolevENN, tsum_fintype, Fintype.sum_prod_type] using
        (enorm_l2_add_le
          (fun ij : Fin 4 × Fin 4 => localSobolevENN r (fun x => F x ij.1 ij.2))
          (fun ij : Fin 4 × Fin 4 => localSobolevENN r (fun x => G x ij.1 ij.2)))

theorem matrixSobolevENN_smul {r : ℝ} {F : FourSpace → Mat4}
    (hF : ∀ i j, LocalSobolevMem r (fun x => F x i j)) (c : ℝ) :
    matrixSobolevENN r (c • F) = ENNReal.ofReal |c| * matrixSobolevENN r F := by
  unfold matrixSobolevENN
  have hentry (i j : Fin 4) : localSobolevENN r (fun x => (c • F) x i j) =
      ENNReal.ofReal |c| * localSobolevENN r (fun x => F x i j) :=
    localSobolevENN_smul (hF i j) c
  simp_rw [hentry]
  simpa only [tsum_fintype, Fintype.sum_prod_type] using
    (enorm_l2_mul (ENNReal.ofReal |c|)
      (fun ij : Fin 4 × Fin 4 => localSobolevENN r (fun x => F x ij.1 ij.2)))

@[simp] theorem matrixSobolevENN_zero (r : ℝ) : matrixSobolevENN r 0 = 0 := by
  change (∑ _i : Fin 4, ∑ _j : Fin 4,
    localSobolevENN r (0 : FourSpace → ℝ) ^ (2 : ℕ)) ^ (1/2 : ℝ) = 0
  simp

theorem matrixSobolevENN_neg {r : ℝ} {F : FourSpace → Mat4}
    (hF : ∀ i j, LocalSobolevMem r (fun x => F x i j)) :
    matrixSobolevENN r (-F) = matrixSobolevENN r F := by
  simpa using matrixSobolevENN_smul hF (-1)

theorem matrixSobolevENN_sub_le {r : ℝ} {F G : FourSpace → Mat4}
    (hF : ∀ i j, LocalSobolevMem r (fun x => F x i j))
    (hG : ∀ i j, LocalSobolevMem r (fun x => G x i j)) :
    matrixSobolevENN r (F - G) ≤ matrixSobolevENN r F + matrixSobolevENN r G := by
  have hneg (i j : Fin 4) : LocalSobolevMem r (fun x => (-G) x i j) := by
    change LocalSobolevMem r (-(fun x => G x i j))
    simpa using localSobolevMem_smul (hG i j) (-1)
  simpa only [sub_eq_add_neg, matrixSobolevENN_neg hG] using matrixSobolevENN_add_le hF hneg

/-- Actual pointwise matrix multiplication in the unchanged Frobenius
square-sum norm. Four summands per entry and four from the sixteen-entry norm
give the explicit safe constant 16 times the scalar algebra constant. -/
theorem matrixSobolev_product (r : ℝ) (A : ℝ≥0)
    (hA : ∀ f g : FourSpace → ℝ, LocalSobolevMem r f → LocalSobolevMem r g →
      LocalSobolevMem r (f*g) ∧ localSobolevENN r (f*g) ≤
        (A : ℝ≥0∞) * localSobolevENN r f * localSobolevENN r g)
    (F G : FourSpace → Mat4)
    (hF : ∀ i j, LocalSobolevMem r (fun x => F x i j))
    (hG : ∀ i j, LocalSobolevMem r (fun x => G x i j)) :
    (∀ i j, LocalSobolevMem r (fun x => (F x * G x) i j)) ∧
      matrixSobolevENN r (fun x => F x * G x) ≤
        ((16*A : ℝ≥0) : ℝ≥0∞) * matrixSobolevENN r F * matrixSobolevENN r G := by
  let Q : ℝ≥0∞ := (A : ℝ≥0∞) * matrixSobolevENN r F * matrixSobolevENN r G
  have hterm (i j k : Fin 4) :
      LocalSobolevMem r (fun x => F x i k * G x k j) ∧
      localSobolevENN r (fun x => F x i k * G x k j) ≤ Q := by
    obtain ⟨hm, hb⟩ := hA _ _ (hF i k) (hG k j)
    refine ⟨hm, hb.trans ?_⟩
    exact mul_le_mul (mul_le_mul le_rfl (localSobolevENN_le_matrix r F i k) bot_le bot_le)
      (localSobolevENN_le_matrix r G k j) bot_le bot_le
  have hentry (i j : Fin 4) :
      LocalSobolevMem r (fun x => (F x * G x) i j) ∧
      localSobolevENN r (fun x => (F x * G x) i j) ≤ 4 * Q := by
    have hsum := localSobolev_finset_sum r Finset.univ
      (fun k : Fin 4 => fun x => F x i k * G x k j) (fun k _ => (hterm i j k).1)
    have heq : (fun x => (F x * G x) i j) =
        ∑ k : Fin 4, fun x => F x i k * G x k j := by
      funext x
      simp only [Matrix.mul_apply, Finset.sum_apply]
    rw [heq]
    refine ⟨hsum.1, hsum.2.trans ?_⟩
    calc
      _ ≤ ∑ _k : Fin 4, Q := Finset.sum_le_sum (fun k _ => (hterm i j k).2)
      _ = _ := by simp
  refine ⟨fun i j => (hentry i j).1, ?_⟩
  calc
    _ ≤ 4 * (4 * Q) := matrixSobolevENN_le_four_mul _ (fun i j => (hentry i j).2)
    _ = _ := by dsimp [Q]; ring

/-- Original real-order local matrix algebra, with one finite constant for all
actual Mat4 coefficient functions, for every real r > 2. -/
theorem matrixSobolev_algebra (r : ℝ) (hr : 2 < r) :
    ∃ B : ℝ≥0, ∀ F G : FourSpace → Mat4,
      (∀ i j, LocalSobolevMem r (fun x => F x i j)) →
      (∀ i j, LocalSobolevMem r (fun x => G x i j)) →
      (∀ i j, LocalSobolevMem r (fun x => (F x * G x) i j)) ∧
        matrixSobolevENN r (fun x => F x * G x) ≤
          (B : ℝ≥0∞) * matrixSobolevENN r F * matrixSobolevENN r G := by
  obtain ⟨A, hA⟩ := localSobolev_algebra r hr
  exact ⟨16*A, fun F G hF hG => matrixSobolev_product r A hA F G hF hG⟩

end K24.Global.SobolevMatrix

/- Reused checked source: K24SOBMATRIX_Banach.lean. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Filter
open scoped NNReal ENNReal Topology BigOperators
namespace K24.Global.SobolevMatrix
open SobolevGlobal SobolevInverse

/-- Actual continuous Mat4 coefficient functions in the original real-order
local class. Constants are not added to this L2 carrier. -/
def continuousMatrixSobolevSpace (r : ℝ) : Set (FourSpace → Mat4) :=
  {F | ∀ i j, Continuous (fun x => F x i j) ∧ LocalSobolevMem r (fun x => F x i j)}

theorem continuous_of_mem {r : ℝ} {F : FourSpace → Mat4}
    (hF : F ∈ continuousMatrixSobolevSpace r) : Continuous F :=
  continuous_pi fun i => continuous_pi fun j => (hF i j).1

/-- Sixteen faithful scalar completions reconstruct an actual continuous
matrix function. The final norm convergence uses the unchanged Frobenius
square sum, not a replacement maximum or entry-sum norm. -/
theorem continuous_matrix_Cauchy_limit (r : ℝ) (hr : 2 < r)
    (F : ℕ → FourSpace → Mat4) (hF : ∀ n, F n ∈ continuousMatrixSobolevSpace r)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      matrixSobolevENN r (F p - F q) < ENNReal.ofReal eps) :
    ∃ G ∈ continuousMatrixSobolevSpace r,
      ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ p ≥ N,
        matrixSobolevENN r (F p - G) < ENNReal.ofReal eps := by
  classical
  have hlim (i j : Fin 4) := localSobolev_Cauchy_limit hr
    (fun n x => F n x i j) (fun n => (hF n i j).1) (fun n => (hF n i j).2)
    (by
      intro eps heps
      obtain ⟨N, hN⟩ := hc eps heps
      refine ⟨N, fun p hp q hq => ?_⟩
      exact (localSobolevENN_le_matrix r (F p-F q) i j).trans_lt (hN p hp q hq))
  choose g hgc hgm hgconv hgpoint using hlim
  let G : FourSpace → Mat4 := fun x i j => g i j x
  refine ⟨G, fun i j => ⟨hgc i j, hgm i j⟩, ?_⟩
  intro eps heps
  have hlocal (i j : Fin 4) : ∀ᶠ n : ℕ in atTop,
      localSobolevENN r (fun x => (F n-G) x i j) < ENNReal.ofReal (eps/8) := by
    obtain ⟨N, hN⟩ := hgconv i j (eps/8) (by positivity)
    exact eventually_atTop.mpr ⟨N, hN⟩
  have hall : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin 4,
      localSobolevENN r (fun x => (F n-G) x i j) < ENNReal.ofReal (eps/8) :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hlocal i j
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  refine ⟨N, fun n hn => ?_⟩
  calc
    _ ≤ 4 * ENNReal.ofReal (eps/8) :=
      matrixSobolevENN_le_four_mul _ (fun i j => (hN n hn i j).le)
    _ < ENNReal.ofReal eps := by
      have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) := by norm_num
      rw [h4, ← ENNReal.ofReal_mul (by norm_num)]
      exact (ENNReal.ofReal_lt_ofReal_iff heps).mpr (by linarith)

/-- The actual continuous matrix carrier is complete in the original canonical
matrixSobolevENN, at every real order r > 2. -/
theorem continuousMatrix_sectionBanachSpace (r : ℝ) (hr : 2 < r) :
    SectionBanachSpace (continuousMatrixSobolevSpace r) (matrixSobolevENN r) where
  zero_mem := by
    intro i j
    exact ⟨continuous_const, (localSobolevENN_lt_top_iff r 0).mp (by simp)⟩
  add_mem := by
    intro F hF G hG i j
    exact ⟨(hF i j).1.add (hG i j).1, localSobolevMem_add (hF i j).2 (hG i j).2⟩
  smul_mem := by
    intro c F hF i j
    exact ⟨(hF i j).1.const_smul c, localSobolevMem_smul (hF i j).2 c⟩
  finite := fun F hF => matrixSobolevENN_finite_of_mem (fun i j => (hF i j).2)
  zero_norm := matrixSobolevENN_zero r
  definite := by
    intro F hF hz
    funext x i j
    have hzero : localSobolevENN r (fun y => F y i j) = 0 :=
      le_antisymm ((localSobolevENN_le_matrix r F i j).trans_eq hz) bot_le
    exact congrFun (localSobolevENN_definite_continuous (hF i j).1 (hF i j).2 hzero) x
  triangle := fun F hF G hG => matrixSobolevENN_add_le
    (fun i j => (hF i j).2) (fun i j => (hG i j).2)
  homogeneous := fun c F hF => matrixSobolevENN_smul (fun i j => (hF i j).2) c
  complete := continuous_matrix_Cauchy_limit r hr

/-- Multiplication remains the actual pointwise Mat4 product on this complete
carrier; the finite bound is measured in the original canonical matrix norm. -/
theorem continuousMatrix_banach_algebra (r : ℝ) (hr : 2 < r) :
    SectionBanachSpace (continuousMatrixSobolevSpace r) (matrixSobolevENN r) ∧
    ∃ B : ℝ≥0, ∀ F ∈ continuousMatrixSobolevSpace r,
      ∀ G ∈ continuousMatrixSobolevSpace r,
      (fun x => F x * G x) ∈ continuousMatrixSobolevSpace r ∧
        matrixSobolevENN r (fun x => F x * G x) ≤
          (B : ℝ≥0∞) * matrixSobolevENN r F * matrixSobolevENN r G := by
  obtain ⟨B, hB⟩ := matrixSobolev_algebra r hr
  refine ⟨continuousMatrix_sectionBanachSpace r hr, B, ?_⟩
  intro F hF G hG
  obtain ⟨hmem, hb⟩ := hB F G (fun i j => (hF i j).2) (fun i j => (hG i j).2)
  refine ⟨fun i j => ⟨?_, hmem i j⟩, hb⟩
  simp only [Matrix.mul_apply]
  exact continuous_finsetSum _ (fun k _ => (hF i k).1.mul (hG k j).1)

end K24.Global.SobolevMatrix

/- Reused checked source: K24SOBNEUMANN_Space.lean. -/

set_option autoImplicit false
open MeasureTheory FourierTransform TemperedDistribution Filter
open scoped ENNReal NNReal Topology

namespace K24.Global.SobolevNeumann

/-- Genuine continuous real local coefficients in the original Bessel space. -/
def continuousLocalSpace (r : ℝ) : Set (SobolevModel → ℝ) :=
  {u | Continuous u ∧ LocalSobolevMem r u}

/-- The original local norm is complete on genuine continuous coefficients.
This only packages the previously checked faithful local completeness theorem. -/
theorem continuousLocal_sectionBanachSpace (r : ℝ) (hr : 2 < r) :
    SectionBanachSpace (continuousLocalSpace r) (localSobolevENN r) := by
  refine
    { zero_mem := ⟨continuous_const, ?_⟩
      add_mem := fun u hu v hv => ⟨hu.1.add hv.1, SobolevGlobal.localSobolevMem_add hu.2 hv.2⟩
      smul_mem := fun c u hu => ⟨continuous_const.smul hu.1,
        SobolevGlobal.localSobolevMem_smul hu.2 c⟩
      finite := fun u hu => (localSobolevENN_lt_top_iff r u).mpr hu.2
      zero_norm := localSobolevENN_zero r
      definite := fun u hu hz => SobolevGlobal.localSobolevENN_definite_continuous hu.1 hu.2 hz
      triangle := fun u hu v hv => SobolevGlobal.localSobolevENN_add_le hu.2 hv.2
      homogeneous := fun c u hu => SobolevGlobal.localSobolevENN_smul hu.2 c
      complete := ?_ }
  · exact (localSobolevENN_lt_top_iff r 0).mp (by simp)
  · intro f hf hc
    obtain ⟨g, hgc, hgm, hconv, _⟩ := SobolevGlobal.localSobolev_Cauchy_limit hr f
      (fun n => (hf n).1) (fun n => (hf n).2) hc
    exact ⟨g, ⟨hgc, hgm⟩, hconv⟩

/-- Pointwise multiplication on the actual continuous local Sobolev subspace. -/
def mulLocal {r : ℝ} (hr : 2 < r)
    (u v : (continuousLocal_sectionBanachSpace r hr).submodule) :
    (continuousLocal_sectionBanachSpace r hr).submodule := by
  refine ⟨(u : SobolevModel → ℝ) * (v : SobolevModel → ℝ),
    u.property.1.mul v.property.1, ?_⟩
  obtain ⟨A, hA⟩ := SobolevAlgebra.localSobolev_algebra r hr
  exact (hA _ _ u.property.2 v.property.2).1

@[simp] theorem mulLocal_coe {r : ℝ} (hr : 2 < r)
    (u v : (continuousLocal_sectionBanachSpace r hr).submodule) :
    ((mulLocal hr u v : (continuousLocal_sectionBanachSpace r hr).submodule) :
      SobolevModel → ℝ) = (u : SobolevModel → ℝ) * (v : SobolevModel → ℝ) := rfl

@[simp] theorem mulLocal_zero {r : ℝ} (hr : 2 < r)
    (u : (continuousLocal_sectionBanachSpace r hr).submodule) :
    mulLocal hr u 0 = 0 := by
  apply Subtype.ext
  simp [mulLocal_coe]

theorem mulLocal_sub_right {r : ℝ} (hr : 2 < r)
    (u v w : (continuousLocal_sectionBanachSpace r hr).submodule) :
    mulLocal hr u (v - w) = mulLocal hr u v - mulLocal hr u w := by
  apply Subtype.ext
  simp only [mulLocal_coe, Submodule.coe_sub]
  exact mul_sub _ _ _

/-- The multiplication estimate in the norm furnished by the exact-norm adapter. -/
theorem norm_mulLocal_le {r : ℝ} (hr : 2 < r) (A : ℝ≥0)
    (hA : ∀ f g : SobolevModel → ℝ, LocalSobolevMem r f → LocalSobolevMem r g →
      localSobolevENN r (f * g) ≤ (A : ℝ≥0∞) * localSobolevENN r f * localSobolevENN r g) :
    letI := (continuousLocal_sectionBanachSpace r hr).normedAddCommGroup
    ∀ u v : (continuousLocal_sectionBanachSpace r hr).submodule,
      ‖mulLocal hr u v‖ ≤ (A : ℝ) * ‖u‖ * ‖v‖ := by
  let hS := continuousLocal_sectionBanachSpace r hr
  letI := hS.normedAddCommGroup
  intro u v
  have hb := hA u v u.property.2 v.property.2
  have hfin : (A : ℝ≥0∞) * localSobolevENN r u * localSobolevENN r v ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (hS.finite u u.property)) (hS.finite v v.property)).ne
  have hh := ENNReal.toReal_mono hfin hb
  rw [hS.norm_eq_toReal (mulLocal hr u v), hS.norm_eq_toReal u, hS.norm_eq_toReal v]
  simpa only [mulLocal_coe, ENNReal.toReal_mul, ENNReal.coe_toReal] using hh

end K24.Global.SobolevNeumann

/- Reused checked source: K24SOBNEUMANN_FixedPoint.lean. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ENNReal NNReal Topology

namespace K24.Global.SobolevNeumann

/-- Banach's contraction argument on the genuine continuous local Sobolev
space produces an actual multiplicative inverse difference and a quadratic
remainder. The normed-space norm is exactly the original finite Bessel norm. -/
theorem neumann_fixed_point {r : ℝ} (hr : 2 < r) (A : ℝ≥0)
    (hA : ∀ f g : SobolevModel → ℝ, LocalSobolevMem r f → LocalSobolevMem r g →
      localSobolevENN r (f * g) ≤ (A : ℝ≥0∞) * localSobolevENN r f * localSobolevENN r g) :
    letI := (continuousLocal_sectionBanachSpace r hr).normedAddCommGroup
    ∀ u : (continuousLocal_sectionBanachSpace r hr).submodule,
      (A : ℝ) * ‖u‖ ≤ 1 / 2 →
      ∃ v : (continuousLocal_sectionBanachSpace r hr).submodule,
        (∀ x, (1 + (u : SobolevModel → ℝ) x) * (1 + (v : SobolevModel → ℝ) x) = 1) ∧
        ‖v‖ ≤ 2 * ‖u‖ ∧ ‖v + u‖ ≤ 2 * (A : ℝ) * ‖u‖ ^ 2 := by
  let hS := continuousLocal_sectionBanachSpace r hr
  letI := hS.normedAddCommGroup
  letI := hS.completeSpace
  intro u hsmall
  let F : hS.submodule → hS.submodule := fun v => -u - mulLocal hr u v
  have hdiff (v w : hS.submodule) : F v - F w = -(mulLocal hr u (v - w)) := by
    rw [mulLocal_sub_right]
    dsimp [F]
    abel
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) F := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro v w
    rw [dist_eq_norm, hdiff, norm_neg, dist_eq_norm]
    calc
      _ ≤ (A : ℝ) * ‖u‖ * ‖v - w‖ := norm_mulLocal_le hr A hA u (v - w)
      _ ≤ (1 / 2 : ℝ) * ‖v - w‖ :=
        mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      _ = _ := by norm_num
  let v : hS.submodule := ContractingWith.fixedPoint F hcontract
  have hfix : F v = v := hcontract.fixedPoint_isFixedPt
  have hvbound : ‖v‖ ≤ 2 * ‖u‖ := by
    have hh := hcontract.dist_fixedPoint_le (0 : hS.submodule)
    norm_num [dist_eq_norm, F, mulLocal_zero] at hh
    linarith
  have hsum : v + u = -(mulLocal hr u v) := by
    dsimp [F] at hfix
    calc
      v + u = (-u - mulLocal hr u v) + u := congrArg (fun q => q + u) hfix.symm
      _ = _ := by abel
  refine ⟨v, ?_, hvbound, ?_⟩
  · intro x
    have hh := congrArg (fun q : hS.submodule => (q : SobolevModel → ℝ) x) hfix
    change -(u : SobolevModel → ℝ) x -
      (u : SobolevModel → ℝ) x * (v : SobolevModel → ℝ) x =
      (v : SobolevModel → ℝ) x at hh
    nlinarith
  · rw [hsum, norm_neg]
    calc
      _ ≤ (A : ℝ) * ‖u‖ * ‖v‖ := norm_mulLocal_le hr A hA u v
      _ ≤ (A : ℝ) * ‖u‖ * (2 * ‖u‖) :=
        mul_le_mul_of_nonneg_left hvbound (by positivity)
      _ = _ := by ring

end K24.Global.SobolevNeumann

/- Reused checked source: K24SOBNEUMANN_Inverse.lean. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ENNReal NNReal Topology

namespace K24.Global.SobolevNeumann

/-- The scalar inverse difference; no claim that the constant function one
belongs to the local L2-based Sobolev space is needed. -/
def inverseDifference (u : SobolevModel → ℝ) : SobolevModel → ℝ :=
  fun x => (1 + u x)⁻¹ - 1

/-- The actual first-order inverse remainder at zero. -/
def inverseRemainder (u : SobolevModel → ℝ) : SobolevModel → ℝ :=
  inverseDifference u + u

/-- Every real-order H^r, r > 2, has a genuine small-inverse neighborhood,
with the original local norm, linear inverse-difference bound and quadratic
remainder bound. Supplied coefficients only need their actual continuity and
original Sobolev membership. -/
theorem local_inverse_quadratic (r : ℝ) (hr : 2 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0, ∀ u : SobolevModel → ℝ,
      Continuous u → LocalSobolevMem r u →
      localSobolevENN r u < ENNReal.ofReal δ →
      (∀ x, 1 + u x ≠ 0) ∧
      Continuous (inverseDifference u) ∧ LocalSobolevMem r (inverseDifference u) ∧
      localSobolevENN r (inverseDifference u) ≤ 2 * localSobolevENN r u ∧
      Continuous (inverseRemainder u) ∧ LocalSobolevMem r (inverseRemainder u) ∧
      localSobolevENN r (inverseRemainder u) ≤ (C : ℝ≥0∞) * (localSobolevENN r u) ^ (2 : ℕ) := by
  obtain ⟨A, hA⟩ := SobolevAlgebra.localSobolev_algebra r hr
  let δ : ℝ := 1 / (2 * ((A : ℝ) + 1))
  have hδ : 0 < δ := by unfold δ; positivity
  refine ⟨δ, hδ, 2 * A, fun u huc hum husmall => ?_⟩
  let hS := continuousLocal_sectionBanachSpace r hr
  letI := hS.normedAddCommGroup
  let U : hS.submodule := ⟨u, huc, hum⟩
  have hUnorm : ENNReal.ofReal ‖U‖ = localSobolevENN r u := hS.ofReal_norm U
  have hUδ : ‖U‖ < δ := (ENNReal.ofReal_lt_ofReal_iff hδ).mp (by rwa [hUnorm])
  have hUhalf : (A : ℝ) * ‖U‖ ≤ 1 / 2 := by
    have hh : ‖U‖ * (2 * ((A : ℝ) + 1)) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < 2 * ((A : ℝ) + 1))).mp hUδ
    nlinarith [norm_nonneg U, A.coe_nonneg]
  obtain ⟨v, hvpoint, hvnorm, hvrem⟩ := neumann_fixed_point hr A
    (fun f g hf hg => (hA f g hf hg).2) U hUhalf
  have hnz (x : SobolevModel) : 1 + u x ≠ 0 := by
    intro hz
    have hh := hvpoint x
    change (1 + u x) * (1 + (v : SobolevModel → ℝ) x) = 1 at hh
    rw [hz, zero_mul] at hh
    norm_num at hh
  have hveq : (v : SobolevModel → ℝ) = inverseDifference u := by
    funext x
    have hh := hvpoint x
    change (1 + u x) * (1 + (v : SobolevModel → ℝ) x) = 1 at hh
    have he : 1 + (v : SobolevModel → ℝ) x = 1 / (1 + u x) :=
      (eq_div_iff (hnz x)).mpr (by nlinarith [hh])
    dsimp [inverseDifference]
    rw [one_div] at he
    linarith
  have hvsnorm : localSobolevENN r (inverseDifference u) ≤ 2 * localSobolevENN r u := by
    have hh := ENNReal.ofReal_le_ofReal hvnorm
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      hUnorm, hS.ofReal_norm v, hveq] at hh
    exact hh
  have hremcoe : ((v + U : hS.submodule) : SobolevModel → ℝ) = inverseRemainder u := by
    simp only [Submodule.coe_add, hveq, inverseRemainder]
    rfl
  have hremsnorm : localSobolevENN r (inverseRemainder u) ≤
      ((2 * A : ℝ≥0) : ℝ≥0∞) * (localSobolevENN r u) ^ (2 : ℕ) := by
    have hh := ENNReal.ofReal_le_ofReal hvrem
    rw [hS.ofReal_norm (v + U), hremcoe] at hh
    have he : ENNReal.ofReal (2 * (A : ℝ) * ‖U‖ ^ (2 : ℕ)) =
        ((2 * A : ℝ≥0) : ℝ≥0∞) * (localSobolevENN r u) ^ (2 : ℕ) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg U), hUnorm]
      congr 1
      exact ENNReal.ofReal_coe_nnreal (p := 2 * A)
    exact he ▸ hh
  refine ⟨hnz, hveq ▸ v.property.1, hveq ▸ v.property.2, hvsnorm,
    hremcoe ▸ (v + U).property.1, hremcoe ▸ (v + U).property.2, hremsnorm⟩

end K24.Global.SobolevNeumann

/- Reused checked source: K24SOBNEUMANN_MatrixSpace.lean. -/

set_option autoImplicit false
open scoped ENNReal NNReal Topology

namespace K24.Global.SobolevNeumann
open SobolevMatrix

/-- Actual pointwise matrix multiplication on the original complete matrix carrier. -/
def mulMatrixLocal {r : ℝ} (hr : 2 < r)
    (u v : (continuousMatrix_sectionBanachSpace r hr).submodule) :
    (continuousMatrix_sectionBanachSpace r hr).submodule := by
  refine ⟨fun x => (u : FourSpace → Mat4) x * (v : FourSpace → Mat4) x, ?_⟩
  obtain ⟨_, B, hB⟩ := continuousMatrix_banach_algebra r hr
  exact (hB u u.property v v.property).1

@[simp] theorem mulMatrixLocal_coe {r : ℝ} (hr : 2 < r)
    (u v : (continuousMatrix_sectionBanachSpace r hr).submodule) :
    ((mulMatrixLocal hr u v : (continuousMatrix_sectionBanachSpace r hr).submodule) :
      FourSpace → Mat4) = fun x => (u : FourSpace → Mat4) x * (v : FourSpace → Mat4) x := rfl

@[simp] theorem mulMatrixLocal_zero {r : ℝ} (hr : 2 < r)
    (u : (continuousMatrix_sectionBanachSpace r hr).submodule) :
    mulMatrixLocal hr u 0 = 0 := by
  apply Subtype.ext
  funext x
  simp [mulMatrixLocal_coe]

theorem mulMatrixLocal_sub_right {r : ℝ} (hr : 2 < r)
    (u v w : (continuousMatrix_sectionBanachSpace r hr).submodule) :
    mulMatrixLocal hr u (v - w) = mulMatrixLocal hr u v - mulMatrixLocal hr u w := by
  apply Subtype.ext
  funext x
  change (u : FourSpace → Mat4) x * ((v : FourSpace → Mat4) x - (w : FourSpace → Mat4) x) = _
  exact mul_sub _ _ _

theorem norm_mulMatrixLocal_le {r : ℝ} (hr : 2 < r) (A : ℝ≥0)
    (hA : ∀ f ∈ continuousMatrixSobolevSpace r, ∀ g ∈ continuousMatrixSobolevSpace r,
      matrixSobolevENN r (fun x => f x * g x) ≤
        (A : ℝ≥0∞) * matrixSobolevENN r f * matrixSobolevENN r g) :
    letI := (continuousMatrix_sectionBanachSpace r hr).normedAddCommGroup
    ∀ u v : (continuousMatrix_sectionBanachSpace r hr).submodule,
      ‖mulMatrixLocal hr u v‖ ≤ (A : ℝ) * ‖u‖ * ‖v‖ := by
  let hS := continuousMatrix_sectionBanachSpace r hr
  letI := hS.normedAddCommGroup
  intro u v
  have hb := hA u u.property v v.property
  have hfin : (A : ℝ≥0∞) * matrixSobolevENN r u * matrixSobolevENN r v ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (hS.finite u u.property)) (hS.finite v v.property)).ne
  have hh := ENNReal.toReal_mono hfin hb
  rw [hS.norm_eq_toReal (mulMatrixLocal hr u v), hS.norm_eq_toReal u, hS.norm_eq_toReal v]
  simpa only [mulMatrixLocal_coe, ENNReal.toReal_mul, ENNReal.coe_toReal] using hh

/-- The noncommutative Neumann contraction on the actual matrix Sobolev carrier. -/
theorem matrix_neumann_fixed_point {r : ℝ} (hr : 2 < r) (A : ℝ≥0)
    (hA : ∀ f ∈ continuousMatrixSobolevSpace r, ∀ g ∈ continuousMatrixSobolevSpace r,
      matrixSobolevENN r (fun x => f x * g x) ≤
        (A : ℝ≥0∞) * matrixSobolevENN r f * matrixSobolevENN r g) :
    letI := (continuousMatrix_sectionBanachSpace r hr).normedAddCommGroup
    ∀ u : (continuousMatrix_sectionBanachSpace r hr).submodule,
      (A : ℝ) * ‖u‖ ≤ 1 / 2 →
      ∃ v : (continuousMatrix_sectionBanachSpace r hr).submodule,
        (∀ x, (1 + (u : FourSpace → Mat4) x) * (1 + (v : FourSpace → Mat4) x) = 1) ∧
        ‖v‖ ≤ 2 * ‖u‖ ∧ ‖v + u‖ ≤ 2 * (A : ℝ) * ‖u‖ ^ 2 := by
  let hS := continuousMatrix_sectionBanachSpace r hr
  letI := hS.normedAddCommGroup
  letI := hS.completeSpace
  intro u hsmall
  let F : hS.submodule → hS.submodule := fun v => -u - mulMatrixLocal hr u v
  have hdiff (v w : hS.submodule) : F v - F w = -(mulMatrixLocal hr u (v - w)) := by
    rw [mulMatrixLocal_sub_right]
    dsimp [F]
    abel
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) F := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro v w
    rw [dist_eq_norm, hdiff, norm_neg, dist_eq_norm]
    calc
      _ ≤ (A : ℝ) * ‖u‖ * ‖v - w‖ := norm_mulMatrixLocal_le hr A hA u (v - w)
      _ ≤ (1 / 2 : ℝ) * ‖v - w‖ :=
        mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      _ = _ := by norm_num
  let v : hS.submodule := ContractingWith.fixedPoint F hcontract
  have hfix : F v = v := hcontract.fixedPoint_isFixedPt
  have hvbound : ‖v‖ ≤ 2 * ‖u‖ := by
    have hh := hcontract.dist_fixedPoint_le (0 : hS.submodule)
    norm_num [dist_eq_norm, F, mulMatrixLocal_zero] at hh
    linarith
  have hsum : v + u = -(mulMatrixLocal hr u v) := by
    dsimp [F] at hfix
    calc
      v + u = (-u - mulMatrixLocal hr u v) + u := congrArg (fun q => q + u) hfix.symm
      _ = _ := by abel
  refine ⟨v, ?_, hvbound, ?_⟩
  · intro x
    have hh := congrArg (fun q : hS.submodule => (q : FourSpace → Mat4) x) hfix
    change -(u : FourSpace → Mat4) x -
      (u : FourSpace → Mat4) x * (v : FourSpace → Mat4) x = (v : FourSpace → Mat4) x at hh
    have hz : (v : FourSpace → Mat4) x + (u : FourSpace → Mat4) x +
        (u : FourSpace → Mat4) x * (v : FourSpace → Mat4) x = 0 := by
      calc
        _ = (-(u : FourSpace → Mat4) x - (u : FourSpace → Mat4) x * (v : FourSpace → Mat4) x) +
            (u : FourSpace → Mat4) x + (u : FourSpace → Mat4) x * (v : FourSpace → Mat4) x :=
          congrArg (fun q => q + (u : FourSpace → Mat4) x +
            (u : FourSpace → Mat4) x * (v : FourSpace → Mat4) x) hh.symm
        _ = 0 := by abel
    calc
      _ = 1 + ((v : FourSpace → Mat4) x + (u : FourSpace → Mat4) x +
          (u : FourSpace → Mat4) x * (v : FourSpace → Mat4) x) := by noncomm_ring
      _ = 1 := by rw [hz, add_zero]
  · rw [hsum, norm_neg]
    calc
      _ ≤ (A : ℝ) * ‖u‖ * ‖v‖ := norm_mulMatrixLocal_le hr A hA u v
      _ ≤ (A : ℝ) * ‖u‖ * (2 * ‖u‖) :=
        mul_le_mul_of_nonneg_left hvbound (by positivity)
      _ = _ := by ring

end K24.Global.SobolevNeumann

/- Reused checked source: K24SOBNEUMANN_MatrixInverse.lean. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ENNReal NNReal Topology

namespace K24.Global.SobolevNeumann
open SobolevMatrix

/-- Actual nonsingular matrix inverse difference around the identity. -/
def matrixInverseDifference (u : FourSpace → Mat4) : FourSpace → Mat4 :=
  fun x => (1 + u x)⁻¹ - 1

/-- Actual first-order remainder for matrix inversion at the identity. -/
def matrixInverseRemainder (u : FourSpace → Mat4) : FourSpace → Mat4 :=
  matrixInverseDifference u + u

/-- Every real order r > 2 admits an actual matrix-inverse neighborhood in the
original Frobenius square-sum Bessel norm. The conclusions concern inverse
differences and remainders; the constant identity is never put in the L2 carrier. -/
theorem local_matrix_inverse_quadratic (r : ℝ) (hr : 2 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0, ∀ u : FourSpace → Mat4,
      u ∈ continuousMatrixSobolevSpace r →
      matrixSobolevENN r u < ENNReal.ofReal δ →
      (∀ x, (1 + u x).det ≠ 0) ∧
      Continuous (matrixInverseDifference u) ∧
      matrixInverseDifference u ∈ continuousMatrixSobolevSpace r ∧
      matrixSobolevENN r (matrixInverseDifference u) ≤ 2 * matrixSobolevENN r u ∧
      Continuous (matrixInverseRemainder u) ∧
      matrixInverseRemainder u ∈ continuousMatrixSobolevSpace r ∧
      matrixSobolevENN r (matrixInverseRemainder u) ≤
        (C : ℝ≥0∞) * (matrixSobolevENN r u) ^ (2 : ℕ) := by
  obtain ⟨_, A, hA⟩ := continuousMatrix_banach_algebra r hr
  let δ : ℝ := 1 / (2 * ((A : ℝ) + 1))
  have hδ : 0 < δ := by unfold δ; positivity
  refine ⟨δ, hδ, 2 * A, fun u hu husmall => ?_⟩
  let hS := continuousMatrix_sectionBanachSpace r hr
  letI := hS.normedAddCommGroup
  let U : hS.submodule := ⟨u, hu⟩
  have hUnorm : ENNReal.ofReal ‖U‖ = matrixSobolevENN r u := hS.ofReal_norm U
  have hUδ : ‖U‖ < δ := (ENNReal.ofReal_lt_ofReal_iff hδ).mp (by rwa [hUnorm])
  have hUhalf : (A : ℝ) * ‖U‖ ≤ 1 / 2 := by
    have hh : ‖U‖ * (2 * ((A : ℝ) + 1)) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < 2 * ((A : ℝ) + 1))).mp hUδ
    nlinarith [norm_nonneg U, A.coe_nonneg]
  obtain ⟨v, hvpoint, hvnorm, hvrem⟩ := matrix_neumann_fixed_point hr A
    (fun f hf g hg => (hA f hf g hg).2) U hUhalf
  have hnz (x : FourSpace) : (1 + u x).det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det (hvpoint x)
    change ((1 + u x) * (1 + (v : FourSpace → Mat4) x)).det = (1 : Mat4).det at hh
    rw [Matrix.det_mul, Matrix.det_one, hz, zero_mul] at hh
    norm_num at hh
  have hveq : (v : FourSpace → Mat4) = matrixInverseDifference u := by
    funext x
    have hh := hvpoint x
    change (1 + u x) * (1 + (v : FourSpace → Mat4) x) = 1 at hh
    have he := Matrix.inv_eq_right_inv hh
    dsimp [matrixInverseDifference]
    rw [he]
    abel
  have hvsnorm : matrixSobolevENN r (matrixInverseDifference u) ≤ 2 * matrixSobolevENN r u := by
    have hh := ENNReal.ofReal_le_ofReal hvnorm
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      hUnorm, hS.ofReal_norm v, hveq] at hh
    exact hh
  have hremcoe : ((v + U : hS.submodule) : FourSpace → Mat4) = matrixInverseRemainder u := by
    simp only [Submodule.coe_add, hveq, matrixInverseRemainder]
    rfl
  have hremsnorm : matrixSobolevENN r (matrixInverseRemainder u) ≤
      ((2 * A : ℝ≥0) : ℝ≥0∞) * (matrixSobolevENN r u) ^ (2 : ℕ) := by
    have hh := ENNReal.ofReal_le_ofReal hvrem
    rw [hS.ofReal_norm (v + U), hremcoe] at hh
    have he : ENNReal.ofReal (2 * (A : ℝ) * ‖U‖ ^ (2 : ℕ)) =
        ((2 * A : ℝ≥0) : ℝ≥0∞) * (matrixSobolevENN r u) ^ (2 : ℕ) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg U), hUnorm]
      congr 1
      exact ENNReal.ofReal_coe_nnreal (p := 2 * A)
    exact he ▸ hh
  refine ⟨hnz, hveq ▸ continuous_of_mem v.property, hveq ▸ v.property, hvsnorm,
    hremcoe ▸ continuous_of_mem (v + U).property, hremcoe ▸ (v + U).property, hremsnorm⟩

end K24.Global.SobolevNeumann

/- Checked source: K24SOBFRECHET_Quadratic.lean. -/

set_option autoImplicit false
open scoped ENNReal NNReal

namespace K24.Global.SobolevFrechet

/-- A proved quadratic remainder on an actual norm neighborhood gives the
canonical restricted Frechet derivative with derivative minus the identity.
The concrete applications below supply the mapping and remainder estimates
from the checked actual inverse functions. -/
theorem hasSectionFrechetDerivative_neg_of_quadratic
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (S : Set X) (nx : X → ℝ≥0∞) (hS : SectionBanachSpace S nx)
    (F : X → X) (hF0 : F 0 = 0) (δ : ℝ) (hδ : 0 < δ) (C : ℝ≥0)
    (hF : ∀ u ∈ S, nx u < ENNReal.ofReal δ → F u ∈ S)
    (hQ : ∀ u ∈ S, nx u < ENNReal.ofReal δ →
      nx (F u + u) ≤ (C : ℝ≥0∞) * (nx u) ^ (2 : ℕ)) :
    SectionNeighborhood S {u | u ∈ S ∧ nx u < ENNReal.ofReal δ} nx 0 ∧
    HasSectionFrechetDerivative S {u | u ∈ S ∧ nx u < ENNReal.ofReal δ} S
      nx nx F (fun h => -h) 0 := by
  have hneg (u : X) (hu : u ∈ S) : -u ∈ S := by
    simpa using hS.smul_mem (-1) u hu
  have hnormneg (u : X) (hu : u ∈ S) : nx (-u) = nx u := by
    simpa using hS.homogeneous (-1) u hu
  constructor
  · refine ⟨δ, hδ, ?_⟩
    intro h hh hn
    simpa only [zero_add, Set.mem_setOf_eq] using And.intro hh hn
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨hS.zero_mem, by rw [hS.zero_norm]; exact ENNReal.ofReal_pos.mpr hδ⟩
    · intro u hu
      exact hF u hu.1 hu.2
    · intro u hu
      exact hneg u hu
    · refine ⟨neg_zero, ?_, ?_⟩
      · intro u hu v hv
        exact neg_add u v
      · intro c u hu
        exact smul_neg c u |>.symm
    · refine ⟨1, fun u hu => ?_⟩
      simp only [hnormneg u hu, ENNReal.coe_one, one_mul, le_refl]
    · intro eps heps
      have hepsδ : 0 < eps / ((C : ℝ) + 1) := by positivity
      refine ⟨eps / ((C : ℝ) + 1), hepsδ, ?_⟩
      intro h hh hU hn
      have hsmall : nx h < ENNReal.ofReal δ := by
        simpa only [zero_add] using hU.2
      have hfinite : nx h ≠ ⊤ := (hS.finite h hh).ne
      have htoReal : ENNReal.ofReal (nx h).toReal = nx h := ENNReal.ofReal_toReal hfinite
      have ht : (nx h).toReal < eps / ((C : ℝ) + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff hepsδ).mp (by rwa [htoReal])
      have hproduct : (C : ℝ) * (nx h).toReal ≤ eps := by
        have hlt := (lt_div_iff₀ (by positivity : 0 < (C : ℝ) + 1)).mp ht
        nlinarith [ENNReal.toReal_nonneg (a := nx h)]
      have hfactor : (C : ℝ≥0∞) * nx h ≤ ENNReal.ofReal eps := by
        rw [← htoReal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
        exact ENNReal.ofReal_le_ofReal hproduct
      calc
        nx (F (0 + h) - F 0 - -h) = nx (F h + h) := by simp only [zero_add, hF0, sub_zero, sub_neg_eq_add]
        _ ≤ (C : ℝ≥0∞) * (nx h) ^ (2 : ℕ) := hQ h hh hsmall
        _ = ((C : ℝ≥0∞) * nx h) * nx h := by ring
        _ ≤ ENNReal.ofReal eps * nx h := mul_le_mul hfactor le_rfl bot_le bot_le

end K24.Global.SobolevFrechet

/- Checked source: K24SOBFRECHET_Inverse.lean. -/

set_option autoImplicit false
open scoped ENNReal NNReal

namespace K24.Global.SobolevFrechet
open SobolevNeumann SobolevMatrix

/-- The actual scalar inverse-difference map has the canonical Frechet
 derivative minus the identity at zero, in every original real-order H^r
 norm above the dimension-four algebra threshold. -/
theorem local_inverse_hasSectionFrechetDerivative (r : ℝ) (hr : 2 < r) :
    ∃ δ : ℝ, 0 < δ ∧
      SectionNeighborhood (continuousLocalSpace r)
        {u | u ∈ continuousLocalSpace r ∧ localSobolevENN r u < ENNReal.ofReal δ}
        (localSobolevENN r) 0 ∧
      HasSectionFrechetDerivative (continuousLocalSpace r)
        {u | u ∈ continuousLocalSpace r ∧ localSobolevENN r u < ENNReal.ofReal δ}
        (continuousLocalSpace r) (localSobolevENN r) (localSobolevENN r)
        inverseDifference (fun h => -h) 0 := by
  obtain ⟨δ, hδ, C, hInv⟩ := local_inverse_quadratic r hr
  refine ⟨δ, hδ, hasSectionFrechetDerivative_neg_of_quadratic
    (continuousLocalSpace r) (localSobolevENN r)
    (continuousLocal_sectionBanachSpace r hr) inverseDifference ?_ δ hδ C ?_ ?_⟩
  · funext x
    simp [inverseDifference]
  · intro u hu hsmall
    obtain ⟨_, hc, hm, _, _, _, _⟩ := hInv u hu.1 hu.2 hsmall
    exact ⟨hc, hm⟩
  · intro u hu hsmall
    obtain ⟨_, _, _, _, _, _, hq⟩ := hInv u hu.1 hu.2 hsmall
    exact hq

/-- The actual matrix inverse-difference map has the canonical Frechet
 derivative minus the identity at zero, in the original matrix Bessel norm.
 All sixteen entry conditions and the real order remain unchanged. -/
theorem local_matrix_inverse_hasSectionFrechetDerivative (r : ℝ) (hr : 2 < r) :
    ∃ δ : ℝ, 0 < δ ∧
      SectionNeighborhood (continuousMatrixSobolevSpace r)
        {u | u ∈ continuousMatrixSobolevSpace r ∧ matrixSobolevENN r u < ENNReal.ofReal δ}
        (matrixSobolevENN r) 0 ∧
      HasSectionFrechetDerivative (continuousMatrixSobolevSpace r)
        {u | u ∈ continuousMatrixSobolevSpace r ∧ matrixSobolevENN r u < ENNReal.ofReal δ}
        (continuousMatrixSobolevSpace r) (matrixSobolevENN r) (matrixSobolevENN r)
        matrixInverseDifference (fun h => -h) 0 := by
  obtain ⟨δ, hδ, C, hInv⟩ := local_matrix_inverse_quadratic r hr
  refine ⟨δ, hδ, hasSectionFrechetDerivative_neg_of_quadratic
    (continuousMatrixSobolevSpace r) (matrixSobolevENN r)
    (continuousMatrix_sectionBanachSpace r hr) matrixInverseDifference ?_ δ hδ C ?_ ?_⟩
  · funext x
    simp [matrixInverseDifference]
  · intro u hu hsmall
    obtain ⟨_, _, hm, _, _, _, _⟩ := hInv u hu hsmall
    exact hm
  · intro u hu hsmall
    obtain ⟨_, _, _, _, _, _, hq⟩ := hInv u hu hsmall
    exact hq

end K24.Global.SobolevFrechet

theorem solution :
  (∀ (r : ℝ), 2 < r →
    let S : Set (K24.Global.SobolevModel → ℝ) :=
      {u | Continuous u ∧ K24.Global.LocalSobolevMem r u}
    ∃ δ : ℝ, 0 < δ ∧
      K24.Global.SectionNeighborhood S
        {u | u ∈ S ∧ K24.Global.localSobolevENN r u < ENNReal.ofReal δ}
        (K24.Global.localSobolevENN r) 0 ∧
      K24.Global.HasSectionFrechetDerivative S
        {u | u ∈ S ∧ K24.Global.localSobolevENN r u < ENNReal.ofReal δ} S
        (K24.Global.localSobolevENN r) (K24.Global.localSobolevENN r)
        (fun u x => (1 + u x)⁻¹ - 1) (fun h => -h) 0) ∧
  (∀ (r : ℝ), 2 < r →
    let S : Set (K24.Global.FourSpace → K24.Global.Mat4) :=
      {u | ∀ i j, Continuous (fun x => u x i j) ∧
        K24.Global.LocalSobolevMem r (fun x => u x i j)}
    ∃ δ : ℝ, 0 < δ ∧
      K24.Global.SectionNeighborhood S
        {u | u ∈ S ∧ K24.Global.matrixSobolevENN r u < ENNReal.ofReal δ}
        (K24.Global.matrixSobolevENN r) 0 ∧
      K24.Global.HasSectionFrechetDerivative S
        {u | u ∈ S ∧ K24.Global.matrixSobolevENN r u < ENNReal.ofReal δ} S
        (K24.Global.matrixSobolevENN r) (K24.Global.matrixSobolevENN r)
        (fun u x => (1 + u x)⁻¹ - 1) (fun h => -h) 0) := ⟨K24.Global.SobolevFrechet.local_inverse_hasSectionFrechetDerivative,
  K24.Global.SobolevFrechet.local_matrix_inverse_hasSectionFrechetDerivative⟩

#check (solution :
  (∀ (r : ℝ), 2 < r →
    let S : Set (K24.Global.SobolevModel → ℝ) :=
      {u | Continuous u ∧ K24.Global.LocalSobolevMem r u}
    ∃ δ : ℝ, 0 < δ ∧
      K24.Global.SectionNeighborhood S
        {u | u ∈ S ∧ K24.Global.localSobolevENN r u < ENNReal.ofReal δ}
        (K24.Global.localSobolevENN r) 0 ∧
      K24.Global.HasSectionFrechetDerivative S
        {u | u ∈ S ∧ K24.Global.localSobolevENN r u < ENNReal.ofReal δ} S
        (K24.Global.localSobolevENN r) (K24.Global.localSobolevENN r)
        (fun u x => (1 + u x)⁻¹ - 1) (fun h => -h) 0) ∧
  (∀ (r : ℝ), 2 < r →
    let S : Set (K24.Global.FourSpace → K24.Global.Mat4) :=
      {u | ∀ i j, Continuous (fun x => u x i j) ∧
        K24.Global.LocalSobolevMem r (fun x => u x i j)}
    ∃ δ : ℝ, 0 < δ ∧
      K24.Global.SectionNeighborhood S
        {u | u ∈ S ∧ K24.Global.matrixSobolevENN r u < ENNReal.ofReal δ}
        (K24.Global.matrixSobolevENN r) 0 ∧
      K24.Global.HasSectionFrechetDerivative S
        {u | u ∈ S ∧ K24.Global.matrixSobolevENN r u < ENNReal.ofReal δ} S
        (K24.Global.matrixSobolevENN r) (K24.Global.matrixSobolevENN r)
        (fun u x => (1 + u x)⁻¹ - 1) (fun h => -h) 0))
#print axioms solution
