-- Prove2me | solution 1 for K24.Global.tensorSobolev_banach
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T20:49:25.16118+00:00
-- url     : https://prove2.me/submissions/c40e328e-74cb-4b66-96e3-6b1b9dacbcfb

import Definitions.Def_K24GlobalStatement
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Lp.lpSpace

/- Inlined checked Reused; exact source/excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff BoundedContinuousFunction

/- Checked inverse Bessel weight integrability reused verbatim; see PROVENANCE.json. -/
namespace K24.Global
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

end K24.Global

/- Inlined FourierDistribution; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology BoundedContinuousFunction

namespace K24.Global

def boundedFunctionDistribution (f : SobolevModel →ᵇ ℂ) : LocalDistribution :=
  ((f.memLp_top (μ := volume)).toLp (f : SobolevModel → ℂ) : LocalDistribution)

theorem boundedFunctionDistribution_apply (f : SobolevModel →ᵇ ℂ)
    (ψ : SchwartzMap SobolevModel ℂ) :
    boundedFunctionDistribution f ψ = ∫ x, ψ x • f x := by
  rw [boundedFunctionDistribution, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(f.memLp_top (μ := volume)).coeFn_toLp] with x hx
  rw [hx]

theorem inverseFourier_L1_distribution (v : Lp ℂ 1 (volume : Measure SobolevModel)) :
    boundedFunctionDistribution (Real.Lp.fourierTransformInv v) = 𝓕⁻ (v : LocalDistribution) := by
  ext ψ
  rw [boundedFunctionDistribution_apply, TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (L := -innerₗ SobolevModel) Real.continuous_fourierChar
    (by
      change Continuous (fun p : SobolevModel × SobolevModel => -inner ℝ p.1 p.2)
      fun_prop) ψ.integrable (L1.integrable_coeFn v)
  symm
  convert h using 1
  · congr 1; ext x
    simp only [SchwartzMap.fourierInv_coe]
    rfl
  · congr 1; ext x
    congr 1
    rw [Real.Lp.fourierTransformInv_apply]
    change VectorFourier.fourierIntegral Real.fourierChar volume
      (-innerₗ SobolevModel) (v : SobolevModel → ℂ) x =
      VectorFourier.fourierIntegral Real.fourierChar volume
      (-innerₗ SobolevModel).flip (v : SobolevModel → ℂ) x
    congr 2
    ext a b
    simp only [LinearMap.flip_apply, LinearMap.neg_apply, innerₗ_apply_apply]
    rw [real_inner_comm]

theorem boundedFunctionDistribution_eq_L2_ae
    (g : SobolevModel →ᵇ ℂ) (f : SobolevModel → ℂ) (hf : MemLp f 2 volume)
    (heq : boundedFunctionDistribution g = (hf.toLp f : LocalDistribution)) :
    (g : SobolevModel → ℂ) =ᵐ[volume] f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    g.continuous.locallyIntegrable (hf.locallyIntegrable (by norm_num))
  intro ψ hψ hcψ
  let φ : SchwartzMap SobolevModel ℂ :=
    (hcψ.comp_left (show Complex.ofRealCLM 0 = 0 by rfl)).toSchwartzMap (by fun_prop)
  have hh := congrArg (fun T : LocalDistribution => T φ) heq
  rw [boundedFunctionDistribution_apply, Lp.toTemperedDistribution_apply] at hh
  have hr : (∫ x, φ x • hf.toLp f x) = ∫ x, φ x • f x := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  rw [hr] at hh
  change (∫ x, (ψ x : ℂ) • g x) = ∫ x, (ψ x : ℂ) • f x at hh
  simpa only [Complex.real_smul, smul_eq_mul] using hh

end K24.Global

/- Inlined FourierMoments; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
noncomputable section
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff

namespace K24.Global

theorem norm_pow_mul_bessel_weight_le (k j : ℕ) (hj : j ≤ k) (r : ℝ) (x : SobolevModel) :
    ‖x‖ ^ j * (1 + ‖x‖ ^ 2) ^ (-r / 2) ≤
      (1 + ‖x‖ ^ 2) ^ (-(r - k) / 2) := by
  have hpow : ‖x‖ ^ j ≤ (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) := by
    calc
      ‖x‖ ^ j ≤ (Real.sqrt (1 + ‖x‖ ^ 2)) ^ j :=
        pow_le_pow_left₀ (norm_nonneg x) (Real.le_sqrt_of_sq_le (by nlinarith)) j
      _ = (1 + ‖x‖ ^ 2) ^ ((j : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖x‖]) (by exact_mod_cast (div_le_div_of_nonneg_right (show (j : ℝ) ≤ k by exact_mod_cast hj) (by norm_num : (0 : ℝ) ≤ 2)))
  calc
    _ ≤ (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) * (1 + ‖x‖ ^ 2) ^ (-r / 2) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

theorem bessel_fourier_moments (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r) :
    ∃ B : ℝ≥0, ∀ (T : LocalDistribution) (hT : BesselMem r T),
      ∃ v : Lp ℂ 1 (volume : Measure SobolevModel),
        𝓕 T = (v : LocalDistribution) ∧ ∀ j ≤ k,
          Integrable (fun x : SobolevModel => ‖x‖ ^ j * ‖v x‖) volume ∧
          (∫ x : SobolevModel, ‖x‖ ^ j * ‖v x‖) ≤ (B : ℝ) * ‖besselRepresentative hT‖ := by
  have hr0 : 2 < r := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hrk : 2 < r - k := by linarith
  let w : SobolevModel → ℂ := fun x => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-r / 2))
  let wK : SobolevModel → ℂ := fun x => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-(r - k) / 2))
  have hw : MemLp w 2 volume := (bessel_inverse_weight_memL2 hr0).ofReal
  have hwK : MemLp wK 2 volume := (bessel_inverse_weight_memL2 hrk).ofReal
  let W : LocalL2 := hwK.toLp wK
  refine ⟨‖W‖₊, fun T hT => ?_⟩
  let u : LocalL2 := 𝓕 (besselRepresentative hT)
  have hu : smulLeftCLM ℂ (fun x : SobolevModel => ((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ))
      (𝓕 T) = (u : LocalDistribution) := by
    rw [← fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      besselRepresentative_spec hT, Lp.fourier_toTemperedDistribution_eq]
  let v : Lp ℂ 1 (volume : Measure SobolevModel) := hw.toLp w • u
  let V : Lp ℂ 1 (volume : Measure SobolevModel) := W • u
  refine ⟨v, ?_, fun j hj => ?_⟩
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
  · have hle : ∀ᵐ x : SobolevModel ∂volume, ‖x‖ ^ j * ‖v x‖ ≤ ‖V x‖ := by
      filter_upwards [Lp.coeFn_lpSMul (r := 1) (hw.toLp w) u,
        Lp.coeFn_lpSMul (r := 1) W u, hw.coeFn_toLp, hwK.coeFn_toLp] with x hvx hVx hwx hWx
      change ‖x‖ ^ j * ‖(hw.toLp w • u : Lp ℂ 1 volume) x‖ ≤ ‖(W • u : Lp ℂ 1 volume) x‖
      rw [hvx, hVx]
      change ‖x‖ ^ j * ‖hw.toLp w x • u x‖ ≤ ‖hwK.toLp wK x • u x‖
      rw [hwx, hWx, norm_smul, norm_smul]
      simp only [w, wK, Complex.norm_real, Real.norm_eq_abs]
      have ha : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-r / 2) := by positivity
      have hb : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-(r - k) / 2) := by positivity
      rw [abs_of_nonneg ha, abs_of_nonneg hb, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (norm_pow_mul_bessel_weight_le k j hj r x) (norm_nonneg _)
    have hm : AEStronglyMeasurable (fun x : SobolevModel => ‖x‖ ^ j * ‖v x‖) volume :=
      (continuous_norm.pow j).aestronglyMeasurable.mul (Lp.aestronglyMeasurable v).norm
    have hi : Integrable (fun x : SobolevModel => ‖x‖ ^ j * ‖v x‖) volume :=
      (L1.integrable_coeFn V).norm.mono' hm (hle.mono fun x hx => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) j) (norm_nonneg (v x)))] using hx)
    refine ⟨hi, ?_⟩
    calc
      _ ≤ ∫ x : SobolevModel, ‖V x‖ := integral_mono_ae hi (L1.integrable_coeFn V).norm hle
      _ = ‖V‖ := (L1.norm_eq_integral_norm V).symm
      _ ≤ ‖W‖ * ‖u‖ := Lp.norm_smul_le W u
      _ = _ := by simp only [u, Lp.norm_fourier_eq, coe_nnnorm]

end K24.Global

/- Inlined InverseDerivatives; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
noncomputable section
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff BoundedContinuousFunction Real

namespace K24.Global

def inverseFourierBilinear : SobolevModel →L[ℝ] SobolevModel →L[ℝ] ℝ :=
  -(innerSL ℝ)

theorem inverseFourier_L1_eq_integral (v : Lp ℂ 1 (volume : Measure SobolevModel)) :
    (Real.Lp.fourierTransformInv v : SobolevModel → ℂ) =
      VectorFourier.fourierIntegral Real.fourierChar volume inverseFourierBilinear.toLinearMap₁₂
        (v : SobolevModel → ℂ) := by
  ext x
  rw [Real.Lp.fourierTransformInv_apply]
  rfl

theorem inverseFourier_moment_derivative_bounds
    (k : ℕ) (v : Lp ℂ 1 (volume : Measure SobolevModel)) (B : ℝ)
    (hm : ∀ j ≤ k, Integrable (fun x : SobolevModel => ‖x‖ ^ j * ‖v x‖) volume ∧
      (∫ x : SobolevModel, ‖x‖ ^ j * ‖v x‖) ≤ B) :
    ContDiff ℝ k (Real.Lp.fourierTransformInv v : SobolevModel → ℂ) ∧
    ∀ j ≤ k, ∀ x : SobolevModel,
      ‖iteratedFDeriv ℝ j (Real.Lp.fourierTransformInv v : SobolevModel → ℂ) x‖ ≤
        (2 * Real.pi * ‖inverseFourierBilinear‖) ^ j * B := by
  have hm' : ∀ j : ℕ, (j : ℕ∞) ≤ k →
      Integrable (fun x : SobolevModel => ‖x‖ ^ j * ‖v x‖) volume := by
    intro j hj
    exact (hm j (by exact_mod_cast hj)).1
  rw [inverseFourier_L1_eq_integral]
  refine ⟨?_, fun j hj x => ?_⟩
  · exact VectorFourier.contDiff_fourierIntegral inverseFourierBilinear hm'
  · rw [VectorFourier.iteratedFDeriv_fourierIntegral inverseFourierBilinear hm'
      (Lp.aestronglyMeasurable v) (by exact_mod_cast hj)]
    calc
      _ ≤ ∫ ξ : SobolevModel,
          ‖VectorFourier.fourierPowSMulRight inverseFourierBilinear (v : SobolevModel → ℂ) ξ j‖ :=
        VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
          inverseFourierBilinear.toLinearMap₁₂ _ x
      _ ≤ ∫ ξ : SobolevModel, (2 * Real.pi * ‖inverseFourierBilinear‖) ^ j * (‖ξ‖ ^ j * ‖v ξ‖) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((hm j hj).1.const_mul _)
        filter_upwards with ξ
        exact (VectorFourier.norm_fourierPowSMulRight_le inverseFourierBilinear
          (v : SobolevModel → ℂ) ξ j).trans_eq (by ring)
      _ = (2 * Real.pi * ‖inverseFourierBilinear‖) ^ j *
          ∫ ξ : SobolevModel, ‖ξ‖ ^ j * ‖v ξ‖ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hm j hj).2 (by positivity)

theorem bessel_classical_complex_representative
    (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r) :
    ∃ A : ℝ≥0, ∀ (T : LocalDistribution) (hT : BesselMem r T),
      ∃ G : SobolevModel →ᵇ ℂ,
        boundedFunctionDistribution G = T ∧ ContDiff ℝ k (G : SobolevModel → ℂ) ∧
        ∀ j ≤ k, ∀ x : SobolevModel,
          ‖iteratedFDeriv ℝ j (G : SobolevModel → ℂ) x‖ ≤
            (A : ℝ) * ‖besselRepresentative hT‖ := by
  obtain ⟨B, hB⟩ := bessel_fourier_moments k r hr
  let a : ℕ → ℝ := fun j => (2 * Real.pi * ‖inverseFourierBilinear‖) ^ j
  let A : ℝ := (∑ j ∈ Finset.range (k + 1), a j) * B
  have hA : 0 ≤ A := by dsimp [A, a]; positivity
  refine ⟨⟨A, hA⟩, fun T hT => ?_⟩
  obtain ⟨v, hv, hm⟩ := hB T hT
  have hG := inverseFourier_moment_derivative_bounds k v ((B : ℝ) * ‖besselRepresentative hT‖) hm
  refine ⟨Real.Lp.fourierTransformInv v, ?_, hG.1, fun j hj x => ?_⟩
  · rw [inverseFourier_L1_distribution, ← hv, fourierInv_fourier_eq]
  · have ha : a j ≤ ∑ l ∈ Finset.range (k + 1), a l :=
      Finset.single_le_sum (s := Finset.range (k + 1)) (f := a) (a := j)
        (fun _ _ => by dsimp [a]; positivity) (Finset.mem_range.mpr (by omega))
    calc
      _ ≤ a j * ((B : ℝ) * ‖besselRepresentative hT‖) := hG.2 j hj x
      _ ≤ (∑ l ∈ Finset.range (k + 1), a l) * ((B : ℝ) * ‖besselRepresentative hT‖) :=
        mul_le_mul_of_nonneg_right ha (by positivity)
      _ = _ := by
        change _ = A * ‖besselRepresentative hT‖
        dsimp [A]
        ring

end K24.Global

/- Inlined RealRepresentative; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
noncomputable section
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff BoundedContinuousFunction

namespace K24.Global

theorem classical_sobolev_representative_proof :
    ∀ (k : ℕ) (r : ℝ), (k : ℝ) + 2 < r → ∃ A : ℝ≥0,
      ∀ f : SobolevModel → ℝ, LocalSobolevMem r f →
      ∃ g : SobolevModel → ℝ,
        ContDiff ℝ k g ∧ f =ᵐ[volume] g ∧ LocalSobolevMem r g ∧
        localSobolevENN r g = localSobolevENN r f ∧
        (∀ (hf : MemLp (complexifyLocal f) 2 volume)
           (hg : MemLp (complexifyLocal g) 2 volume),
          localFunctionDistribution f hf = localFunctionDistribution g hg) ∧
        ∀ j ≤ k, ∀ x : SobolevModel,
          ENNReal.ofReal ‖iteratedFDeriv ℝ j g x‖ ≤ (A : ℝ≥0∞) * localSobolevENN r f := by
  intro k r hr
  obtain ⟨A, hA⟩ := bessel_classical_complex_representative k r hr
  refine ⟨A, fun f ⟨hf, hB⟩ => ?_⟩
  obtain ⟨G, hGD, hGC, hGb⟩ := hA (localFunctionDistribution f hf) hB
  let g : SobolevModel → ℝ := fun x => (G x).re
  have hgC : ContDiff ℝ k g := Complex.reCLM.contDiff.comp hGC
  have hGae : (G : SobolevModel → ℂ) =ᵐ[volume] complexifyLocal f :=
    boundedFunctionDistribution_eq_L2_ae G _ hf hGD
  have hfg : f =ᵐ[volume] g := by
    filter_upwards [hGae] with x hx
    have hrx := congrArg Complex.re hx
    simpa only [complexifyLocal, Complex.ofReal_re, g] using hrx.symm
  have hfgC : complexifyLocal f =ᵐ[volume] complexifyLocal g := by
    filter_upwards [hfg] with x hx
    simp only [complexifyLocal, hx]
  have hg : MemLp (complexifyLocal g) 2 volume := (memLp_congr_ae hfgC).mp hf
  have hd : ∀ (hf' : MemLp (complexifyLocal f) 2 volume)
      (hg' : MemLp (complexifyLocal g) 2 volume),
      localFunctionDistribution f hf' = localFunctionDistribution g hg' := by
    intro hf' hg'
    exact congrArg (fun v : LocalL2 => (v : LocalDistribution)) (MemLp.toLp_congr hf' hg' hfgC)
  have hgB : BesselMem r (localFunctionDistribution g hg) := by
    rw [← hd hf hg]
    exact hB
  refine ⟨g, hgC, hfg, ⟨hg, hgB⟩, ?_, hd, fun j hj x => ?_⟩
  · simp only [localSobolevENN, dif_pos hf, dif_pos hg, hd hf hg]
  · have hn : ‖iteratedFDeriv ℝ j g x‖ ≤ ‖iteratedFDeriv ℝ j (G : SobolevModel → ℂ) x‖ := by
      have hh := Complex.reCLM.norm_iteratedFDeriv_comp_left (x := x) hGC.contDiffAt
        (show (j : ℕ∞ω) ≤ k by exact_mod_cast hj)
      simpa only [Complex.reCLM_norm, one_mul, g, Function.comp_def, Complex.reCLM_apply] using hh
    have hb := hn.trans (hGb j hj x)
    simp only [localSobolevENN, dif_pos hf, besselSobolevENN_of_mem hB]
    calc
      _ ≤ ENNReal.ofReal ((A : ℝ) * ‖besselRepresentative hB‖) := ENNReal.ofReal_le_ofReal hb
      _ = _ := by rw [ENNReal.ofReal_mul A.coe_nonneg, ENNReal.ofReal_coe_nnreal]

theorem continuous_localSobolev_classical_bound
    (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r) :
    ∃ A : ℝ≥0, ∀ f : SobolevModel → ℝ, Continuous f → LocalSobolevMem r f →
      ContDiff ℝ k f ∧ ∀ j ≤ k, ∀ x : SobolevModel,
        ENNReal.ofReal ‖iteratedFDeriv ℝ j f x‖ ≤ (A : ℝ≥0∞) * localSobolevENN r f := by
  obtain ⟨A, hA⟩ := classical_sobolev_representative_proof k r hr
  refine ⟨A, fun f hfc hfm => ?_⟩
  obtain ⟨g, hgc, hae, _, _, _, hb⟩ := hA f hfm
  have hfg : f = g := (hfc.ae_eq_iff_eq volume hgc.continuous).mp hae
  subst g
  exact ⟨hgc, hb⟩

end K24.Global

namespace K24.Global
theorem besselRepresentative_add {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselRepresentative (hT.add hU) = besselRepresentative hT + besselRepresentative hU := by
  apply besselRepresentative_unique
  rw [map_add, besselRepresentative_spec hT, besselRepresentative_spec hU]
  simp only [← Lp.toTemperedDistributionCLM_apply, map_add]

theorem besselRepresentative_sub {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselRepresentative (hT.sub hU) = besselRepresentative hT - besselRepresentative hU := by
  apply besselRepresentative_unique
  rw [map_sub, besselRepresentative_spec hT, besselRepresentative_spec hU]
  simp only [← Lp.toTemperedDistributionCLM_apply, map_sub]

theorem besselMem_real_smul {s : ℝ} {T : LocalDistribution} (hT : BesselMem s T) (c : ℝ) :
    BesselMem s (c • T) := by
  exact ⟨c • besselRepresentative hT, by
    rw [ContinuousLinearMap.map_smul_of_tower, besselRepresentative_spec hT]
    simp only [← Lp.toTemperedDistributionCLM_apply, ContinuousLinearMap.map_smul_of_tower]⟩

theorem besselRepresentative_real_smul {s : ℝ} {T : LocalDistribution}
    (hT : BesselMem s T) (c : ℝ) :
    besselRepresentative (besselMem_real_smul hT c) = c • besselRepresentative hT := by
  apply besselRepresentative_unique
  rw [ContinuousLinearMap.map_smul_of_tower, besselRepresentative_spec hT]
  simp only [← Lp.toTemperedDistributionCLM_apply, ContinuousLinearMap.map_smul_of_tower]

theorem besselSobolevENN_sub_eq {s : ℝ} {T U : LocalDistribution}
    (hT : BesselMem s T) (hU : BesselMem s U) :
    besselSobolevENN s (T - U) =
      ENNReal.ofReal ‖besselRepresentative hT - besselRepresentative hU‖ := by
  rw [besselSobolevENN_of_mem (hT.sub hU), besselRepresentative_sub]

theorem besselSobolev_complete (s : ℝ) (f : ℕ → LocalDistribution)
    (hf : ∀ n, BesselMem s (f n))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      besselSobolevENN s (f i - f j) < ENNReal.ofReal eps) :
    ∃ T, BesselMem s T ∧ ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      besselSobolevENN s (f i - T) < ENNReal.ofReal eps := by
  have hC : CauchySeq (fun n => besselRepresentative (hf n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := hc eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
    simpa only [dist_eq_norm, besselSobolevENN_sub_eq (hf i) (hf j)] using hN i hi j hj
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hC
  let T : LocalDistribution := besselPotential SobolevModel ℂ (-s) (v : LocalDistribution)
  have hTrep : besselPotential SobolevModel ℂ s T = (v : LocalDistribution) := by
    simp [T]
  have hT : BesselMem s T := ⟨v, hTrep⟩
  refine ⟨T, hT, fun eps heps => ?_⟩
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hv) eps heps
  refine ⟨N, fun i hi => ?_⟩
  rw [besselSobolevENN_sub_eq (hf i) hT, besselRepresentative_unique hT v hTrep]
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mpr
  simpa only [dist_eq_norm] using hN i hi

theorem besselSobolev_banach_proof (s : ℝ) :
    SectionBanachSpace {T : LocalDistribution | BesselMem s T} (besselSobolevENN s) where
  zero_mem := memSobolev_fun_zero SobolevModel ℂ s 2
  add_mem T hT U hU := hT.add hU
  smul_mem c T hT := besselMem_real_smul hT c
  finite T hT := (besselSobolevENN_lt_top_iff s T).mpr hT
  zero_norm := besselSobolevENN_zero s
  definite T hT hn := by
    have hz : besselRepresentative hT = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa only [besselSobolevENN_of_mem hT, ENNReal.ofReal_eq_zero] using hn
    have hd := besselRepresentative_spec hT
    rw [hz] at hd
    have hback := congrArg (besselPotential SobolevModel ℂ (-s)) hd
    simpa only [besselPotential_besselPotential_apply, add_neg_cancel, besselPotential_zero,
      ContinuousLinearMap.id_apply, ← Lp.toTemperedDistributionCLM_apply, map_zero] using hback
  triangle T hT U hU := by
    rw [besselSobolevENN_of_mem (hT.add hU), besselRepresentative_add hT hU,
      besselSobolevENN_of_mem hT, besselSobolevENN_of_mem hU,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  homogeneous c T hT := by
    rw [besselSobolevENN_of_mem (besselMem_real_smul hT c), besselRepresentative_real_smul,
      norm_smul, Real.norm_eq_abs, ENNReal.ofReal_mul (abs_nonneg c), besselSobolevENN_of_mem hT]
  complete := besselSobolev_complete s

theorem complexifyLocal_sub (f g : SobolevModel → ℝ) :
    complexifyLocal (f - g) = complexifyLocal f - complexifyLocal g := by
  ext x; simp [complexifyLocal]

theorem localFunctionDistribution_sub (f g : SobolevModel → ℝ)
    (hf : MemLp (complexifyLocal f) 2 volume) (hg : MemLp (complexifyLocal g) 2 volume)
    (hfg : MemLp (complexifyLocal (f - g)) 2 volume) :
    localFunctionDistribution (f - g) hfg = localFunctionDistribution f hf - localFunctionDistribution g hg := by
  have heq : complexifyLocal (f - g) = complexifyLocal f - complexifyLocal g := by
    ext x; simp [complexifyLocal]
  unfold localFunctionDistribution
  simp only [← Lp.toTemperedDistributionCLM_apply, ← map_sub]
  congr 1
  apply Lp.ext
  filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
    Lp.coeFn_sub (hf.toLp (complexifyLocal f)) (hg.toLp (complexifyLocal g))] with x hfgx hfx hgx hsub
  rw [hfgx, hsub, Pi.sub_apply, hfx, hgx]
  exact congrFun heq x

theorem localSobolev_Cauchy_distribution_limit (s : ℝ) (f : ℕ → SobolevModel → ℝ)
    (hf : ∀ n, LocalSobolevMem s (f n))
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      localSobolevENN s (f i - f j) < ENNReal.ofReal eps) :
    ∃ (hL2 : ∀ n, MemLp (complexifyLocal (f n)) 2 volume) (T : LocalDistribution),
      BesselMem s T ∧ ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
        besselSobolevENN s (localFunctionDistribution (f i) (hL2 i) - T) < ENNReal.ofReal eps := by
  classical
  choose hL2 hB using hf
  refine ⟨hL2, ?_⟩
  apply besselSobolev_complete s _ hB
  intro eps heps
  obtain ⟨N, hN⟩ := hc eps heps
  refine ⟨N, fun i hi j hj => ?_⟩
  have hsub : MemLp (complexifyLocal (f i - f j)) 2 volume := by
    rw [complexifyLocal_sub]
    exact (hL2 i).sub (hL2 j)
  rw [← localFunctionDistribution_sub _ _ (hL2 i) (hL2 j) hsub]
  simpa only [localSobolevENN, dif_pos hsub] using hN i hi j hj


end K24.Global

/- Inlined checked ClassicalMap; exact source/excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory TemperedDistribution Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff BoundedContinuousFunction
namespace K24.Global

theorem boundedFunctionDistribution_injective : Function.Injective boundedFunctionDistribution := by
  intro f g h
  apply DFunLike.coe_injective
  apply (f.continuous.ae_eq_iff_eq volume g.continuous).mp
  apply ae_eq_of_integral_contDiff_smul_eq f.continuous.locallyIntegrable g.continuous.locallyIntegrable
  intro ψ hψ hcψ
  let φ : SchwartzMap SobolevModel ℂ :=
    (hcψ.comp_left (show Complex.ofRealCLM 0 = 0 by rfl)).toSchwartzMap (by fun_prop)
  have hh := congrArg (fun T : LocalDistribution => T φ) h
  rw [boundedFunctionDistribution_apply, boundedFunctionDistribution_apply] at hh
  change (∫ x, (ψ x : ℂ) • f x) = ∫ x, (ψ x : ℂ) • g x at hh
  simpa only [Complex.real_smul, smul_eq_mul] using hh

theorem boundedFunctionDistribution_add (f g : SobolevModel →ᵇ ℂ) :
    boundedFunctionDistribution (f + g) = boundedFunctionDistribution f + boundedFunctionDistribution g := by
  unfold boundedFunctionDistribution
  rw [← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply,
    ← Lp.toTemperedDistributionCLM_apply, ← map_add]
  congr 1


theorem boundedFunctionDistribution_real_smul (a : ℝ) (f : SobolevModel →ᵇ ℂ) :
    boundedFunctionDistribution (a • f) = a • boundedFunctionDistribution f := by
  unfold boundedFunctionDistribution
  rw [← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply,
    ← ContinuousLinearMap.map_smul_of_tower]
  congr 1

theorem boundedFunctionDistribution_eq_of_memLp (f : SobolevModel →ᵇ ℂ)
    (hf : MemLp (f : SobolevModel → ℂ) 2 volume) :
    boundedFunctionDistribution f = (hf.toLp f : LocalDistribution) := by
  ext ψ
  rw [boundedFunctionDistribution_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

def inverseBesselDistribution (r : ℝ) : LocalL2 →L[ℝ] LocalDistribution :=
  ((besselPotential SobolevModel ℂ (-r)).comp
    (Lp.toTemperedDistributionCLM ℂ volume 2)).restrictScalars ℝ

theorem inverseBesselDistribution_mem (r : ℝ) (v : LocalL2) :
    BesselMem r (inverseBesselDistribution r v) := by
  refine ⟨v, ?_⟩
  simp [inverseBesselDistribution]

theorem inverseBesselDistribution_rep (r : ℝ) (v : LocalL2) :
    besselRepresentative (inverseBesselDistribution_mem r v) = v := by
  apply besselRepresentative_unique
  simp [inverseBesselDistribution]

theorem inverseBesselDistribution_rep_apply {r : ℝ} {T : LocalDistribution} (hT : BesselMem r T) :
    inverseBesselDistribution r (besselRepresentative hT) = T := by
  change besselPotential SobolevModel ℂ (-r) (besselRepresentative hT : LocalDistribution) = T
  have hh := congrArg (besselPotential SobolevModel ℂ (-r)) (besselRepresentative_spec hT)
  simpa only [besselPotential_besselPotential_apply, add_neg_cancel, besselPotential_zero,
    ContinuousLinearMap.id_apply, inverseBesselDistribution, ContinuousLinearMap.coe_restrictScalars,
    ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply] using hh.symm

/-- The canonical continuous representative of the inverse Bessel transform. -/
def besselClassicalMap (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r) :
    LocalL2 →L[ℝ] (SobolevModel →ᵇ ℂ) := by
  classical
  let A := (bessel_classical_complex_representative k r hr).choose
  have hA := (bessel_classical_complex_representative k r hr).choose_spec
  let G := fun v : LocalL2 => (hA (inverseBesselDistribution r v) (inverseBesselDistribution_mem r v)).choose
  have hGD := fun v : LocalL2 => (hA (inverseBesselDistribution r v) (inverseBesselDistribution_mem r v)).choose_spec.1
  have hGb := fun v : LocalL2 => (hA (inverseBesselDistribution r v) (inverseBesselDistribution_mem r v)).choose_spec.2.2
  let L : LocalL2 →ₗ[ℝ] (SobolevModel →ᵇ ℂ) := {
    toFun := G
    map_add' := fun v w => boundedFunctionDistribution_injective (by
      rw [hGD, boundedFunctionDistribution_add, hGD, hGD, map_add])
    map_smul' := fun a v => boundedFunctionDistribution_injective (by
      rw [hGD, boundedFunctionDistribution_real_smul, hGD, map_smul]
      rfl) }
  apply L.mkContinuous A
  intro v
  change ‖G v‖ ≤ (A : ℝ) * ‖v‖
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  have hb := hGb v 0 (Nat.zero_le _) x
  rw [norm_iteratedFDeriv_zero] at hb
  change ‖G v x‖ ≤ (A : ℝ) * ‖besselRepresentative (inverseBesselDistribution_mem r v)‖ at hb
  rw [inverseBesselDistribution_rep] at hb
  exact hb

theorem besselClassicalMap_spec (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r) (v : LocalL2) :
    boundedFunctionDistribution (besselClassicalMap k r hr v) = inverseBesselDistribution r v ∧
      ContDiff ℝ k (besselClassicalMap k r hr v : SobolevModel → ℂ) := by
  classical
  exact ⟨((bessel_classical_complex_representative k r hr).choose_spec _
      (inverseBesselDistribution_mem r v)).choose_spec.1,
    ((bessel_classical_complex_representative k r hr).choose_spec _
      (inverseBesselDistribution_mem r v)).choose_spec.2.1⟩

theorem besselClassicalMap_rep_eq (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r)
    (f : SobolevModel → ℝ) (hc : Continuous f) (hf : LocalSobolevMem r f) :
    (besselClassicalMap k r hr (besselRepresentative hf.choose_spec) : SobolevModel → ℂ) =
      complexifyLocal f := by
  apply ((besselClassicalMap k r hr (besselRepresentative hf.choose_spec)).continuous.ae_eq_iff_eq
    volume (Complex.continuous_ofReal.comp hc)).mp
  apply boundedFunctionDistribution_eq_L2_ae
  rw [(besselClassicalMap_spec k r hr _).1, inverseBesselDistribution_rep_apply hf.choose_spec]
  rfl

theorem localSobolev_compact_limit (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r)
    (K : Set SobolevModel) (hK : IsCompact K)
    (f : ℕ → SobolevModel → ℝ) (hfc : ∀ n, Continuous (f n))
    (hfK : ∀ n, Function.support (f n) ⊆ K) (hf : ∀ n, LocalSobolevMem r (f n))
    (v : LocalL2) (hv : Tendsto (fun n => besselRepresentative (hf n).choose_spec) atTop (𝓝 v)) :
    ∃ g : SobolevModel → ℝ, ContDiff ℝ k g ∧ Function.support g ⊆ K ∧
      ∃ hg : LocalSobolevMem r g,
        besselRepresentative hg.choose_spec = v ∧
        ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  let G := besselClassicalMap k r hr v
  let g : SobolevModel → ℝ := fun x => (G x).re
  have hG : Tendsto (fun n => besselClassicalMap k r hr (besselRepresentative (hf n).choose_spec))
      atTop (𝓝 G) := (besselClassicalMap k r hr).continuous.tendsto v |>.comp hv
  have hpx (x : SobolevModel) : Tendsto (fun n => (f n x : ℂ)) atTop (𝓝 (G x)) := by
    have ht := (((continuous_apply x).comp BoundedContinuousFunction.continuous_coe).tendsto G).comp hG
    change Tendsto (fun n => (besselClassicalMap k r hr (besselRepresentative (hf n).choose_spec)) x) atTop (𝓝 (G x)) at ht
    simpa only [besselClassicalMap_rep_eq k r hr _ (hfc _) (hf _), complexifyLocal] using ht
  have hreal (x : SobolevModel) : (g x : ℂ) = G x := by
    have hi : (G x).im = 0 := by
      have ht := Complex.continuous_im.continuousAt.tendsto.comp (hpx x)
      simp only [Function.comp_def, Complex.ofReal_im] at ht
      exact tendsto_nhds_unique ht tendsto_const_nhds
    exact Complex.ext (by rfl) (by simpa using hi.symm)
  have hgc : ContDiff ℝ k g := Complex.reCLM.contDiff.comp (besselClassicalMap_spec k r hr v).2
  have hfg (x : SobolevModel) : Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using Complex.continuous_re.continuousAt.tendsto.comp (hpx x)
  have hgK : Function.support g ⊆ K := by
    intro x hx
    by_contra hxn
    have hz : ∀ n, f n x = 0 := fun n => Function.notMem_support.mp (mt (fun h => hfK n h) hxn)
    have ht : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (g x)) := by simpa only [hz] using hfg x
    exact hx (tendsto_nhds_unique ht tendsto_const_nhds)
  have hgcompact : HasCompactSupport g := hK.of_isClosed_subset isClosed_closure
    (closure_minimal hgK hK.isClosed)
  have hL2 : MemLp (complexifyLocal g) 2 volume :=
    (Complex.continuous_ofReal.comp hgc.continuous).memLp_of_hasCompactSupport
      (hgcompact.comp_left (by simp [complexifyLocal]))
  have hd : localFunctionDistribution g hL2 = inverseBesselDistribution r v := by
    rw [← (besselClassicalMap_spec k r hr v).1]
    have heq : complexifyLocal g = (G : SobolevModel → ℂ) := funext hreal
    unfold localFunctionDistribution
    have hGL2 : MemLp (G : SobolevModel → ℂ) 2 volume := heq ▸ hL2
    rw [boundedFunctionDistribution_eq_of_memLp G hGL2]
    exact congrArg (fun w : LocalL2 => (w : LocalDistribution))
      (MemLp.toLp_congr hL2 hGL2 (Eventually.of_forall fun x => hreal x))
  have hg : LocalSobolevMem r g := ⟨hL2, hd ▸ inverseBesselDistribution_mem r v⟩
  refine ⟨g, hgc, hgK, hg, ?_, hfg⟩
  apply besselRepresentative_unique
  change besselPotential SobolevModel ℂ r (localFunctionDistribution g hg.choose) = _
  rw [show localFunctionDistribution g hg.choose = localFunctionDistribution g hL2 from rfl, hd]
  simp [inverseBesselDistribution]

end K24.Global

/- Inlined checked LocalAlgebra; exact source/excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory TemperedDistribution Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff BoundedContinuousFunction
namespace K24.Global

def localSobolevRep {r : ℝ} {f : SobolevModel → ℝ} (hf : LocalSobolevMem r f) : LocalL2 :=
  besselRepresentative hf.choose_spec

theorem localSobolevENN_eq_rep {r : ℝ} {f : SobolevModel → ℝ} (hf : LocalSobolevMem r f) :
    localSobolevENN r f = ENNReal.ofReal ‖localSobolevRep hf‖ := by
  simp only [localSobolevENN, dif_pos hf.choose, localSobolevRep, besselSobolevENN_of_mem hf.choose_spec]

theorem localFunctionDistribution_add (f g : SobolevModel → ℝ)
    (hf : MemLp (complexifyLocal f) 2 volume) (hg : MemLp (complexifyLocal g) 2 volume)
    (hfg : MemLp (complexifyLocal (f + g)) 2 volume) :
    localFunctionDistribution (f + g) hfg = localFunctionDistribution f hf + localFunctionDistribution g hg := by
  have heq : complexifyLocal (f + g) = complexifyLocal f + complexifyLocal g := by ext x; simp [complexifyLocal]
  unfold localFunctionDistribution
  rw [← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply,
    ← Lp.toTemperedDistributionCLM_apply, ← map_add]
  congr 1
  apply Lp.ext
  filter_upwards [hfg.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
    Lp.coeFn_add (hf.toLp _) (hg.toLp _)] with x hfgx hfx hgx ha
  rw [hfgx, ha, Pi.add_apply, hfx, hgx]
  exact congrFun heq x

theorem localFunctionDistribution_smul (a : ℝ) (f : SobolevModel → ℝ)
    (hf : MemLp (complexifyLocal f) 2 volume)
    (haf : MemLp (complexifyLocal (a • f)) 2 volume) :
    localFunctionDistribution (a • f) haf = a • localFunctionDistribution f hf := by
  unfold localFunctionDistribution
  rw [← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply,
    ← ContinuousLinearMap.map_smul_of_tower]
  congr 1
  apply Lp.ext
  filter_upwards [haf.coeFn_toLp, hf.coeFn_toLp, Lp.coeFn_smul a (hf.toLp _)] with x hax hx hsm
  rw [hax, hsm, Pi.smul_apply, hx]
  simp [complexifyLocal, Complex.real_smul]

theorem LocalSobolevMem.add {r : ℝ} {f g : SobolevModel → ℝ}
    (hf : LocalSobolevMem r f) (hg : LocalSobolevMem r g) : LocalSobolevMem r (f + g) := by
  have hL2 : MemLp (complexifyLocal (f + g)) 2 volume := by
    convert hf.choose.add hg.choose using 1
    ext x; simp [complexifyLocal]
  refine ⟨hL2, ?_⟩
  rw [localFunctionDistribution_add _ _ hf.choose hg.choose hL2]
  exact hf.choose_spec.add hg.choose_spec

theorem LocalSobolevMem.smul {r : ℝ} {f : SobolevModel → ℝ}
    (hf : LocalSobolevMem r f) (a : ℝ) : LocalSobolevMem r (a • f) := by
  have hL2 : MemLp (complexifyLocal (a • f)) 2 volume := by
    convert hf.choose.const_smul a using 1
    ext x; simp [complexifyLocal, Complex.real_smul]
  refine ⟨hL2, ?_⟩
  rw [localFunctionDistribution_smul _ _ hf.choose hL2]
  exact besselMem_real_smul hf.choose_spec a

theorem LocalSobolevMem.sub {r : ℝ} {f g : SobolevModel → ℝ}
    (hf : LocalSobolevMem r f) (hg : LocalSobolevMem r g) : LocalSobolevMem r (f - g) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using hf.add (hg.smul (-1))

theorem localSobolevRep_add {r : ℝ} {f g : SobolevModel → ℝ}
    (hf : LocalSobolevMem r f) (hg : LocalSobolevMem r g) :
    localSobolevRep (hf.add hg) = localSobolevRep hf + localSobolevRep hg := by
  apply besselRepresentative_unique
  rw [localFunctionDistribution_add _ _ hf.choose hg.choose, map_add,
    besselRepresentative_spec hf.choose_spec, besselRepresentative_spec hg.choose_spec]
  simp only [localSobolevRep, ← Lp.toTemperedDistributionCLM_apply, map_add]

theorem localSobolevRep_smul {r : ℝ} {f : SobolevModel → ℝ}
    (hf : LocalSobolevMem r f) (a : ℝ) :
    localSobolevRep (hf.smul a) = a • localSobolevRep hf := by
  apply besselRepresentative_unique
  rw [localFunctionDistribution_smul _ _ hf.choose, ContinuousLinearMap.map_smul_of_tower,
    besselRepresentative_spec hf.choose_spec]
  simp only [localSobolevRep, ← Lp.toTemperedDistributionCLM_apply, ContinuousLinearMap.map_smul_of_tower]

theorem localSobolevRep_sub {r : ℝ} {f g : SobolevModel → ℝ}
    (hf : LocalSobolevMem r f) (hg : LocalSobolevMem r g) :
    localSobolevRep (hf.sub hg) = localSobolevRep hf - localSobolevRep hg := by
  apply besselRepresentative_unique
  rw [localFunctionDistribution_sub _ _ hf.choose hg.choose, map_sub,
    besselRepresentative_spec hf.choose_spec, besselRepresentative_spec hg.choose_spec]
  simp only [localSobolevRep, ← Lp.toTemperedDistributionCLM_apply, map_sub]

section Square
variable {ι E : Type*} [NormedAddCommGroup E]

def squareENorm (v : ι → E) : ℝ≥0∞ := (∑' i, (ENNReal.ofReal ‖v i‖)^2) ^ (1/2 : ℝ)

theorem squareENorm_finite_iff (v : ι → E) : squareENorm v < ⊤ ↔ Memℓp v 2 := by
  rw [squareENorm, ENNReal.rpow_lt_top_iff_of_pos (by norm_num), memℓp_gen_iff (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  constructor
  · intro h
    have ht := ENNReal.summable_toReal h.ne
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_ofReal (norm_nonneg _)] using ht
  · intro h
    simpa only [ENNReal.ofReal_pow (norm_nonneg _)] using h.tsum_ofReal_lt_top

theorem squareENorm_eq_lp (v : lp (fun _ : ι => E) 2) :
    squareENorm (v : ι → E) = ENNReal.ofReal ‖v‖ := by
  have hs : Summable (fun i => ‖v i‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (lp.memℓp v).summable (by norm_num)
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg fun _ => sq_nonneg _) (by norm_num),
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs]
  simp only [squareENorm, ENNReal.ofReal_pow (norm_nonneg _)]

end Square
end K24.Global

/- Inlined checked ComponentHilbert; exact source/excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
namespace SobolevPartition
variable {C : BoundedLocalCover M} (P : SobolevPartition C) {κ : Type*} [Fintype κ]

@[simp] theorem localize_add (ν : C.Index) (f g : FourSpace → ℝ) :
    P.localize ν (f + g) = P.localize ν f + P.localize ν g := by
  simp only [P.localize_eq_cutoff_mul, mul_add]
@[simp] theorem localize_smul (ν : C.Index) (a : ℝ) (f : FourSpace → ℝ) :
    P.localize ν (a • f) = a • P.localize ν f := by
  ext x
  simp only [P.localize_eq_cutoff_mul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring
@[simp] theorem localize_sub (ν : C.Index) (f g : FourSpace → ℝ) :
    P.localize ν (f - g) = P.localize ν f - P.localize ν g := by
  simp only [P.localize_eq_cutoff_mul, mul_sub]

/-- Exact unweighted Hilbert coordinates for all localized scalar coefficients. -/
def componentRep {r : ℝ} {f : C.Index → κ → FourSpace → ℝ}
    (hf : ∀ ν a, LocalSobolevMem r (P.localize ν (f ν a))) : C.Index × κ → LocalL2 :=
  fun b => localSobolevRep (hf b.1 b.2)

theorem componentSobolevENorm_eq_square {r : ℝ} {f : C.Index → κ → FourSpace → ℝ}
    (hf : ∀ ν a, LocalSobolevMem r (P.localize ν (f ν a))) :
    P.componentSobolevENorm r f = squareENorm (P.componentRep hf) := by
  unfold componentSobolevENorm componentSobolevSquare squareENorm componentRep
  rw [ENNReal.tsum_prod']
  simp only [tsum_fintype, localSobolevENN_eq_rep (hf _ _)]

def componentHilbert {r : ℝ} {f : C.Index → κ → FourSpace → ℝ}
    (hf : P.componentSobolevENorm r f < ⊤) : lp (fun _ : C.Index × κ => LocalL2) 2 :=
  ⟨P.componentRep (P.local_mem_of_component_finite hf),
    (squareENorm_finite_iff _).mp ((P.componentSobolevENorm_eq_square
      (P.local_mem_of_component_finite hf)) ▸ hf)⟩

theorem componentHilbert_norm {r : ℝ} {f : C.Index → κ → FourSpace → ℝ}
    (hf : P.componentSobolevENorm r f < ⊤) :
    P.componentSobolevENorm r f = ENNReal.ofReal ‖P.componentHilbert hf‖ := by
  rw [P.componentSobolevENorm_eq_square (P.local_mem_of_component_finite hf)]
  exact squareENorm_eq_lp (P.componentHilbert hf)

theorem componentSobolevENorm_add_eq {r : ℝ} {f g : C.Index → κ → FourSpace → ℝ}
    (hf : P.componentSobolevENorm r f < ⊤) (hg : P.componentSobolevENorm r g < ⊤) :
    P.componentSobolevENorm r (f + g) = ENNReal.ofReal ‖P.componentHilbert hf + P.componentHilbert hg‖ := by
  have hm (ν : C.Index) (a : κ) : LocalSobolevMem r (P.localize ν ((f+g) ν a)) := by
    simpa only [Pi.add_apply, P.localize_add] using
      (P.local_mem_of_component_finite hf ν a).add (P.local_mem_of_component_finite hg ν a)
  rw [P.componentSobolevENorm_eq_square hm]
  have he : P.componentRep hm = (P.componentHilbert hf + P.componentHilbert hg : lp (fun _ : C.Index × κ => LocalL2) 2) := by
    funext b
    change localSobolevRep (hm b.1 b.2) = _
    simp only [Pi.add_apply, P.localize_add] at *
    exact localSobolevRep_add (P.local_mem_of_component_finite hf b.1 b.2) (P.local_mem_of_component_finite hg b.1 b.2)
  rw [he]
  exact squareENorm_eq_lp _

theorem componentSobolevENorm_smul_eq {r : ℝ} {f : C.Index → κ → FourSpace → ℝ}
    (hf : P.componentSobolevENorm r f < ⊤) (c : ℝ) :
    P.componentSobolevENorm r (c • f) = ENNReal.ofReal ‖c • P.componentHilbert hf‖ := by
  have hm (ν : C.Index) (a : κ) : LocalSobolevMem r (P.localize ν ((c • f) ν a)) := by
    simpa only [Pi.smul_apply, P.localize_smul] using
      (P.local_mem_of_component_finite hf ν a).smul c
  rw [P.componentSobolevENorm_eq_square hm]
  have he : P.componentRep hm = (c • P.componentHilbert hf : lp (fun _ : C.Index × κ => LocalL2) 2) := by
    funext b
    change localSobolevRep (hm b.1 b.2) = _
    simp only [Pi.smul_apply, P.localize_smul] at *
    exact localSobolevRep_smul (P.local_mem_of_component_finite hf b.1 b.2) c
  rw [he]
  exact squareENorm_eq_lp _

theorem componentSobolevENorm_sub_eq {r : ℝ} {f g : C.Index → κ → FourSpace → ℝ}
    (hf : P.componentSobolevENorm r f < ⊤) (hg : P.componentSobolevENorm r g < ⊤) :
    P.componentSobolevENorm r (f - g) = ENNReal.ofReal ‖P.componentHilbert hf - P.componentHilbert hg‖ := by
  have hm (ν : C.Index) (a : κ) : LocalSobolevMem r (P.localize ν ((f-g) ν a)) := by
    simpa only [Pi.sub_apply, P.localize_sub] using
      (P.local_mem_of_component_finite hf ν a).sub (P.local_mem_of_component_finite hg ν a)
  rw [P.componentSobolevENorm_eq_square hm]
  have he : P.componentRep hm = (P.componentHilbert hf - P.componentHilbert hg : lp (fun _ : C.Index × κ => LocalL2) 2) := by
    funext b
    change localSobolevRep (hm b.1 b.2) = _
    simp only [Pi.sub_apply, P.localize_sub] at *
    exact localSobolevRep_sub (P.local_mem_of_component_finite hf b.1 b.2) (P.local_mem_of_component_finite hg b.1 b.2)
  rw [he]
  exact squareENorm_eq_lp _

end SobolevPartition
end K24.Global

/- Inlined checked GeometryReuse; exact source/excerpt hashes in PROVENANCE.json. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.CoverRegularityProof

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {F : LocalFiniteCover M}

omit [IsManifold I4 ∞ M] in
theorem contMDiffAt_lift (c : LocalCoverChart F) (x : FourSpace)
    (hx : x ∈ c.outerDomain) : ContMDiffAt I4 I4 ∞ c.lift x := by
  apply F.projectionSmooth.contMDiffAt.comp
  exact contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas c.coordinate_mem_atlas) (c.outerSubsetTarget hx)

theorem transition_smooth (c : LocalCoverChart F) (q : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    ContDiffAt ℝ ∞ ((chartAt FourSpace q) ∘ c.lift) x := by
  apply ContMDiffAt.contDiffAt
  exact (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hq).comp x
    (contMDiffAt_lift c x hx)

theorem transition_derivative (c : LocalCoverChart F) (q : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    ∃ d : FourSpace ≃L[ℝ] FourSpace,
      HasFDerivAt ((chartAt FourSpace q) ∘ c.lift) (d : FourSpace →L[ℝ] FourSpace) x := by
  let e := chartAt FourSpace q
  let de := (mdifferentiable_chart (I := I4) q).mfderiv hq
  let d : FourSpace ≃L[ℝ] FourSpace := (c.tangentMap x).trans de
  have heq : (d : FourSpace →L[ℝ] FourSpace) =
      mfderiv I4 I4 (e ∘ c.lift) x := by
    rw [mfderiv_comp x ((mdifferentiable_chart (I := I4) q).mdifferentiableAt hq)
      ((contMDiffAt_lift c x hx).mdifferentiableAt (by simp))]
    have hc : (c.tangentMap x).toContinuousLinearMap = mfderiv I4 I4 c.lift x :=
      c.tangentMap_eq x hx
    rw [← hc]
    rfl
  refine ⟨d, ?_⟩
  rw [heq, mfderiv_eq_fderiv]
  exact ((transition_smooth c q x hx hq).differentiableAt (by simp)).hasFDerivAt

theorem matrixToBilinear_apply (A : Mat4) (v w : FourSpace) :
    matrixToBilinear A v w = ∑ a, ∑ b, v a * A a b * w b := by
  simp [matrixToBilinear, coordProj, mul_assoc]

def pullbackCoefficients (A : FourSpace → Mat4) (S : FourSpace → FourSpace)
    (y : FourSpace) : Mat4 :=
  fun i j => matrixToBilinear (A (S y))
    (fderiv ℝ S y (basisVector i)) (fderiv ℝ S y (basisVector j))

theorem contDiffAt_pullbackCoefficients (A : FourSpace → Mat4)
    (S : FourSpace → FourSpace) (y : FourSpace) (k : ℕ)
    (hA : ContDiffAt ℝ k A (S y)) (hS : ContDiffAt ℝ ∞ S y) :
    ContDiffAt ℝ k (pullbackCoefficients A S) y := by
  have hT : ContDiffAt ℝ k (fderiv ℝ S) y := hS.fderiv_right (by exact_mod_cast (le_top : (k : ℕ∞) + 1 ≤ ⊤))
  have hAS : ContDiffAt ℝ k (A ∘ S) y := hA.comp y (hS.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
  have hV (i a : Fin 4) :
      ContDiffAt ℝ k (fun z => (fderiv ℝ S z (basisVector i)) a) y :=
    (coordProj a).contDiff.contDiffAt.comp y (hT.clm_apply contDiffAt_const)
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [pullbackCoefficients, matrixToBilinear_apply]
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro b _
  exact ((hV i a).mul (contDiffAt_pi.mp (contDiffAt_pi.mp hAS a) b)).mul (hV j b)


end K24.Global.CoverRegularityProof

/- Inlined checked LocalGeometry; exact source/excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Manifold ContDiff Topology Matrix.Norms.Elementwise
namespace K24.Global
open CoverRegularityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {F : LocalFiniteCover M}

theorem LocalCoverChart.liftedCov2_eq_chart_pullback (c : LocalCoverChart F)
    (u : RawCov2 M) (q : M) (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    c.liftedCov2 u x = pullbackCoefficients (cov2InChart u q) ((chartAt FourSpace q) ∘ c.lift) x := by
  let e := chartAt FourSpace q
  have hder := mfderiv_comp (I := I4) (I' := I4) (I'' := I4) x
    ((mdifferentiable_chart (I := I4) q).mdifferentiableAt hq)
    ((contMDiffAt_lift c x hx).mdifferentiableAt (by simp))
  have hc : (c.tangentMap x).toContinuousLinearMap = mfderiv I4 I4 c.lift x := c.tangentMap_eq x hx
  rw [← hc, mfderiv_eq_fderiv] at hder
  have hrec := cov2_chart_recovery u q (c.lift x) hq
  ext i j
  change u (c.lift x) (c.tangentMap x (basisVector i)) (c.tangentMap x (basisVector j)) = _
  rw [← hrec]
  change matrixToBilinear (cov2InChart u q (e (c.lift x)))
    ((mfderiv I4 I4 e (c.lift x)) (c.tangentMap x (basisVector i)))
    ((mfderiv I4 I4 e (c.lift x)) (c.tangentMap x (basisVector j))) = _
  simp only [pullbackCoefficients, Function.comp_apply, hder, ContinuousLinearMap.comp_apply]
  rfl

theorem LocalCoverChart.contDiffOn_liftedCov2 (c : LocalCoverChart F)
    (k : ℕ) (u : RawCov2 M) (hu : Cov2ContDiff k u) :
    ContDiffOn ℝ k (c.liftedCov2 u) c.outerDomain := by
  intro x hx
  let q := c.lift x
  have hq : c.lift x ∈ (chartAt FourSpace q).source := mem_chart_source FourSpace q
  have hT := transition_smooth c q x hx hq
  have hA : ContDiffAt ℝ k (cov2InChart u q) ((chartAt FourSpace q) (c.lift x)) :=
    (hu q _ ((chartAt FourSpace q).map_source hq)).contDiffAt
      ((chartAt FourSpace q).open_target.mem_nhds ((chartAt FourSpace q).map_source hq))
  have hC := contDiffAt_pullbackCoefficients _ _ x k hA hT
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ c.outerDomain ∧ c.lift y ∈ (chartAt FourSpace q).source :=
    by
      filter_upwards [c.outerOpen.mem_nhds hx,
        (contMDiffAt_lift c x hx).continuousAt.tendsto ((chartAt FourSpace q).open_source.mem_nhds hq)] with y hy hz
      exact ⟨hy, hz⟩
  apply (hC.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hnear] with y hy
  exact c.liftedCov2_eq_chart_pullback u q y hy.1 hy.2

namespace SobolevPartition
variable {C : BoundedLocalCover M} (P : SobolevPartition C)

theorem localize_contDiff {k : ℕ} (ν : C.Index) (f : FourSpace → ℝ)
    (hf : ContDiffOn ℝ k f (C.chart ν).outerDomain) : ContDiff ℝ k (P.localize ν f) := by
  rw [P.localize_eq_cutoff_mul]
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ (C.chart ν).outerDomain
  · exact ((P.cutoffSmooth ν).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt.mul
      ((hf x hx).contDiffAt ((C.chart ν).outerOpen.mem_nhds hx))
  · have hxn : x ∉ tsupport (P.cutoff ν) := fun h => hx (P.cutoffSupport ν h)
    have hn : ∀ᶠ y in 𝓝 x, y ∉ tsupport (P.cutoff ν) := (isClosed_tsupport (f := P.cutoff ν)).isOpen_compl.mem_nhds hxn
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    simp only [Pi.mul_apply, image_eq_zero_of_notMem_tsupport hy, zero_mul]

theorem localized_cov2_contDiff (k : ℕ) (u : RawCov2 M) (hu : Cov2ContDiff k u)
    (ν : C.Index) (a : Fin 4 × Fin 4) :
    ContDiff ℝ k (P.localize ν (cov2Components (C := C) u ν a)) := by
  apply P.localize_contDiff
  exact contDiffOn_pi.mp (contDiffOn_pi.mp ((C.chart ν).contDiffOn_liftedCov2 k u hu) a.1) a.2

/-- Every point is detected by an actually nonzero partition localization. -/
theorem exists_nonzero_cutoff_lift (p : M) :
    ∃ (ν : C.Index) (x : FourSpace), x ∈ (C.chart ν).outerDomain ∧
      (C.chart ν).lift x = p ∧ P.cutoff ν x ≠ 0 := by
  obtain ⟨a, ha⟩ := P.partition.exists_pos_of_mem (Set.mem_univ p)
  have hp : p ∈ (C.cover a).innerBaseDomain := P.subordinate a (subset_tsupport _ ha.ne')
  obtain ⟨q, hq⟩ := (C.cover a).ontoBase ⟨p, (C.cover a).innerBaseSubset hp⟩
  have hqp : (C.cover a).projection q = p := congrArg Subtype.val hq
  have hqi : q ∈ (C.cover a).projection ⁻¹' (C.cover a).innerBaseDomain := by simpa only [Set.mem_preimage, hqp] using hp
  obtain ⟨j, hj⟩ := (P.upstairsPartition a).exists_pos_of_mem hqi
  have hsub := P.upstairsSubordinate a j (subset_tsupport _ hj.ne')
  let ν : C.Index := ⟨a, j⟩
  let x : FourSpace := (C.localChart a j).coordinate q
  have hx : x ∈ (C.chart ν).outerDomain := hsub.2
  have hlift : (C.chart ν).lift x = p := by
    change (C.cover a).projection ((C.localChart a j).coordinate.symm ((C.localChart a j).coordinate q)) = p
    rw [(C.localChart a j).coordinate.left_inv hsub.1, hqp]
  refine ⟨ν, x, hx, hlift, ?_⟩
  rw [P.cutoff_eq_partition ν x hx, hlift]
  have he : (C.chart ν).liftToCover x = q := (C.localChart a j).coordinate.left_inv hsub.1
  rw [he]
  exact mul_ne_zero ha.ne' hj.ne'

end SobolevPartition
end K24.Global

/- Inlined checked LocalizedGluing; exact source/excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Manifold ContDiff Topology Matrix.Norms.Elementwise
namespace K24.Global.CoverRegularityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {F : LocalFiniteCover M}
theorem local_inverse_outer (c : LocalCoverChart F) (q : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    ∃ S : FourSpace → FourSpace,
      S (chartAt FourSpace q (c.lift x)) = x ∧
      ContDiffAt ℝ ∞ S (chartAt FourSpace q (c.lift x)) ∧
      (∀ᶠ y in 𝓝 (chartAt FourSpace q (c.lift x)), S y ∈ c.outerDomain) ∧
      (c.lift ∘ S =ᶠ[𝓝 (chartAt FourSpace q (c.lift x))] (chartAt FourSpace q).symm) := by
  have hxo : x ∈ c.outerDomain := hx
  let f : FourSpace → FourSpace := (chartAt FourSpace q) ∘ c.lift
  have hf : ContDiffAt ℝ ∞ f x := transition_smooth c q x hxo hq
  obtain ⟨d, hd⟩ := transition_derivative c q x hxo hq
  have hd' : HasFDerivAt f (d : FourSpace →L[ℝ] FourSpace) x := hd
  let S := hf.localInverse hd' (by simp)
  have hSx : S (f x) = x := hf.localInverse_apply_image hd' (by simp)
  have hS : ContDiffAt ℝ ∞ S (f x) := hf.to_localInverse hd' (by simp)
  have hSt : Tendsto S (𝓝 (f x)) (𝓝 x) := by
    simpa only [hSx] using hS.continuousAt.tendsto
  have hinner : ∀ᶠ y in 𝓝 (f x), S y ∈ c.outerDomain :=
    hSt (c.outerOpen.mem_nhds hx)
  have hsource : ∀ᶠ y in 𝓝 (f x), c.lift (S y) ∈ (chartAt FourSpace q).source :=
    ((contMDiffAt_lift c x hxo).continuousAt.tendsto.comp hSt)
      ((chartAt FourSpace q).open_source.mem_nhds hq)
  have hright : ∀ᶠ y in 𝓝 (f x), f (S y) = y :=
    (hf.hasStrictFDerivAt' hd' (by simp)).eventually_right_inverse
  refine ⟨S, hSx, hS, hinner, ?_⟩
  filter_upwards [hsource, hright] with y hy hy'
  change c.lift (S y) = (chartAt FourSpace q).symm y
  calc
    c.lift (S y) = (chartAt FourSpace q).symm (f (S y)) :=
      ((chartAt FourSpace q).left_inv hy).symm
    _ = (chartAt FourSpace q).symm y := congrArg (chartAt FourSpace q).symm hy'


omit [IsManifold I4 ∞ M] in
theorem pullbackCoefficients_eventually_outer (c : LocalCoverChart F) (u : RawCov2 M)
    (q : M) (S : FourSpace → FourSpace) (y : FourSpace)
    (hS : ContDiffAt ℝ ∞ S y)
    (hinner : ∀ᶠ z in 𝓝 y, S z ∈ c.outerDomain)
    (heq : c.lift ∘ S =ᶠ[𝓝 y] (chartAt FourSpace q).symm) :
    pullbackCoefficients (c.liftedCov2 u) S =ᶠ[𝓝 y] cov2InChart u q := by
  have hS1 : ContDiffAt ℝ 1 S y := hS.of_le (by simp)
  have hSnear := hS1.eventually (by simp)
  filter_upwards [hinner, heq.eventuallyEq_nhds, hSnear] with z hz heqz hSz
  have hzo : S z ∈ c.outerDomain := hz
  have hDL := (contMDiffAt_lift c (S z) hzo).mdifferentiableAt (by simp)
  have hDS := (hSz.differentiableAt (by simp)).mdifferentiableAt
  have hder := heqz.mfderiv_eq (I := I4) (I' := I4)
  rw [mfderiv_comp z hDL hDS, mfderiv_eq_fderiv] at hder
  have hc : (c.tangentMap (S z)).toContinuousLinearMap =
      mfderiv I4 I4 c.lift (S z) := c.tangentMap_eq (S z) hzo
  rw [← hc] at hder
  have hvec (i : Fin 4) : c.tangentMap (S z) (fderiv ℝ S z (basisVector i)) =
      mfderiv I4 I4 (chartAt FourSpace q).symm z (basisVector i) :=
    congrArg (fun D : FourSpace →L[ℝ] FourSpace => D (basisVector i)) hder
  have hmat := matrixToBilinear_recover
    (bilinearPullback (u (c.lift (S z))) (c.tangentMap (S z)).toContinuousLinearMap)
  change matrixToBilinear (c.liftedCov2 u (S z)) = _ at hmat
  ext i j
  change matrixToBilinear (c.liftedCov2 u (S z))
    (fderiv ℝ S z (basisVector i)) (fderiv ℝ S z (basisVector j)) = _
  rw [hmat]
  simp only [bilinearPullback_apply]
  change u (c.lift (S z)) (c.tangentMap (S z) (fderiv ℝ S z (basisVector i)))
    (c.tangentMap (S z) (fderiv ℝ S z (basisVector j))) = _
  rw [hvec i, hvec j]
  change u (c.lift (S z)) _ _ = u ((chartAt FourSpace q).symm z) _ _
  rw [show c.lift (S z) = (chartAt FourSpace q).symm z from heqz.self_of_nhds]

end K24.Global.CoverRegularityProof
namespace K24.Global
open CoverRegularityProof
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
namespace SobolevPartition
variable {C : BoundedLocalCover M} (P : SobolevPartition C)

theorem contDiffAt_lifted_of_localized (k : ℕ) (u : RawCov2 M)
    (h : ∀ ν a, ContDiff ℝ k (P.localize ν (cov2Components (C := C) u ν a)))
    (ν : C.Index) (x : FourSpace) (hx : P.cutoff ν x ≠ 0) :
    ContDiffAt ℝ k ((C.chart ν).liftedCov2 u) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hcut : ContDiffAt ℝ k (P.cutoff ν) x :=
    ((P.cutoffSmooth ν).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
  have hd := (h ν (i,j)).contDiffAt.div hcut hx
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ y in 𝓝 x, P.cutoff ν y ≠ 0 := hcut.continuousAt.eventually_ne hx
  filter_upwards [hn] with y hy
  simp only [Pi.div_apply, P.localize_eq_cutoff_mul, Pi.mul_apply, cov2Components]
  exact (mul_div_cancel_left₀ _ hy).symm

theorem cov2ContDiff_of_localized (k : ℕ) (u : RawCov2 M)
    (h : ∀ ν a, ContDiff ℝ k (P.localize ν (cov2Components (C := C) u ν a))) :
    Cov2ContDiff k u := by
  intro q y hy
  obtain ⟨ν, x, hx, hxy, hnonzero⟩ := P.exists_nonzero_cutoff_lift ((chartAt FourSpace q).symm y)
  have hq : (C.chart ν).lift x ∈ (chartAt FourSpace q).source := by
    rw [hxy]
    exact (chartAt FourSpace q).map_target hy
  obtain ⟨S, hSx, hS, houter, heq⟩ := local_inverse_outer (C.chart ν) q x hx hq
  have hbase : chartAt FourSpace q ((C.chart ν).lift x) = y := by
    rw [hxy]
    exact (chartAt FourSpace q).right_inv hy
  rw [hbase] at hSx hS houter heq
  have hA : ContDiffAt ℝ k ((C.chart ν).liftedCov2 u) (S y) := by
    rw [hSx]
    exact P.contDiffAt_lifted_of_localized k u h ν x hnonzero
  have hpull := contDiffAt_pullbackCoefficients _ S y k hA hS
  have hequal := pullbackCoefficients_eventually_outer (C.chart ν) u q S y hS houter heq
  exact (hpull.congr_of_eventuallyEq hequal.symm).contDiffWithinAt

end SobolevPartition
end K24.Global

/- Inlined checked FiberReuse; exact source/excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped NNReal ENNReal Topology Matrix.Norms.Elementwise
open Filter
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
local instance tangentFiniteDimensional (p : M) : FiniteDimensional ℝ (TangentSpace I4 p) := by
  exact inferInstanceAs (FiniteDimensional ℝ FourSpace)

local instance tangentT2 (p : M) : T2Space (TangentSpace I4 p) := by
  exact inferInstanceAs (T2Space FourSpace)

def LocalCoverChart.cov2CoordinateLinearMap {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (x : FourSpace) :
    (TangentSpace I4 (c.lift x) →L[ℝ] (TangentSpace I4 (c.lift x) →L[ℝ] ℝ)) →ₗ[ℝ] Mat4 where
  toFun a := fun i j => a (c.tangentMap x (basisVector i)) (c.tangentMap x (basisVector j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def LocalCoverChart.cov2ReconstructLinearMap {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (x : FourSpace) :
    Mat4 →ₗ[ℝ] (TangentSpace I4 (c.lift x) →L[ℝ]
      (TangentSpace I4 (c.lift x) →L[ℝ] ℝ)) where
  toFun A := bilinearPullback (matrixToBilinear A) (c.tangentMap x).symm.toContinuousLinearMap
  map_add' A B := by
    ext v w
    change matrixToBilinear (A + B) ((c.tangentMap x).symm v) ((c.tangentMap x).symm w) =
      matrixToBilinear A ((c.tangentMap x).symm v) ((c.tangentMap x).symm w) +
      matrixToBilinear B ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)
    simp [matrixToBilinear, Finset.sum_add_distrib, mul_add, add_mul]
  map_smul' r A := by
    ext v w
    change matrixToBilinear (r • A) ((c.tangentMap x).symm v) ((c.tangentMap x).symm w) =
      r * matrixToBilinear A ((c.tangentMap x).symm v) ((c.tangentMap x).symm w)
    simp [matrixToBilinear, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem LocalCoverChart.cov2_reconstruct {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (x : FourSpace) (u : RawCov2 M) :
    c.cov2ReconstructLinearMap x (c.liftedCov2 u x) = u (c.lift x) := by
  have h := matrixToBilinear_recover (bilinearPullback (u (c.lift x)) (c.tangentMap x).toContinuousLinearMap)
  change (bilinearPullback (matrixToBilinear (c.liftedCov2 u x))
    (c.tangentMap x).symm.toContinuousLinearMap) = u (c.lift x)
  change matrixToBilinear (c.liftedCov2 u x) = _ at h
  rw [h]
  ext v w
  change u (c.lift x) ((c.tangentMap x) ((c.tangentMap x).symm v))
    ((c.tangentMap x) ((c.tangentMap x).symm w)) = u (c.lift x) v w
  rw [(c.tangentMap x).apply_symm_apply, (c.tangentMap x).apply_symm_apply]

@[simp] theorem LocalCoverChart.liftedCov2_sub {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u v : RawCov2 M) :
    c.liftedCov2 (u - v) = c.liftedCov2 u - c.liftedCov2 v := rfl

@[simp] theorem LocalCoverChart.liftedCov2_add {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (u v : RawCov2 M) :
    c.liftedCov2 (u + v) = c.liftedCov2 u + c.liftedCov2 v := rfl

@[simp] theorem LocalCoverChart.liftedCov2_smul {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (r : ℝ) (u : RawCov2 M) :
    c.liftedCov2 (r • u) = r • c.liftedCov2 u := rfl

@[simp] theorem LocalCoverChart.liftedCov2_zero {F : LocalFiniteCover M}
    (c : LocalCoverChart F) : c.liftedCov2 (0 : RawCov2 M) = 0 := rfl

set_option maxHeartbeats 800000 in
theorem LocalCoverChart.liftedCov2_tendsto {F : LocalFiniteCover M}
    (c : LocalCoverChart F) (f : ℕ → RawCov2 M) (u : RawCov2 M)
    (ht : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (u p))) (x : FourSpace) :
    Tendsto (fun n => c.liftedCov2 (f n) x) atTop (𝓝 (c.liftedCov2 u x)) :=
  by
    change Tendsto (fun n => c.cov2CoordinateLinearMap x (f n (c.lift x))) atTop
      (𝓝 (c.cov2CoordinateLinearMap x (u (c.lift x))))
    exact ((c.cov2CoordinateLinearMap x).continuous_of_finiteDimensional.tendsto _).comp (ht (c.lift x))
def tensorEvaluationLinearMap (p : M) (v w : TangentSpace I4 p) :
    (TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ)) →ₗ[ℝ] ℝ where
  toFun a := a v w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isSymmetricCov2_of_pointwise_tendsto {f : ℕ → RawCov2 M} {u : RawCov2 M}
    (hf : ∀ n, IsSymmetricCov2 (f n))
    (ht : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (u p))) : IsSymmetricCov2 u := by
  intro p v w
  have h₁ : Tendsto (fun n => f n p v w) atTop (𝓝 (u p v w)) :=
    by
      change Tendsto (fun n => tensorEvaluationLinearMap p v w (f n p)) atTop
        (𝓝 (tensorEvaluationLinearMap p v w (u p)))
      exact ((tensorEvaluationLinearMap p v w).continuous_of_finiteDimensional.tendsto _).comp (ht p)
  have h₂ : Tendsto (fun n => f n p w v) atTop (𝓝 (u p w v)) :=
    by
      change Tendsto (fun n => tensorEvaluationLinearMap p w v (f n p)) atTop
        (𝓝 (tensorEvaluationLinearMap p w v (u p)))
      exact ((tensorEvaluationLinearMap p w v).continuous_of_finiteDimensional.tendsto _).comp (ht p)
  apply tendsto_nhds_unique h₁
  convert h₂ using 1
  exact funext (fun n => hf n p v w)


end K24.Global

/- Inlined checked TensorComplete; exact source/excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology ContDiff Matrix.Norms.Elementwise
namespace K24.Global
attribute [local instance] tangentFiniteDimensional tangentT2
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
namespace SobolevPartition
variable {C : BoundedLocalCover M} (P : SobolevPartition C)

@[simp] theorem cov2Components_sub (u v : RawCov2 M) :
    cov2Components (C := C) (u - v) = cov2Components u - cov2Components v := rfl
@[simp] theorem cov2Components_add (u v : RawCov2 M) :
    cov2Components (C := C) (u + v) = cov2Components u + cov2Components v := rfl
@[simp] theorem cov2Components_smul (a : ℝ) (u : RawCov2 M) :
    cov2Components (C := C) (a • u) = a • cov2Components u := rfl
@[simp] theorem cov2Components_zero : cov2Components (C := C) (0 : RawCov2 M) = 0 := rfl

theorem cov2SobolevENorm_sub_eq {r : ℝ} {u v : RawCov2 M}
    (hu : P.cov2SobolevENorm r u < ⊤) (hv : P.cov2SobolevENorm r v < ⊤) :
    P.cov2SobolevENorm r (u-v) =
      ENNReal.ofReal ‖P.componentHilbert hu - P.componentHilbert hv‖ := by
  exact P.componentSobolevENorm_sub_eq hu hv

theorem cov2_pointwise_limit_of_localized {f : ℕ → RawCov2 M}
    (g : C.Index → (Fin 4 × Fin 4) → FourSpace → ℝ)
    (hg : ∀ ν a x, Tendsto (fun n => P.localize ν (cov2Components (C := C) (f n) ν a) x)
      atTop (𝓝 (g ν a x))) :
    ∃ u : RawCov2 M, ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (u p)) := by
  classical
  have hp (p : M) : ∃ v : TangentSpace I4 p →L[ℝ] (TangentSpace I4 p →L[ℝ] ℝ),
      Tendsto (fun n => f n p) atTop (𝓝 v) := by
    obtain ⟨ν, x, _, hxp, hcut⟩ := P.exists_nonzero_cutoff_lift p
    subst p
    let A : Mat4 := fun i j => g ν (i,j) x / P.cutoff ν x
    have ht : Tendsto (fun n => (C.chart ν).liftedCov2 (f n) x) atTop (𝓝 A) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_pi_nhds.mpr
      intro j
      have h := (hg ν (i,j) x).div_const (P.cutoff ν x)
      simpa only [P.localize_eq_cutoff_mul, Pi.mul_apply, cov2Components,
        mul_div_cancel_left₀ _ hcut] using h
    refine ⟨(C.chart ν).cov2ReconstructLinearMap x A, ?_⟩
    have h := (((C.chart ν).cov2ReconstructLinearMap x).continuous_of_finiteDimensional.tendsto A).comp ht
    simpa only [Function.comp_def, LocalCoverChart.cov2_reconstruct] using h
  choose u hu using hp
  exact ⟨u, hu⟩

theorem localize_cov2_tendsto {f : ℕ → RawCov2 M} {u : RawCov2 M}
    (hf : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (u p))) (ν : C.Index)
    (a : Fin 4 × Fin 4) (x : FourSpace) :
    Tendsto (fun n => P.localize ν (cov2Components (C := C) (f n) ν a) x) atTop
      (𝓝 (P.localize ν (cov2Components (C := C) u ν a) x)) := by
  have ht := (((C.chart ν).liftedCov2_tendsto f u hf x).apply_nhds a.1).apply_nhds a.2
  simpa only [P.localize_eq_cutoff_mul, Pi.mul_apply, cov2Components] using ht.const_mul (P.cutoff ν x)

theorem tensorSobolev_complete (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r)
    (f : ℕ → RawCov2 M) (hf : ∀ n, f n ∈ tensorSobolevSpace P k r)
    (hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      P.cov2SobolevENorm r (f i - f j) < ENNReal.ofReal eps) :
    ∃ u ∈ tensorSobolevSpace P k r, ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N,
      P.cov2SobolevENorm r (f i - u) < ENNReal.ofReal eps := by
  classical
  let Vn : ℕ → lp (fun _ : C.Index × (Fin 4 × Fin 4) => LocalL2) 2 :=
    fun n => P.componentHilbert (hf n).2.2
  have hC : CauchySeq Vn := by
    apply Metric.cauchySeq_iff.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := hc eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
    simpa only [dist_eq_norm, P.cov2SobolevENorm_sub_eq (hf i).2.2 (hf j).2.2] using hN i hi j hj
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hC
  have hex (b : C.Index × (Fin 4 × Fin 4)) :
      ∃ g : FourSpace → ℝ, ContDiff ℝ k g ∧
        ∃ hg : LocalSobolevMem r g, localSobolevRep hg = V b ∧
          ∀ x, Tendsto (fun n => P.localize b.1 (cov2Components (C := C) (f n) b.1 b.2) x)
            atTop (𝓝 (g x)) := by
    let fn := fun n => P.localize b.1 (cov2Components (C := C) (f n) b.1 b.2)
    have hm (n : ℕ) : LocalSobolevMem r (fn n) := P.local_mem_of_component_finite (hf n).2.2 b.1 b.2
    have ht : Tendsto (fun n => localSobolevRep (hm n)) atTop (𝓝 (V b)) :=
      ((lp.evalCLM ℝ (fun _ : C.Index × (Fin 4 × Fin 4) => LocalL2) 2 b).continuous.tendsto V).comp hV
    have hs (n : ℕ) : Function.support (fn n) ⊆ tsupport (P.cutoff b.1) := by
      intro x hx
      apply subset_tsupport
      intro hz
      apply hx
      simp only [fn, P.localize_eq_cutoff_mul, Pi.mul_apply, hz, zero_mul]
    obtain ⟨g, hgC, _, hgm, hgr, hgt⟩ := localSobolev_compact_limit k r hr
      (tsupport (P.cutoff b.1)) (P.cutoffCompact b.1) fn
      (fun n => (P.localized_cov2_contDiff k (f n) (hf n).2.1 b.1 b.2).continuous)
      hs hm (V b) ht
    exact ⟨g, hgC, hgm, hgr, hgt⟩
  choose g hgC hgm hgr hgt using hex
  obtain ⟨u, hu⟩ := P.cov2_pointwise_limit_of_localized (fun ν a => g (ν,a))
    (fun ν a => hgt (ν,a))
  have heq (ν : C.Index) (a : Fin 4 × Fin 4) :
      P.localize ν (cov2Components (C := C) u ν a) = g (ν,a) := by
    funext x
    exact tendsto_nhds_unique (P.localize_cov2_tendsto hu ν a x) (hgt (ν,a) x)
  have hum (ν : C.Index) (a : Fin 4 × Fin 4) :
      LocalSobolevMem r (P.localize ν (cov2Components (C := C) u ν a)) := heq ν a ▸ hgm (ν,a)
  have hrep : P.componentRep hum = (V : C.Index × (Fin 4 × Fin 4) → LocalL2) := by
    funext b
    change localSobolevRep (hum b.1 b.2) = V b
    simpa only [heq b.1 b.2] using hgr b
  have hnorm : P.cov2SobolevENorm r u = ENNReal.ofReal ‖V‖ := by
    rw [cov2SobolevENorm, P.componentSobolevENorm_eq_square hum, hrep]
    exact squareENorm_eq_lp V
  have hfinite : P.cov2SobolevENorm r u < ⊤ := hnorm ▸ ENNReal.ofReal_lt_top
  have huc : Cov2ContDiff k u := P.cov2ContDiff_of_localized k u (fun ν a => heq ν a ▸ hgC (ν,a))
  have huV : P.componentHilbert hfinite = V := by
    apply Subtype.ext
    exact hrep
  refine ⟨u, ⟨isSymmetricCov2_of_pointwise_tendsto (fun n => (hf n).1) hu, huc, hfinite⟩,
    fun eps heps => ?_⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hV eps heps
  refine ⟨N, fun i hi => ?_⟩
  rw [P.cov2SobolevENorm_sub_eq (hf i).2.2 hfinite, huV]
  exact (ENNReal.ofReal_lt_ofReal_iff heps).mpr (by simpa only [dist_eq_norm] using hN i hi)

end SobolevPartition
end K24.Global

/- Inlined checked TensorBanach; exact source/excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
open scoped NNReal ENNReal Topology ContDiff Matrix.Norms.Elementwise
namespace K24.Global
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]
namespace SobolevPartition
variable {C : BoundedLocalCover M} (P : SobolevPartition C)

theorem cov2SobolevENorm_zero (r : ℝ) : P.cov2SobolevENorm r (0 : RawCov2 M) = 0 := by
  simp [cov2SobolevENorm, componentSobolevENorm, componentSobolevSquare,
    cov2Components_zero, P.localize_eq_cutoff_mul]

theorem cov2SobolevENorm_definite (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r)
    (u : RawCov2 M) (hu : P.Cov2Sobolev k r u) (hn : P.cov2SobolevENorm r u = 0) : u = 0 := by
  have hn' : ENNReal.ofReal ‖P.componentHilbert hu.2‖ = 0 := (P.componentHilbert_norm hu.2).symm.trans hn
  have hz : P.componentHilbert hu.2 = 0 := norm_eq_zero.mp
    (le_antisymm (ENNReal.ofReal_eq_zero.mp hn') (norm_nonneg _))
  have hlocal (ν : C.Index) (a : Fin 4 × Fin 4) :
      P.localize ν (cov2Components (C := C) u ν a) = 0 := by
    let hm := P.local_mem_of_component_finite hu.2 ν a
    have hrep : localSobolevRep hm = 0 := congrArg (fun v => v (ν,a)) hz
    have he := besselClassicalMap_rep_eq k r hr _
      (P.localized_cov2_contDiff k u hu.1 ν a).continuous hm
    change (besselClassicalMap k r hr (localSobolevRep hm) : FourSpace → ℂ) = _ at he
    rw [hrep, map_zero] at he
    funext x
    apply Complex.ofReal_injective
    simpa only [complexifyLocal, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Complex.ofReal_zero] using
      (congrFun he x).symm
  funext p
  obtain ⟨ν, x, _, hxp, hc⟩ := P.exists_nonzero_cutoff_lift p
  subst p
  have hmat : (C.chart ν).liftedCov2 u x = 0 := by
    ext i j
    have h := congrFun (hlocal ν (i,j)) x
    simp only [P.localize_eq_cutoff_mul, Pi.mul_apply, cov2Components, Pi.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  rw [← (C.chart ν).cov2_reconstruct x u, hmat, map_zero]
  rfl

theorem cov2SobolevENorm_triangle {r : ℝ} {u v : RawCov2 M}
    (hu : P.cov2SobolevENorm r u < ⊤) (hv : P.cov2SobolevENorm r v < ⊤) :
    P.cov2SobolevENorm r (u + v) ≤ P.cov2SobolevENorm r u + P.cov2SobolevENorm r v := by
  change P.componentSobolevENorm r (cov2Components (C := C) u + cov2Components (C := C) v) ≤ _
  rw [P.componentSobolevENorm_add_eq hu hv]
  change _ ≤ P.componentSobolevENorm r (cov2Components (C := C) u) + P.componentSobolevENorm r (cov2Components (C := C) v)
  rw [P.componentHilbert_norm hu, P.componentHilbert_norm hv, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)

theorem cov2SobolevENorm_smul {r : ℝ} {u : RawCov2 M}
    (hu : P.cov2SobolevENorm r u < ⊤) (c : ℝ) :
    P.cov2SobolevENorm r (c • u) = ENNReal.ofReal |c| * P.cov2SobolevENorm r u := by
  change P.componentSobolevENorm r (c • cov2Components (C := C) u) = _
  rw [P.componentSobolevENorm_smul_eq hu c, norm_smul, Real.norm_eq_abs,
    ENNReal.ofReal_mul (abs_nonneg c)]
  rw [show P.cov2SobolevENorm r u = ENNReal.ofReal ‖P.componentHilbert hu‖ from P.componentHilbert_norm hu]

end SobolevPartition

theorem tensorSobolev_banach_proof {C : BoundedLocalCover M} (P : SobolevPartition C)
    (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r) :
    SectionBanachSpace (tensorSobolevSpace P k r) (P.cov2SobolevENorm r) where
  zero_mem := by
    refine ⟨fun _ _ _ => rfl, ?_, by rw [P.cov2SobolevENorm_zero]; exact ENNReal.zero_lt_top⟩
    intro c
    change ContDiffOn ℝ k (fun _ : FourSpace => (0 : Mat4)) (chartAt FourSpace c).target
    exact contDiffOn_const
  add_mem u hu v hv := by
    refine ⟨?_, ?_, (P.cov2SobolevENorm_triangle hu.2.2 hv.2.2).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hu.2.2, hv.2.2⟩)⟩
    · intro p x y
      change u p x y + v p x y = u p y x + v p y x
      rw [hu.1 p x y, hv.1 p x y]
    · intro c
      exact (hu.2.1 c).add (hv.2.1 c)
  smul_mem a u hu := by
    refine ⟨?_, ?_, ?_⟩
    · intro p x y
      change a * u p x y = a * u p y x
      rw [hu.1 p x y]
    · intro c
      exact (hu.2.1 c).const_smul a
    · rw [P.cov2SobolevENorm_smul hu.2.2 a]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2.2
  finite u hu := hu.2.2
  zero_norm := P.cov2SobolevENorm_zero r
  definite u hu := P.cov2SobolevENorm_definite k r hr u hu.2
  triangle u hu v hv := P.cov2SobolevENorm_triangle hu.2.2 hv.2.2
  homogeneous a u hu := P.cov2SobolevENorm_smul hu.2.2 a
  complete := P.tensorSobolev_complete k r hr

end K24.Global

namespace K24.Global
universe u
theorem _root_.solution :
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [CompactSpace M] [T2Space M],
    ∀ (C : BoundedLocalCover M) (P : SobolevPartition C) (k : ℕ) (r : ℝ),
      (k : ℝ) + 2 < r →
      SectionBanachSpace (tensorSobolevSpace P k r) (P.cov2SobolevENorm r) := by
  intro M _ _ _ _ _ C P k r hr
  exact tensorSobolev_banach_proof P k r hr
end K24.Global
