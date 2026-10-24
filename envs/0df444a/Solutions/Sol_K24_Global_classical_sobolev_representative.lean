-- Prove2me | solution 1 for K24.Global.classical_sobolev_representative
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T20:22:52.791507+00:00
-- url     : https://prove2.me/submissions/e39489c9-6c21-470f-a55d-64712d888d05

import Definitions.Def_K24GlobalStatement
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
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

open K24.Global in
theorem solution :
  ∀ (k : ℕ) (r : ℝ), (k : ℝ) + 2 < r → ∃ A : ℝ≥0,
    ∀ f : SobolevModel → ℝ, LocalSobolevMem r f →
    ∃ g : SobolevModel → ℝ,
      ContDiff ℝ k g ∧ f =ᵐ[volume] g ∧ LocalSobolevMem r g ∧
      localSobolevENN r g = localSobolevENN r f ∧
      (∀ (hf : MemLp (complexifyLocal f) 2 volume)
         (hg : MemLp (complexifyLocal g) 2 volume),
        localFunctionDistribution f hf = localFunctionDistribution g hg) ∧
      ∀ j ≤ k, ∀ x : SobolevModel,
        ENNReal.ofReal ‖iteratedFDeriv ℝ j g x‖ ≤ (A : ℝ≥0∞) * localSobolevENN r f :=
  classical_sobolev_representative_proof
