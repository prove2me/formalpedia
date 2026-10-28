-- Prove2me | solution 1 for K24.Global.realOrderClassicalSobolevDerivatives
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T04:41:10.174948+00:00
-- url     : https://prove2.me/submissions/f621f527-1e27-46e0-9319-1da0d91c543a

import Definitions.Def_K24GlobalStatement
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false


/- Inlined source K24SOBPROJ_ClassicalRepresentative.lean; SHA256 43afe72c60525d4d90e9a49648af91d81eea40c73896857ed740aabf2ad578f3. -/
noncomputable section K24SOBPROJ_ClassicalRepresentative_Bundle
/- Reused accepted all-k classical representative proof. Source target 34e91b46-5f35-4cfe-a602-83d563a4f123, accepted submission e39489c9-6c21-470f-a55d-64712d888d05. Archived source SHA256 093052934ab66eccaffc86957d2ec415f1f205deac89d985a95c5ffab129b9a4. Only namespace isolation, heartbeat option, and omission of the redundant final solution alias differ. -/
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff BoundedContinuousFunction

/- Checked inverse Bessel weight integrability reused verbatim; see PROVENANCE.json. -/
namespace K24.Global.SobolevProjectionClassical
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

end K24.Global.SobolevProjectionClassical

/- Inlined FourierDistribution; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology BoundedContinuousFunction

namespace K24.Global.SobolevProjectionClassical

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

end K24.Global.SobolevProjectionClassical

/- Inlined FourierMoments; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff

namespace K24.Global.SobolevProjectionClassical

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

end K24.Global.SobolevProjectionClassical

/- Inlined InverseDerivatives; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff BoundedContinuousFunction Real

namespace K24.Global.SobolevProjectionClassical

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

end K24.Global.SobolevProjectionClassical

/- Inlined RealRepresentative; source and excerpt hashes in PROVENANCE.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 16
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped NNReal ENNReal SchwartzMap Topology ContDiff BoundedContinuousFunction

namespace K24.Global.SobolevProjectionClassical

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

end K24.Global.SobolevProjectionClassical

end K24SOBPROJ_ClassicalRepresentative_Bundle


/- Inlined source K24SOB_ExactBesselBanach.lean; SHA256 c5496787dd97d5401abfacb05060575148125346b889d1da5de5d33a28cdccae. -/
noncomputable section K24SOB_ExactBesselBanach_Bundle

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
end K24SOB_ExactBesselBanach_Bundle


/- Inlined source K24SOB_ContinuousRepresentative.lean; SHA256 58d5f93deed312b24a76bd464384af09f667f0a8af4a32cbfa5a8866793c413b. -/
noncomputable section K24SOB_ContinuousRepresentative_Bundle

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
end K24SOB_ContinuousRepresentative_Bundle


/- Inlined source K24SOBGLOBAL_Local.lean; SHA256 997674688a0d43be5056ea4d5b982b2b4326d9741136f3941993ddbe39032111. -/
noncomputable section K24SOBGLOBAL_Local_Bundle

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
end K24SOBGLOBAL_Local_Bundle


/- Inlined source K24SOBDERIV_Multiplier.lean; SHA256 5e733690c0345565fb4b93e444b754646059977939488e43bd98adad7b1465bc. -/
noncomputable section K24SOBDERIV_Multiplier_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped ENNReal NNReal SchwartzMap BoundedContinuousFunction Topology

namespace K24.Global.SobolevDerivative

/-- Quantitative form of the bounded Fourier multiplier theorem, for the
unchanged canonical Bessel norm at every real order. -/
theorem bessel_fourierMultiplier_bound {s : ℝ} {T : LocalDistribution}
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

end K24SOBDERIV_Multiplier_Bundle


/- Inlined source K24SOBDERIV_Order.lean; SHA256 ea0a982d664f362211684d1e3548c61605d226c4e77de1526f016434b8b7aa58. -/
noncomputable section K24SOBDERIV_Order_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory TemperedDistribution FourierTransform Filter
open scoped ENNReal NNReal SchwartzMap Topology Real LineDeriv

namespace K24.Global.SobolevDerivative

theorem bessel_norm_potential (s r : ℝ) (T : LocalDistribution)
    (hT : BesselMem (r + s) T) :
    besselSobolevENN s (besselPotential SobolevModel ℂ r T) =
      besselSobolevENN (r + s) T := by
  have h : BesselMem s (besselPotential SobolevModel ℂ r T) :=
    memSobolev_besselPotential_iff.mpr hT
  have heq : besselRepresentative h = besselRepresentative hT := by
    apply besselRepresentative_unique
    rw [besselPotential_besselPotential_apply, besselRepresentative_spec hT]
  rw [besselSobolevENN_of_mem h, besselSobolevENN_of_mem hT, heq]

theorem bessel_norm_complex_smul {s : ℝ} {T : LocalDistribution}
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
theorem bessel_lower_order {s r : ℝ} (hrs : r ≤ s) {T : LocalDistribution}
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

theorem normalized_derivative_symbol_bound (m x : SobolevModel) :
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
theorem bessel_directional_derivative {s : ℝ} {T : LocalDistribution}
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

end K24SOBDERIV_Order_Bundle


/- Inlined source K24SOBCLASSDERIV_Identification.lean; SHA256 64b0563ef31c6a43ac7493676b60225644fbc05591ae055ca985b047aefe2958. -/
noncomputable section K24SOBCLASSDERIV_Identification_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory TemperedDistribution Filter
open scoped NNReal ENNReal Topology SchwartzMap BoundedContinuousFunction ContDiff LineDeriv
namespace K24.Global.SobolevClassicalDerivative
open SobolevGlobal

lemma integrable_schwartz_mul_bounded (φ : 𝓢(SobolevModel, ℂ))
    (G : SobolevModel →ᵇ ℂ) : Integrable (fun x => φ x * G x) volume := by
  apply (φ.integrable.norm.mul_const ‖G‖).mono'
    (φ.continuous.mul G.continuous).aestronglyMeasurable
  filter_upwards with x
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_left (G.norm_coe_le_norm x) (norm_nonneg _)

/-- Integration by parts proves equality of genuine classical and distributional
first derivatives. Boundedness suffices; no derivative L2 premise is used. -/
theorem boundedContinuousDistribution_directional (G D : SobolevModel →ᵇ ℂ)
    (hG : Differentiable ℝ (G : SobolevModel → ℂ)) (m : SobolevModel)
    (hD : ∀ x, D x = fderiv ℝ (G : SobolevModel → ℂ) x m) :
    boundedContinuousDistribution D = ∂_{m} (boundedContinuousDistribution G) := by
  ext φ
  rw [boundedContinuousDistribution_apply, TemperedDistribution.lineDerivOp_apply_apply,
    boundedContinuousDistribution_apply]
  simp only [smul_eq_mul, SchwartzMap.neg_apply, neg_mul, integral_neg]
  have hi : Integrable (fun x => φ x * fderiv ℝ (G : SobolevModel → ℂ) x m) volume := by
    simpa only [← hD] using integrable_schwartz_mul_bounded φ D
  have hip : Integrable (fun x => fderiv ℝ (φ : SobolevModel → ℂ) x m * G x) volume :=
    integrable_schwartz_mul_bounded (∂_{m} φ) G
  have heq := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hip hi
    (integrable_schwartz_mul_bounded φ G)
    (fun x _ => φ.differentiableAt) (fun x _ => hG x)
  simpa only [← hD, SchwartzMap.lineDerivOp_apply_eq_fderiv] using heq

/-- The faithful first classical derivative of an original continuous local
Sobolev coefficient has a bounded continuous realization with exactly the
actual distributional derivative. The accepted all-k representative supplies
C1 and bounded derivatives at the strict real threshold r > 3. -/
theorem exists_bounded_classical_directional {r : ℝ} (hr : 3 < r)
    (f : SobolevModel → ℝ) (hfc : Continuous f) (hf : LocalSobolevMem r f)
    (m : SobolevModel) :
    ContDiff ℝ 1 f ∧ ∃ D : SobolevModel →ᵇ ℂ,
      (D : SobolevModel → ℂ) = complexifyLocal (fun x => fderiv ℝ f x m) ∧
      boundedContinuousDistribution D = ∂_{m} (localFunctionDistribution f hf.choose) := by
  obtain ⟨A, hA⟩ := SobolevProjectionClassical.bessel_classical_complex_representative
    1 r (by norm_num; exact hr)
  obtain ⟨G, hGD, hGC, hGb⟩ := hA (localFunctionDistribution f hf.choose) hf.choose_spec
  have hGD' : boundedContinuousDistribution G = localFunctionDistribution f hf.choose := hGD
  have hGeq := eq_complexify_of_distribution_eq hfc hf.choose G hGD'
  have hfc1 : ContDiff ℝ 1 f := by
    have heq : f = fun x => (G x).re := by
      funext x
      rw [show G x = complexifyLocal f x from congrFun hGeq x]
      rfl
    rw [heq]
    exact Complex.reCLM.contDiff.comp hGC
  have hdc : Continuous (fun x => fderiv ℝ (G : SobolevModel → ℂ) x m) :=
    (hGC.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdb (x : SobolevModel) : ‖fderiv ℝ (G : SobolevModel → ℂ) x m‖ ≤
      ((A : ℝ) * ‖besselRepresentative hf.choose_spec‖) * ‖m‖ := by
    refine ((fderiv ℝ (G : SobolevModel → ℂ) x).le_opNorm m).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg m)
    simpa only [norm_iteratedFDeriv_one] using hGb 1 le_rfl x
  let D : SobolevModel →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => fderiv ℝ (G : SobolevModel → ℂ) x m) hdc
    (((A : ℝ) * ‖besselRepresentative hf.choose_spec‖) * ‖m‖) hdb
  refine ⟨hfc1, D, ?_, ?_⟩
  · funext x
    change fderiv ℝ (G : SobolevModel → ℂ) x m = (fderiv ℝ f x m : ℂ)
    rw [hGeq]
    have hh : HasFDerivAt (complexifyLocal f)
        (Complex.ofRealCLM.comp (fderiv ℝ f x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x ((hfc1.differentiable (by simp) x).hasFDerivAt)
    rw [hh.fderiv]
    rfl
  · rw [← hGD']
    exact boundedContinuousDistribution_directional G D (hGC.differentiable (by simp)) m
      (fun _ => rfl)

end K24.Global.SobolevClassicalDerivative
end K24SOBCLASSDERIV_Identification_Bundle


/- Inlined source K24SOBCLASSDERIV_Membership.lean; SHA256 571ec31a286355ad5f0d11f1e4e09533b4c579953a511b0b6460dae6b94a68c9. -/
noncomputable section K24SOBCLASSDERIV_Membership_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory TemperedDistribution Filter
open scoped NNReal ENNReal Topology SchwartzMap BoundedContinuousFunction ContDiff LineDeriv
namespace K24.Global.SobolevClassicalDerivative
open SobolevGlobal

/-- Actual first derivatives of every original continuous local coefficient
lose exactly one real Sobolev order. Their L2 membership is proved, not assumed. -/
theorem local_directional_mem {r : ℝ} (hr : 3 < r)
    (f : SobolevModel → ℝ) (hfc : Continuous f) (hf : LocalSobolevMem r f)
    (m : SobolevModel) :
    LocalSobolevMem (r-1) (fun x => fderiv ℝ f x m) := by
  obtain ⟨hfc1, D, hDf, hDT⟩ := exists_bounded_classical_directional hr f hfc hf m
  have hdT : BesselMem (r-1) (∂_{m} (localFunctionDistribution f hf.choose)) :=
    hf.choose_spec.lineDerivOp
  obtain ⟨G, hG2, hGT⟩ := besselMem_exists_boundedContinuous_L2 (by linarith : 2 < r-1) hdT
  have hDG : D = G := boundedContinuousDistribution_injective
    (hDT.trans ((boundedContinuousDistribution_eq_L2 G hG2).trans hGT).symm)
  have hD2 : MemLp (D : SobolevModel → ℂ) 2 volume := by rw [hDG]; exact hG2
  have hdm : MemLp (complexifyLocal (fun x => fderiv ℝ f x m)) 2 volume := by
    rw [← hDf]
    exact hD2
  have hdd : localFunctionDistribution (fun x => fderiv ℝ f x m) hdm =
      ∂_{m} (localFunctionDistribution f hf.choose) := by
    rw [← hDT, boundedContinuousDistribution_eq_L2 D hD2]
    unfold localFunctionDistribution
    congr 1
    exact MemLp.toLp_congr hdm hD2 (Filter.Eventually.of_forall (fun x => (congrFun hDf x).symm))
  exact ⟨hdm, by rw [hdd]; exact hdT⟩

/-- The original derivative distribution is represented by the actual pointwise
classical coefficient derivative, for any choice of its proved L2 witness. -/
theorem local_directional_distribution {r : ℝ} (hr : 3 < r)
    (f : SobolevModel → ℝ) (hfc : Continuous f) (hf : LocalSobolevMem r f)
    (m : SobolevModel)
    (hd : MemLp (complexifyLocal (fun x => fderiv ℝ f x m)) 2 volume) :
    localFunctionDistribution (fun x => fderiv ℝ f x m) hd =
      ∂_{m} (localFunctionDistribution f hf.choose) := by
  obtain ⟨_, D, hDf, hDT⟩ := exists_bounded_classical_directional hr f hfc hf m
  have hD2 : MemLp (D : SobolevModel → ℂ) 2 volume := by rw [hDf]; exact hd
  rw [← hDT, boundedContinuousDistribution_eq_L2 D hD2]
  unfold localFunctionDistribution
  congr 1
  exact MemLp.toLp_congr hd hD2 (Filter.Eventually.of_forall (fun x => (congrFun hDf x).symm))

end K24.Global.SobolevClassicalDerivative
end K24SOBCLASSDERIV_Membership_Bundle


/- Inlined source K24SOBCLASSDERIV_Exact.lean; SHA256 a2beab97ba5aad625c8ff2a4d1bff2aa29760ce3b34ba648ddf6d3ce05271d6c. -/
noncomputable section K24SOBCLASSDERIV_Exact_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory TemperedDistribution Filter
open scoped NNReal ENNReal Topology SchwartzMap BoundedContinuousFunction ContDiff LineDeriv
namespace K24.Global.SobolevClassicalDerivative
open SobolevGlobal

/-- Actual first derivatives of every original continuous local coefficient
lose exactly one real Sobolev order, with the original Fourier-normalized norm
constant. Their L2 membership is proved, not assumed. -/
theorem local_directional_derivative {r : ℝ} (hr : 3 < r)
    (f : SobolevModel → ℝ) (hfc : Continuous f) (hf : LocalSobolevMem r f)
    (m : SobolevModel) :
    LocalSobolevMem (r-1) (fun x => fderiv ℝ f x m) ∧
    localSobolevENN (r-1) (fun x => fderiv ℝ f x m) ≤
      ENNReal.ofReal (2 * Real.pi * ‖m‖) * localSobolevENN r f := by
  have hdm := local_directional_mem hr f hfc hf m
  have hdd := local_directional_distribution hr f hfc hf m hdm.choose
  have hdT := SobolevDerivative.bessel_directional_derivative hf.choose_spec m
  refine ⟨hdm, ?_⟩
  simpa only [localSobolevENN, dif_pos hdm.choose, dif_pos hf.choose, hdd] using hdT.2

/-- Actual second directional derivatives at every original real source order
r > 4 have the exact two-step original Sobolev norm bound. -/
theorem local_second_directional_derivative {r : ℝ} (hr : 4 < r)
    (f : SobolevModel → ℝ) (hfc : Continuous f) (hf : LocalSobolevMem r f)
    (m n : SobolevModel) :
    LocalSobolevMem (r-2) (fun x => fderiv ℝ (fun y => fderiv ℝ f y m) x n) ∧
    localSobolevENN (r-2) (fun x => fderiv ℝ (fun y => fderiv ℝ f y m) x n) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ 2 * ‖m‖ * ‖n‖) * localSobolevENN r f := by
  have hfirst := local_directional_derivative (by linarith : 3 < r) f hfc hf m
  have hfc1 := (exists_bounded_classical_directional (by linarith : 3 < r) f hfc hf m).1
  have hdc : Continuous (fun x => fderiv ℝ f x m) :=
    (hfc1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsecond := local_directional_derivative (by linarith : 3 < r-1)
    (fun x => fderiv ℝ f x m) hdc hfirst.1 n
  rw [show r-1-1 = r-2 by ring] at hsecond
  refine ⟨hsecond.1, hsecond.2.trans ?_⟩
  calc
    _ ≤ ENNReal.ofReal (2 * Real.pi * ‖n‖) *
        (ENNReal.ofReal (2 * Real.pi * ‖m‖) * localSobolevENN r f) :=
      mul_le_mul (le_refl _) hfirst.2 bot_le bot_le
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end K24.Global.SobolevClassicalDerivative
end K24SOBCLASSDERIV_Exact_Bundle


/- Inlined source K24SOBCLASSDERIV_Partials.lean; SHA256 ba6ea844b495402e9afceb519471ba038cce6993b9247f4b01e6bf7beecd5c13. -/
noncomputable section K24SOBCLASSDERIV_Partials_Bundle

set_option autoImplicit false
open scoped NNReal ENNReal Topology ContDiff
namespace K24.Global.SobolevClassicalDerivative

/-- Actual coordinate partials of the original coefficients, in the canonical basis. -/
theorem local_partial_derivative {r : ℝ} (hr : 3 < r)
    (f : SobolevModel → ℝ) (hfc : Continuous f) (hf : LocalSobolevMem r f)
    (i : Fin 4) :
    LocalSobolevMem (r-1) (fun x => fderiv ℝ f x (basisVector i)) ∧
    localSobolevENN (r-1) (fun x => fderiv ℝ f x (basisVector i)) ≤
      ENNReal.ofReal (2 * Real.pi) * localSobolevENN r f := by
  simpa [basisVector] using local_directional_derivative hr f hfc hf (basisVector i)

/-- Actual second coordinate partials, with the original real order and norm. -/
theorem local_second_partial_derivative {r : ℝ} (hr : 4 < r)
    (f : SobolevModel → ℝ) (hfc : Continuous f) (hf : LocalSobolevMem r f)
    (i j : Fin 4) :
    LocalSobolevMem (r-2)
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (basisVector i)) x (basisVector j)) ∧
    localSobolevENN (r-2)
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (basisVector i)) x (basisVector j)) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * localSobolevENN r f := by
  simpa [basisVector] using local_second_directional_derivative hr f hfc hf
    (basisVector i) (basisVector j)

end K24.Global.SobolevClassicalDerivative
end K24SOBCLASSDERIV_Partials_Bundle


open K24.Global in
theorem solution :
    (∀ (r : ℝ), 3 < r → ∀ f : SobolevModel → ℝ,
      Continuous f → LocalSobolevMem r f → ∀ m : SobolevModel,
      LocalSobolevMem (r-1) (fun x => fderiv ℝ f x m) ∧
      localSobolevENN (r-1) (fun x => fderiv ℝ f x m) ≤
        ENNReal.ofReal (2 * Real.pi * ‖m‖) * localSobolevENN r f) ∧
    (∀ (r : ℝ), 4 < r → ∀ f : SobolevModel → ℝ,
      Continuous f → LocalSobolevMem r f → ∀ m n : SobolevModel,
      LocalSobolevMem (r-2) (fun x => fderiv ℝ (fun y => fderiv ℝ f y m) x n) ∧
      localSobolevENN (r-2) (fun x => fderiv ℝ (fun y => fderiv ℝ f y m) x n) ≤
        ENNReal.ofReal ((2 * Real.pi) ^ 2 * ‖m‖ * ‖n‖) * localSobolevENN r f) := by
  exact ⟨fun r hr f hfc hf m =>
    K24.Global.SobolevClassicalDerivative.local_directional_derivative hr f hfc hf m,
    fun r hr f hfc hf m n =>
    K24.Global.SobolevClassicalDerivative.local_second_directional_derivative hr f hfc hf m n⟩

#print axioms solution
#check @solution
