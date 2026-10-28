-- Prove2me | solution 1 for K24.Global.exactSobolevHaarProjections
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-26T04:23:26.969068+00:00
-- url     : https://prove2.me/submissions/aafbb3f0-6e0b-4409-ae06-9cc58724ad61

import Definitions.Def_K24GlobalStatement
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

set_option autoImplicit false


/- Inlined source: K24SOBPROJ_ClassicalRepresentative.lean
   SHA256 43afe72c60525d4d90e9a49648af91d81eea40c73896857ed740aabf2ad578f3. -/
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


/- Inlined source: K24SOBGLOBAL_Geometry.lean
   SHA256 a8e0fc69f6b58a4a29a0ea44008a38d2dd6a8b7272f83f698d2d0d3ed1bd62f5. -/
noncomputable section K24SOBGLOBAL_Geometry_Bundle

/- Reuses the accepted covering-tensor descent proof, submission 693fce7c,
   target 411b040b, archived as K24-existing-cover-cov2-solution.lean.txt.
   The inverse neighborhood is generalized from innerDomain to outerDomain. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.SobolevGlobalGeometry

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

theorem local_inverse (c : LocalCoverChart F) (q : M) (x : FourSpace)
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

omit [IsManifold I4 ∞ M] in
theorem pullbackCoefficients_eventually (c : LocalCoverChart F) (u : RawCov2 M)
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


omit [IsManifold I4 ∞ M] in
/-- The actual two-stage partition selects a nonzero cutoff over every base point. -/
theorem exists_nonzero_cutoff_lift (C : BoundedLocalCover M) (P : SobolevPartition C)
    (p : M) : ∃ ν : C.Index, ∃ x ∈ (C.chart ν).outerDomain,
      (C.chart ν).lift x = p ∧ P.cutoff ν x ≠ 0 := by
  obtain ⟨a, ha⟩ := P.partition.exists_pos_of_mem (Set.mem_univ p)
  have hp : p ∈ (C.cover a).innerBaseDomain :=
    P.subordinate a (subset_tsupport (P.partition a : M → ℝ) (ne_of_gt ha))
  obtain ⟨q, hq⟩ := (C.cover a).ontoBase ⟨p, (C.cover a).innerBaseSubset hp⟩
  have hqp : (C.cover a).projection q = p := congrArg Subtype.val hq
  have hqi : q ∈ (C.cover a).projection ⁻¹' (C.cover a).innerBaseDomain := by
    change (C.cover a).projection q ∈ (C.cover a).innerBaseDomain
    rw [hqp]
    exact hp
  obtain ⟨j, hj⟩ := (P.upstairsPartition a).exists_pos_of_mem hqi
  have hqs := P.upstairsSubordinate a j
    (subset_tsupport (P.upstairsPartition a j : (C.cover a).TotalSpace → ℝ) (ne_of_gt hj))
  let ν : C.Index := ⟨a, j⟩
  let x : FourSpace := (C.localChart a j).coordinate q
  have hxo : x ∈ (C.chart ν).outerDomain := hqs.2
  have hxq : (C.chart ν).liftToCover x = q := (C.localChart a j).coordinate.left_inv hqs.1
  have hxp : (C.chart ν).lift x = p := by
    change (C.cover a).projection ((C.chart ν).liftToCover x) = p
    rw [hxq, hqp]
  refine ⟨ν, x, hxo, hxp, ?_⟩
  rw [P.cutoff_eq_partition ν x hxo, hxp, hxq]
  exact mul_ne_zero (ne_of_gt ha) (ne_of_gt hj)

omit [IsManifold I4 ∞ M] in
/-- Dividing the genuine localized scalar by the nonzero cutoff recovers it locally. -/
theorem contDiffAt_of_localize (C : BoundedLocalCover M) (P : SobolevPartition C)
    (ν : C.Index) (k : ℕ) (f : FourSpace → ℝ) (x : FourSpace)
    (hx : P.cutoff ν x ≠ 0) (hf : ContDiff ℝ k (P.localize ν f)) :
    ContDiffAt ℝ k f x := by
  have hc : ContDiffAt ℝ k (P.cutoff ν) x :=
    ((P.cutoffSmooth ν).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
  have hd : ContDiffAt ℝ k (fun y => P.localize ν f y / P.cutoff ν y) x :=
    hf.contDiffAt.div hc hx
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ y in 𝓝 x, P.cutoff ν y ≠ 0 :=
    (P.cutoffSmooth ν).continuous.continuousAt.eventually_ne hx
  filter_upwards [hn] with y hy
  rw [P.localize_eq_cutoff_mul]
  exact (mul_div_cancel_left₀ (f y) hy).symm

/-- Global regularity descends from the original scalar localized coefficients. -/
theorem cov2ContDiff_of_localized (C : BoundedLocalCover M) (P : SobolevPartition C)
    (k : ℕ) (u : RawCov2 M)
    (hu : ∀ (ν : C.Index) (a : Fin 4 × Fin 4),
      ContDiff ℝ k (P.localize ν (SobolevPartition.cov2Components u ν a))) :
    Cov2ContDiff k u := by
  intro q y hy
  obtain ⟨ν, x, hx, hxy, hn⟩ := exists_nonzero_cutoff_lift C P
    ((chartAt FourSpace q).symm y)
  have hq : (C.chart ν).lift x ∈ (chartAt FourSpace q).source := by
    rw [hxy]
    exact (chartAt FourSpace q).map_target hy
  obtain ⟨S, hSx, hS, houter, heq⟩ := local_inverse (C.chart ν) q x hx hq
  have hbase : chartAt FourSpace q ((C.chart ν).lift x) = y := by
    rw [hxy]
    exact (chartAt FourSpace q).right_inv hy
  rw [hbase] at hSx hS houter heq
  have hA : ContDiffAt ℝ k ((C.chart ν).liftedCov2 u) (S y) := by
    rw [hSx]
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact contDiffAt_of_localize C P ν k
      (SobolevPartition.cov2Components u ν (i, j)) x hn (hu ν (i, j))
  have hpull := contDiffAt_pullbackCoefficients _ S y k hA hS
  have hequal := pullbackCoefficients_eventually (C.chart ν) u q S y hS houter heq
  exact (hpull.congr_of_eventuallyEq hequal.symm).contDiffWithinAt

theorem transition_fderiv (c : LocalCoverChart F) (q : M) (x : FourSpace)
    (hx : x ∈ c.outerDomain) (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    fderiv ℝ ((chartAt FourSpace q) ∘ c.lift) x =
      (mfderiv I4 I4 (chartAt FourSpace q) (c.lift x)).comp
        (c.tangentMap x).toContinuousLinearMap := by
  have hc : (c.tangentMap x).toContinuousLinearMap = mfderiv I4 I4 c.lift x :=
    c.tangentMap_eq x hx
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp x ((mdifferentiable_chart (I := I4) q).mdifferentiableAt hq)
      ((contMDiffAt_lift c x hx).mdifferentiableAt (by simp)), ← hc]

theorem liftedCov2_eq_pullbackCoefficients (c : LocalCoverChart F) (u : RawCov2 M)
    (q : M) (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    c.liftedCov2 u x =
      pullbackCoefficients (cov2InChart u q) ((chartAt FourSpace q) ∘ c.lift) x := by
  ext i j
  have hrec := congrArg
    (fun L : TangentSpace I4 (c.lift x) →L[ℝ]
      (TangentSpace I4 (c.lift x) →L[ℝ] ℝ) =>
      L (c.tangentMap x (basisVector i)) (c.tangentMap x (basisVector j)))
    (cov2_chart_recovery u q (c.lift x) hq)
  change u (c.lift x) _ _ = _
  rw [← hrec]
  simp only [cov2FromChartAt, bilinearPullback_apply, pullbackCoefficients,
    transition_fderiv c q x hx hq]
  rfl

theorem contDiffOn_liftedCov2 (c : LocalCoverChart F) (u : RawCov2 M) (k : ℕ)
    (hu : Cov2ContDiff k u) : ContDiffOn ℝ k (c.liftedCov2 u) c.outerDomain := by
  intro x hx
  let q := c.lift x
  have hq : c.lift x ∈ (chartAt FourSpace q).source := mem_chart_source FourSpace q
  have hA : ContDiffAt ℝ k (cov2InChart u q) (chartAt FourSpace q (c.lift x)) :=
    (hu q _ ((chartAt FourSpace q).map_source hq)).contDiffAt
      ((chartAt FourSpace q).open_target.mem_nhds ((chartAt FourSpace q).map_source hq))
  have hT := contDiffAt_pullbackCoefficients (cov2InChart u q)
    ((chartAt FourSpace q) ∘ c.lift) x k hA (transition_smooth c q x hx hq)
  apply (hT.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hsource : ∀ᶠ z in 𝓝 x, c.lift z ∈ (chartAt FourSpace q).source :=
    (contMDiffAt_lift c x hx).continuousAt.tendsto
      ((chartAt FourSpace q).open_source.mem_nhds hq)
  filter_upwards [c.outerOpen.mem_nhds hx, hsource] with z hz hqz
  exact liftedCov2_eq_pullbackCoefficients c u q z hz hqz

omit [IsManifold I4 ∞ M] in
theorem contDiff_localize {C : BoundedLocalCover M} (P : SobolevPartition C)
    (ν : C.Index) (f : FourSpace → ℝ) (k : ℕ)
    (hf : ContDiffOn ℝ k f (C.chart ν).outerDomain) :
    ContDiff ℝ k (P.localize ν f) := by
  rw [P.localize_eq_cutoff_mul]
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport (P.cutoff ν)
  · have hxo := P.cutoffSupport ν hx
    exact ((P.cutoffSmooth ν).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt.mul
        ((hf x hxo).contDiffAt ((C.chart ν).outerOpen.mem_nhds hxo))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

theorem contDiff_localize_cov2Components {C : BoundedLocalCover M}
    (P : SobolevPartition C) (u : RawCov2 M) (k : ℕ) (hu : Cov2ContDiff k u)
    (ν : C.Index) (a : Fin 4 × Fin 4) :
    ContDiff ℝ k (P.localize ν (SobolevPartition.cov2Components (C := C) u ν a)) := by
  apply contDiff_localize P ν _ k
  exact contDiffOn_pi.mp (contDiffOn_pi.mp
    (contDiffOn_liftedCov2 (C.chart ν) u k hu) a.1) a.2

/-- Exact geometric equivalence for the original partition, at every finite order. -/
theorem cov2ContDiff_iff_localized (C : BoundedLocalCover M) (P : SobolevPartition C)
    (k : ℕ) (u : RawCov2 M) :
    Cov2ContDiff k u ↔ ∀ (ν : C.Index) (a : Fin 4 × Fin 4),
      ContDiff ℝ k (P.localize ν (SobolevPartition.cov2Components u ν a)) :=
  ⟨fun hu ν a => contDiff_localize_cov2Components P u k hu ν a,
    cov2ContDiff_of_localized C P k u⟩

end K24.Global.SobolevGlobalGeometry


end K24SOBGLOBAL_Geometry_Bundle


/- Inlined source: K24SOBPROJ_CovectorGeometry.lean
   SHA256 010b03ce1ed1d2f444e48ff13708d0263b15760b164fd97d4ed1307f285773d0. -/
noncomputable section K24SOBPROJ_CovectorGeometry_Bundle

/- Covector adaptation of the inspected tensor geometry proof frozen at
   a2e04619d5bcc1e1e13cfe6d4ff1d33bb5ba3b28. The original partition,
   actual chart derivatives, and outerDomain local inverse are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
open scoped Manifold ContDiff BigOperators NNReal Matrix.Norms.Elementwise Topology
open Filter

namespace K24.Global.SobolevProjectionCovector
open SobolevGlobalGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {F : LocalFiniteCover M}

lemma coefficientsToCovector_apply (a : Fin 4 → ℝ) (v : FourSpace) :
    coefficientsToCovector a v = ∑ i : Fin 4, a i * v i := by
  simp [coefficientsToCovector, coordProj]

def pullbackCoefficients (A : FourSpace → Fin 4 → ℝ) (S : FourSpace → FourSpace)
    (y : FourSpace) : Fin 4 → ℝ :=
  fun i => coefficientsToCovector (A (S y)) (fderiv ℝ S y (basisVector i))

theorem contDiffAt_pullbackCoefficients (A : FourSpace → Fin 4 → ℝ)
    (S : FourSpace → FourSpace) (y : FourSpace) (k : ℕ)
    (hA : ContDiffAt ℝ k A (S y)) (hS : ContDiffAt ℝ ∞ S y) :
    ContDiffAt ℝ k (pullbackCoefficients A S) y := by
  have hT : ContDiffAt ℝ k (fderiv ℝ S) y :=
    hS.fderiv_right (by exact_mod_cast (le_top : (k : ℕ∞) + 1 ≤ ⊤))
  have hAS : ContDiffAt ℝ k (A ∘ S) y :=
    hA.comp y (hS.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
  have hV (i a : Fin 4) :
      ContDiffAt ℝ k (fun z => (fderiv ℝ S z (basisVector i)) a) y :=
    (coordProj a).contDiff.contDiffAt.comp y (hT.clm_apply contDiffAt_const)
  apply contDiffAt_pi.mpr
  intro i
  simp only [pullbackCoefficients, coefficientsToCovector_apply]
  apply ContDiffAt.sum
  intro a _
  exact (contDiffAt_pi.mp hAS a).mul (hV i a)

omit [IsManifold I4 ∞ M] in
theorem pullbackCoefficients_eventually (c : LocalCoverChart F) (u : RawCovector M)
    (q : M) (S : FourSpace → FourSpace) (y : FourSpace)
    (hS : ContDiffAt ℝ ∞ S y)
    (houter : ∀ᶠ z in 𝓝 y, S z ∈ c.outerDomain)
    (heq : c.lift ∘ S =ᶠ[𝓝 y] (chartAt FourSpace q).symm) :
    pullbackCoefficients (c.liftedCovector u) S =ᶠ[𝓝 y] covectorInChart u q := by
  have hS1 : ContDiffAt ℝ 1 S y := hS.of_le (by simp)
  have hSnear := hS1.eventually (by simp)
  filter_upwards [houter, heq.eventuallyEq_nhds, hSnear] with z hz heqz hSz
  have hDL := (contMDiffAt_lift c (S z) hz).mdifferentiableAt (by simp)
  have hDS := (hSz.differentiableAt (by simp)).mdifferentiableAt
  have hder := heqz.mfderiv_eq (I := I4) (I' := I4)
  rw [mfderiv_comp z hDL hDS, mfderiv_eq_fderiv] at hder
  have hc : (c.tangentMap (S z)).toContinuousLinearMap =
      mfderiv I4 I4 c.lift (S z) := c.tangentMap_eq (S z) hz
  rw [← hc] at hder
  have hvec (i : Fin 4) : c.tangentMap (S z) (fderiv ℝ S z (basisVector i)) =
      mfderiv I4 I4 (chartAt FourSpace q).symm z (basisVector i) :=
    congrArg (fun D : FourSpace →L[ℝ] FourSpace => D (basisVector i)) hder
  have hcoeff := coefficientsToCovector_recover
    ((u (c.lift (S z))).comp (c.tangentMap (S z)).toContinuousLinearMap)
  change coefficientsToCovector (c.liftedCovector u (S z)) = _ at hcoeff
  ext i
  change coefficientsToCovector (c.liftedCovector u (S z))
    (fderiv ℝ S z (basisVector i)) = _
  rw [hcoeff]
  change u (c.lift (S z)) (c.tangentMap (S z) (fderiv ℝ S z (basisVector i))) = _
  rw [hvec i]
  change u (c.lift (S z)) _ = u ((chartAt FourSpace q).symm z) _
  rw [show c.lift (S z) = (chartAt FourSpace q).symm z from heqz.self_of_nhds]

/-- Native finite regularity descends from the genuine localized covector coefficients. -/
theorem covectorContDiff_of_localized (C : BoundedLocalCover M) (P : SobolevPartition C)
    (k : ℕ) (u : RawCovector M)
    (hu : ∀ (ν : C.Index) (a : Fin 4),
      ContDiff ℝ k (P.localize ν (SobolevPartition.covectorComponents u ν a))) :
    CovectorContDiff k u := by
  intro q y hy
  obtain ⟨ν, x, hx, hxy, hn⟩ := exists_nonzero_cutoff_lift C P
    ((chartAt FourSpace q).symm y)
  have hq : (C.chart ν).lift x ∈ (chartAt FourSpace q).source := by
    rw [hxy]
    exact (chartAt FourSpace q).map_target hy
  obtain ⟨S, hSx, hS, houter, heq⟩ := local_inverse (C.chart ν) q x hx hq
  have hbase : chartAt FourSpace q ((C.chart ν).lift x) = y := by
    rw [hxy]
    exact (chartAt FourSpace q).right_inv hy
  rw [hbase] at hSx hS houter heq
  have hA : ContDiffAt ℝ k ((C.chart ν).liftedCovector u) (S y) := by
    rw [hSx]
    apply contDiffAt_pi.mpr
    intro i
    exact contDiffAt_of_localize C P ν k
      (SobolevPartition.covectorComponents u ν i) x hn (hu ν i)
  have hpull := contDiffAt_pullbackCoefficients _ S y k hA hS
  have hequal := pullbackCoefficients_eventually (C.chart ν) u q S y hS houter heq
  exact (hpull.congr_of_eventuallyEq hequal.symm).contDiffWithinAt

theorem liftedCovector_eq_pullbackCoefficients (c : LocalCoverChart F) (u : RawCovector M)
    (q : M) (x : FourSpace) (hx : x ∈ c.outerDomain)
    (hq : c.lift x ∈ (chartAt FourSpace q).source) :
    c.liftedCovector u x =
      pullbackCoefficients (covectorInChart u q) ((chartAt FourSpace q) ∘ c.lift) x := by
  ext i
  have hrec := congrArg
    (fun L : TangentSpace I4 (c.lift x) →L[ℝ] ℝ => L (c.tangentMap x (basisVector i)))
    (covector_chart_recovery u q (c.lift x) hq)
  change u (c.lift x) _ = _
  rw [← hrec]
  simp only [covectorFromChartAt, ContinuousLinearMap.comp_apply, pullbackCoefficients,
    transition_fderiv c q x hx hq]
  rfl

theorem contDiffOn_liftedCovector (c : LocalCoverChart F) (u : RawCovector M) (k : ℕ)
    (hu : CovectorContDiff k u) : ContDiffOn ℝ k (c.liftedCovector u) c.outerDomain := by
  intro x hx
  let q := c.lift x
  have hq : c.lift x ∈ (chartAt FourSpace q).source := mem_chart_source FourSpace q
  have hA : ContDiffAt ℝ k (covectorInChart u q) (chartAt FourSpace q (c.lift x)) :=
    (hu q _ ((chartAt FourSpace q).map_source hq)).contDiffAt
      ((chartAt FourSpace q).open_target.mem_nhds ((chartAt FourSpace q).map_source hq))
  have hT := contDiffAt_pullbackCoefficients (covectorInChart u q)
    ((chartAt FourSpace q) ∘ c.lift) x k hA (transition_smooth c q x hx hq)
  apply (hT.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hsource : ∀ᶠ z in 𝓝 x, c.lift z ∈ (chartAt FourSpace q).source :=
    (contMDiffAt_lift c x hx).continuousAt.tendsto
      ((chartAt FourSpace q).open_source.mem_nhds hq)
  filter_upwards [c.outerOpen.mem_nhds hx, hsource] with z hz hqz
  exact liftedCovector_eq_pullbackCoefficients c u q z hz hqz

theorem contDiff_localize_covectorComponents {C : BoundedLocalCover M}
    (P : SobolevPartition C) (u : RawCovector M) (k : ℕ) (hu : CovectorContDiff k u)
    (ν : C.Index) (a : Fin 4) :
    ContDiff ℝ k (P.localize ν (SobolevPartition.covectorComponents (C := C) u ν a)) := by
  apply contDiff_localize P ν _ k
  exact contDiffOn_pi.mp (contDiffOn_liftedCovector (C.chart ν) u k hu) a

/-- Exact equivalence for the original covector coefficients and partition, at every finite order. -/
theorem covectorContDiff_iff_localized (C : BoundedLocalCover M) (P : SobolevPartition C)
    (k : ℕ) (u : RawCovector M) :
    CovectorContDiff k u ↔ ∀ (ν : C.Index) (a : Fin 4),
      ContDiff ℝ k (P.localize ν (SobolevPartition.covectorComponents u ν a)) :=
  ⟨fun hu ν a => contDiff_localize_covectorComponents P u k hu ν a,
    covectorContDiff_of_localized C P k u⟩

end K24.Global.SobolevProjectionCovector
end K24SOBPROJ_CovectorGeometry_Bundle


/- Inlined source: K24SOB_ExactBesselBanach.lean
   SHA256 c5496787dd97d5401abfacb05060575148125346b889d1da5de5d33a28cdccae. -/
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


/- Inlined source: K24SOB_ContinuousRepresentative.lean
   SHA256 58d5f93deed312b24a76bd464384af09f667f0a8af4a32cbfa5a8866793c413b. -/
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


/- Inlined source: K24SOBGLOBAL_Local.lean
   SHA256 997674688a0d43be5056ea4d5b982b2b4326d9741136f3941993ddbe39032111. -/
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


/- Inlined source: K24SOBGLOBAL_LocalNorm.lean
   SHA256 163ed437c1782920f00a9c8c66b913a0fc5ca9c3c7f6841e585dad7ee6da390d. -/
noncomputable section K24SOBGLOBAL_LocalNorm_Bundle

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
end K24SOBGLOBAL_LocalNorm_Bundle


/- Inlined source: K24SOBGLOBAL_NormLaws.lean
   SHA256 4fc3b0ed978e9b80204ebbaa4ce73e672ab20b23d3ee4c2d18f0e65346b90e4b. -/
noncomputable section K24SOBGLOBAL_NormLaws_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

open scoped Manifold ContDiff BigOperators NNReal ENNReal Topology

namespace K24.Global.SobolevGlobal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable {C : BoundedLocalCover M} (P : SobolevPartition C)
variable {κ : Type*} [Fintype κ]

@[simp] theorem localize_zero (ν : C.Index) : P.localize ν 0 = 0 := by
  rw [P.localize_eq_cutoff_mul]
  simp

theorem localize_add (ν : C.Index) (f g : FourSpace → ℝ) :
    P.localize ν (f + g) = P.localize ν f + P.localize ν g := by
  simp only [P.localize_eq_cutoff_mul, mul_add]

theorem localize_sub (ν : C.Index) (f g : FourSpace → ℝ) :
    P.localize ν (f - g) = P.localize ν f - P.localize ν g := by
  simp only [P.localize_eq_cutoff_mul, mul_sub]

theorem localize_smul (ν : C.Index) (c : ℝ) (f : FourSpace → ℝ) :
    P.localize ν (c • f) = c • P.localize ν f := by
  simp only [P.localize_eq_cutoff_mul]
  ext x
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem cov2Components_zero :
    SobolevPartition.cov2Components (C := C) (0 : RawCov2 M) = 0 := rfl

theorem cov2Components_add (u v : RawCov2 M) :
    SobolevPartition.cov2Components (C := C) (u + v) =
      SobolevPartition.cov2Components u + SobolevPartition.cov2Components v := rfl

theorem cov2Components_sub (u v : RawCov2 M) :
    SobolevPartition.cov2Components (C := C) (u - v) =
      SobolevPartition.cov2Components u - SobolevPartition.cov2Components v := rfl

theorem cov2Components_smul (c : ℝ) (u : RawCov2 M) :
    SobolevPartition.cov2Components (C := C) (c • u) =
      c • SobolevPartition.cov2Components u := rfl

@[simp] theorem componentSobolevENorm_zero (s : ℝ) :
    P.componentSobolevENorm s (0 : C.Index → κ → FourSpace → ℝ) = 0 := by
  simp [SobolevPartition.componentSobolevENorm, SobolevPartition.componentSobolevSquare,
    localize_zero]

/-- Minkowski for an arbitrary family of extended nonnegative coordinates. -/
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

theorem componentSobolevENorm_add_le (s : ℝ)
    (f g : C.Index → κ → FourSpace → ℝ)
    (hf : ∀ ν a, LocalSobolevMem s (P.localize ν (f ν a)))
    (hg : ∀ ν a, LocalSobolevMem s (P.localize ν (g ν a))) :
    P.componentSobolevENorm s (f + g) ≤
      P.componentSobolevENorm s f + P.componentSobolevENorm s g := by
  unfold SobolevPartition.componentSobolevENorm SobolevPartition.componentSobolevSquare
  calc
    _ ≤ (∑' ν, ∑ a, (localSobolevENN s (P.localize ν (f ν a)) +
          localSobolevENN s (P.localize ν (g ν a))) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      apply ENNReal.tsum_le_tsum
      intro ν
      apply Finset.sum_le_sum
      intro a _
      apply pow_le_pow_left'
      change localSobolevENN s (P.localize ν (f ν a + g ν a)) ≤ _
      rw [localize_add]
      exact localSobolevENN_add_le (hf ν a) (hg ν a)
    _ ≤ _ := by
      simpa only [ENNReal.tsum_prod', tsum_fintype] using
        (enorm_l2_add_le
          (fun p : C.Index × κ => localSobolevENN s (P.localize p.1 (f p.1 p.2)))
          (fun p : C.Index × κ => localSobolevENN s (P.localize p.1 (g p.1 p.2))))

theorem componentSobolevENorm_smul (s : ℝ) (c : ℝ)
    (f : C.Index → κ → FourSpace → ℝ)
    (hf : ∀ ν a, LocalSobolevMem s (P.localize ν (f ν a))) :
    P.componentSobolevENorm s (c • f) =
      ENNReal.ofReal |c| * P.componentSobolevENorm s f := by
  unfold SobolevPartition.componentSobolevENorm SobolevPartition.componentSobolevSquare
  simp only [Pi.smul_apply]
  simp_rw [localize_smul, localSobolevENN_smul (hf _ _) c]
  simpa only [ENNReal.tsum_prod', tsum_fintype] using
    (enorm_l2_mul (ENNReal.ofReal |c|)
      (fun p : C.Index × κ => localSobolevENN s (P.localize p.1 (f p.1 p.2))))

@[simp] theorem cov2SobolevENorm_zero (s : ℝ) : P.cov2SobolevENorm s 0 = 0 := by
  unfold SobolevPartition.cov2SobolevENorm
  rw [cov2Components_zero, componentSobolevENorm_zero]

theorem cov2SobolevENorm_add_le (s : ℝ) (u v : RawCov2 M)
    (hu : P.cov2SobolevENorm s u < ⊤) (hv : P.cov2SobolevENorm s v < ⊤) :
    P.cov2SobolevENorm s (u + v) ≤ P.cov2SobolevENorm s u + P.cov2SobolevENorm s v := by
  unfold SobolevPartition.cov2SobolevENorm at *
  rw [cov2Components_add]
  exact componentSobolevENorm_add_le P s _ _
    (P.local_mem_of_component_finite hu) (P.local_mem_of_component_finite hv)

theorem cov2SobolevENorm_smul (s : ℝ) (c : ℝ) (u : RawCov2 M)
    (hu : P.cov2SobolevENorm s u < ⊤) :
    P.cov2SobolevENorm s (c • u) = ENNReal.ofReal |c| * P.cov2SobolevENorm s u := by
  unfold SobolevPartition.cov2SobolevENorm at *
  rw [cov2Components_smul]
  exact componentSobolevENorm_smul P s c _ (P.local_mem_of_component_finite hu)

theorem rawCov2_neg_one_smul (u : RawCov2 M) : (-1 : ℝ) • u = -u := by
  funext p
  ext a b
  change (-1 : ℝ) * u p a b = -(u p a b)
  ring

theorem rawCov2_sub_eq_add_neg (u v : RawCov2 M) : u - v = u + -v := by
  funext p
  ext a b
  change u p a b - v p a b = u p a b + -(v p a b)
  ring

theorem cov2SobolevENorm_neg (s : ℝ) (u : RawCov2 M)
    (hu : P.cov2SobolevENorm s u < ⊤) :
    P.cov2SobolevENorm s (-u) = P.cov2SobolevENorm s u := by
  simpa only [rawCov2_neg_one_smul, abs_neg, abs_one, ENNReal.ofReal_one, one_mul] using
    cov2SobolevENorm_smul P s (-1) u hu

theorem cov2SobolevENorm_sub_le (s : ℝ) (u v : RawCov2 M)
    (hu : P.cov2SobolevENorm s u < ⊤) (hv : P.cov2SobolevENorm s v < ⊤) :
    P.cov2SobolevENorm s (u - v) ≤ P.cov2SobolevENorm s u + P.cov2SobolevENorm s v := by
  have hvn : P.cov2SobolevENorm s (-v) < ⊤ := by
    rw [cov2SobolevENorm_neg P s v hv]
    exact hv
  simpa only [rawCov2_sub_eq_add_neg, cov2SobolevENorm_neg P s v hv] using
    cov2SobolevENorm_add_le P s u (-v) hu hvn

variable [IsManifold I4 ∞ M]

include P in
theorem cov2ContDiff_zero (k : ℕ) : Cov2ContDiff k (0 : RawCov2 M) := by
  apply SobolevGlobalGeometry.cov2ContDiff_of_localized C P k 0
  intro ν a
  simp only [cov2Components_zero, Pi.zero_apply, localize_zero]
  exact contDiff_const

include P in
theorem cov2ContDiff_add (k : ℕ) (u v : RawCov2 M)
    (hu : Cov2ContDiff k u) (hv : Cov2ContDiff k v) : Cov2ContDiff k (u + v) := by
  apply SobolevGlobalGeometry.cov2ContDiff_of_localized C P k (u + v)
  intro ν a
  rw [cov2Components_add]
  change ContDiff ℝ k (P.localize ν (SobolevPartition.cov2Components u ν a +
    SobolevPartition.cov2Components v ν a))
  rw [localize_add]
  exact (SobolevGlobalGeometry.contDiff_localize_cov2Components P u k hu ν a).add
    (SobolevGlobalGeometry.contDiff_localize_cov2Components P v k hv ν a)

include P in
theorem cov2ContDiff_smul (k : ℕ) (c : ℝ) (u : RawCov2 M)
    (hu : Cov2ContDiff k u) : Cov2ContDiff k (c • u) := by
  apply SobolevGlobalGeometry.cov2ContDiff_of_localized C P k (c • u)
  intro ν a
  rw [cov2Components_smul]
  change ContDiff ℝ k (P.localize ν (c • SobolevPartition.cov2Components u ν a))
  rw [localize_smul]
  exact (SobolevGlobalGeometry.contDiff_localize_cov2Components P u k hu ν a).const_smul c

theorem tensorSobolevSpace_zero_mem (k : ℕ) (s : ℝ) :
    (0 : RawCov2 M) ∈ tensorSobolevSpace P k s := by
  refine ⟨?_, cov2ContDiff_zero P k, ?_⟩
  · intro p v w
    rfl
  · simp

theorem tensorSobolevSpace_add_mem (k : ℕ) (s : ℝ) (u v : RawCov2 M)
    (hu : u ∈ tensorSobolevSpace P k s) (hv : v ∈ tensorSobolevSpace P k s) :
    u + v ∈ tensorSobolevSpace P k s := by
  refine ⟨?_, cov2ContDiff_add P k u v hu.2.1 hv.2.1, ?_⟩
  · intro p a b
    change u p a b + v p a b = u p b a + v p b a
    rw [hu.1 p a b, hv.1 p a b]
  · exact lt_of_le_of_lt (cov2SobolevENorm_add_le P s u v hu.2.2 hv.2.2)
      (ENNReal.add_lt_top.mpr ⟨hu.2.2, hv.2.2⟩)

theorem tensorSobolevSpace_smul_mem (k : ℕ) (s : ℝ) (c : ℝ) (u : RawCov2 M)
    (hu : u ∈ tensorSobolevSpace P k s) : c • u ∈ tensorSobolevSpace P k s := by
  refine ⟨?_, cov2ContDiff_smul P k c u hu.2.1, ?_⟩
  · intro p a b
    change c * u p a b = c * u p b a
    rw [hu.1 p a b]
  · rw [cov2SobolevENorm_smul P s c u hu.2.2]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.2.2

theorem tensorSobolevSpace_neg_mem (k : ℕ) (s : ℝ) (u : RawCov2 M)
    (hu : u ∈ tensorSobolevSpace P k s) : -u ∈ tensorSobolevSpace P k s := by
  simpa only [rawCov2_neg_one_smul] using tensorSobolevSpace_smul_mem P k s (-1) u hu

theorem tensorSobolevSpace_sub_mem (k : ℕ) (s : ℝ) (u v : RawCov2 M)
    (hu : u ∈ tensorSobolevSpace P k s) (hv : v ∈ tensorSobolevSpace P k s) :
    u - v ∈ tensorSobolevSpace P k s := by
  simpa only [rawCov2_sub_eq_add_neg] using
    tensorSobolevSpace_add_mem P k s u (-v) hu (tensorSobolevSpace_neg_mem P k s v hv)

end K24.Global.SobolevGlobal


end K24SOBGLOBAL_NormLaws_Bundle


/- Inlined source: K24SOBPROJ_CovectorNormLaws.lean
   SHA256 ed6e56eaf263aecd3a3ebf4ce5df5f405a2dfd9b509185a331331fe785e14801. -/
noncomputable section K24SOBPROJ_CovectorNormLaws_Bundle

/- Covector adaptation of the frozen original-norm tensor linear laws.
   Every norm is the original SobolevPartition.covectorSobolevENorm. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff BigOperators NNReal ENNReal Topology
namespace K24.Global.SobolevProjectionCovector
open SobolevGlobal
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable {C : BoundedLocalCover M} (P : SobolevPartition C)

@[simp] theorem covectorComponents_zero :
    SobolevPartition.covectorComponents (C := C) (0 : RawCovector M) = 0 := rfl

theorem covectorComponents_add (u v : RawCovector M) :
    SobolevPartition.covectorComponents (C := C) (u + v) =
      SobolevPartition.covectorComponents u + SobolevPartition.covectorComponents v := rfl

theorem covectorComponents_sub (u v : RawCovector M) :
    SobolevPartition.covectorComponents (C := C) (u - v) =
      SobolevPartition.covectorComponents u - SobolevPartition.covectorComponents v := rfl

theorem covectorComponents_smul (c : ℝ) (u : RawCovector M) :
    SobolevPartition.covectorComponents (C := C) (c • u) =
      c • SobolevPartition.covectorComponents u := rfl

@[simp] theorem covectorSobolevENorm_zero (s : ℝ) : P.covectorSobolevENorm s 0 = 0 := by
  unfold SobolevPartition.covectorSobolevENorm
  rw [covectorComponents_zero, componentSobolevENorm_zero]

theorem covectorSobolevENorm_add_le (s : ℝ) (u v : RawCovector M)
    (hu : P.covectorSobolevENorm s u < ⊤) (hv : P.covectorSobolevENorm s v < ⊤) :
    P.covectorSobolevENorm s (u + v) ≤ P.covectorSobolevENorm s u + P.covectorSobolevENorm s v := by
  unfold SobolevPartition.covectorSobolevENorm at *
  rw [covectorComponents_add]
  exact componentSobolevENorm_add_le P s _ _
    (P.local_mem_of_component_finite hu) (P.local_mem_of_component_finite hv)

theorem covectorSobolevENorm_smul (s : ℝ) (c : ℝ) (u : RawCovector M)
    (hu : P.covectorSobolevENorm s u < ⊤) :
    P.covectorSobolevENorm s (c • u) = ENNReal.ofReal |c| * P.covectorSobolevENorm s u := by
  unfold SobolevPartition.covectorSobolevENorm at *
  rw [covectorComponents_smul]
  exact componentSobolevENorm_smul P s c _ (P.local_mem_of_component_finite hu)

theorem rawCovector_neg_one_smul (u : RawCovector M) : (-1 : ℝ) • u = -u := by
  funext p
  ext a
  change (-1 : ℝ) * u p a = -(u p a)
  ring

theorem rawCovector_sub_eq_add_neg (u v : RawCovector M) : u - v = u + -v := by
  funext p
  ext a
  change u p a - v p a = u p a + -(v p a)
  ring

theorem covectorSobolevENorm_neg (s : ℝ) (u : RawCovector M)
    (hu : P.covectorSobolevENorm s u < ⊤) :
    P.covectorSobolevENorm s (-u) = P.covectorSobolevENorm s u := by
  simpa only [rawCovector_neg_one_smul, abs_neg, abs_one, ENNReal.ofReal_one, one_mul] using
    covectorSobolevENorm_smul P s (-1) u hu

theorem covectorSobolevENorm_sub_le (s : ℝ) (u v : RawCovector M)
    (hu : P.covectorSobolevENorm s u < ⊤) (hv : P.covectorSobolevENorm s v < ⊤) :
    P.covectorSobolevENorm s (u - v) ≤ P.covectorSobolevENorm s u + P.covectorSobolevENorm s v := by
  have hvn : P.covectorSobolevENorm s (-v) < ⊤ := by
    rw [covectorSobolevENorm_neg P s v hv]
    exact hv
  simpa only [rawCovector_sub_eq_add_neg, covectorSobolevENorm_neg P s v hv] using
    covectorSobolevENorm_add_le P s u (-v) hu hvn

variable [IsManifold I4 ∞ M]

include P in
theorem covectorContDiff_sub (k : ℕ) (u v : RawCovector M)
    (hu : CovectorContDiff k u) (hv : CovectorContDiff k v) :
    CovectorContDiff k (u - v) := by
  apply covectorContDiff_of_localized C P k (u - v)
  intro ν a
  rw [covectorComponents_sub]
  change ContDiff ℝ k (P.localize ν (SobolevPartition.covectorComponents u ν a -
    SobolevPartition.covectorComponents v ν a))
  rw [localize_sub]
  exact (contDiff_localize_covectorComponents P u k hu ν a).sub
    (contDiff_localize_covectorComponents P v k hv ν a)

theorem covectorSobolev_sub (k : ℕ) (s : ℝ) (u v : RawCovector M)
    (hu : P.CovectorSobolev k s u) (hv : P.CovectorSobolev k s v) :
    P.CovectorSobolev k s (u - v) := by
  refine ⟨covectorContDiff_sub P k u v hu.1 hv.1, ?_⟩
  exact lt_of_le_of_lt (covectorSobolevENorm_sub_le P s u v hu.2 hv.2)
    (ENNReal.add_lt_top.mpr ⟨hu.2, hv.2⟩)

end K24.Global.SobolevProjectionCovector
end K24SOBPROJ_CovectorNormLaws_Bundle


/- Inlined source: K24SOBPERP_Haar.lean
   SHA256 d8ce1bccf750d711b94583869129eb7b16d574baa9aea3ebf6469e541606be89. -/
noncomputable section K24SOBPERP_Haar_Bundle

/- Selective reuse from inspected HolderPERPAll source 7bb2fa1c57a44839e328e75f211222926999affd
(evidence ab18f17): genuine pointwise Haar identities, smooth tangent action,
and native tensor bundle-evaluation continuity. Original HP0/CONT attribution
is preserved in the final report. No Holder norm assumption is used here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16
open Filter MeasureTheory Bundle
open scoped NNReal ENNReal Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace K24.Global.SobolevPerpHaar
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

lemma matrixToBilinear_apply (a : Mat4) (v w : FourSpace) :
    matrixToBilinear a v w = ∑ i : Fin 4, ∑ j : Fin 4, v i * (a i j * w j) := by
  simp [matrixToBilinear, coordProj]

lemma integrable_cov2_coordinates (a : Circle → Mat4)
    (ha : ∀ i j, Integrable (fun t => a t i j) circleHaar) (v w : FourSpace) :
    Integrable (fun t => matrixToBilinear (a t) v w) circleHaar := by
  simp_rw [matrixToBilinear_apply]
  exact integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => ((ha i j).mul_const _).const_mul _))

lemma integral_cov2_coordinates (a : Circle → Mat4)
    (ha : ∀ i j, Integrable (fun t => a t i j) circleHaar) (v w : FourSpace) :
    matrixToBilinear (fun i j => ∫ t, a t i j ∂circleHaar) v w =
      ∫ t, matrixToBilinear (a t) v w ∂circleHaar := by
  simp_rw [matrixToBilinear_apply]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => ((ha i j).mul_const _).const_mul _))]
  congr 1
  funext i
  rw [integral_finsetSum _ (fun j _ => ((ha i j).mul_const _).const_mul _)]
  simp_rw [integral_const_mul, integral_mul_const]

lemma cov2_chart_eval (u : RawCov2 M) (p : M) (v w : TangentSpace I4 p) :
    matrixToBilinear (cov2InChart u p (chartAt FourSpace p p))
      (mfderiv I4 I4 (chartAt FourSpace p) p v)
      (mfderiv I4 I4 (chartAt FourSpace p) p w) = u p v w := by
  have h := cov2_chart_recovery u p p (mem_chart_source FourSpace p)
  exact congrArg (fun L => L v w) h

lemma cov2_orbit_integrable (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (p : M) (v w : TangentSpace I4 p) :
    Integrable (fun t => actionPullbackCov2 rho t u p v w) circleHaar := by
  have h := integrable_cov2_coordinates
    (fun t => cov2InChart (actionPullbackCov2 rho t u) p (chartAt FourSpace p p))
    (hu p _ (mem_chart_target FourSpace p))
    (mfderiv I4 I4 (chartAt FourSpace p) p v)
    (mfderiv I4 I4 (chartAt FourSpace p) p w)
  simpa only [cov2_chart_eval] using h

lemma cov2Pi0_apply (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (p : M) (v w : TangentSpace I4 p) :
    cov2Pi0 rho u p v w = ∫ t, actionPullbackCov2 rho t u p v w ∂circleHaar := by
  change matrixToBilinear
    (fun i j => ∫ t, cov2InChart (actionPullbackCov2 rho t u) p
      (chartAt FourSpace p p) i j ∂circleHaar)
      (mfderiv I4 I4 (chartAt FourSpace p) p v)
      (mfderiv I4 I4 (chartAt FourSpace p) p w) = _
  rw [integral_cov2_coordinates _ (hu p _ (mem_chart_target FourSpace p))]
  simp only [cov2_chart_eval]

lemma cov2_integrable_sub (rho : CircleAction M) (u z : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (hz : Cov2HaarIntegrable rho z) :
    Cov2HaarIntegrable rho (u - z) := by
  intro c x hx i j
  exact (hu c x hx i j).sub (hz c x hx i j)

lemma cov2Pi0_sub (rho : CircleAction M) (u z : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (hz : Cov2HaarIntegrable rho z) :
    cov2Pi0 rho (u - z) = cov2Pi0 rho u - cov2Pi0 rho z := by
  funext p
  ext v w
  rw [cov2Pi0_apply rho (u - z) (cov2_integrable_sub rho u z hu hz)]
  change (∫ t, actionPullbackCov2 rho t u p v w - actionPullbackCov2 rho t z p v w
    ∂circleHaar) = cov2Pi0 rho u p v w - cov2Pi0 rho z p v w
  rw [integral_sub (cov2_orbit_integrable rho u hu p v w)
    (cov2_orbit_integrable rho z hz p v w), cov2Pi0_apply rho u hu,
    cov2Pi0_apply rho z hz]

/-- Pointwise projection and sector laws for the canonical tensor Haar average. -/

abbrev TangentPair (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] :=
  {q : TangentBundle I4 M × TangentBundle I4 M // q.1.proj = q.2.proj}

/-- Continuity of bilinear evaluation on pairs of vectors in the same tangent fiber. -/

def Cov2EvaluationContinuous (u : RawCov2 M) : Prop :=
  Continuous (fun q : TangentPair M => u q.val.1.proj q.val.1.2 q.val.2.2)

/-- Joint continuity of the actual tangent lift of the smooth circle action. -/

lemma action_tangent_continuous (rho : CircleAction M) :
    Continuous (fun q : Circle × TangentBundle I4 M =>
      (⟨rho.act q.1 q.2.proj, mfderiv I4 I4 (rho.act q.1) q.2.proj q.2.2⟩ :
        TangentBundle I4 M)) := by
  have hz : Continuous (fun t : Circle => (⟨t, 0⟩ : TangentBundle (𝓡 1) Circle)) :=
    Bundle.Trivialization.continuous_zeroSection ℝ
  have hi := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓡 1) (M := Circle) (I' := I4) (M' := M) (n := 0)).continuous.comp
      ((hz.comp continuous_fst).prodMk (continuous_snd :
        Continuous (Prod.snd : Circle × TangentBundle I4 M → TangentBundle I4 M)))
  have h := (rho.smooth.continuous_tangentMap (by simp)).comp hi
  convert h using 1
  funext ⟨t, p, v⟩
  change (⟨rho.act t p, mfderiv I4 I4 (rho.act t) p v⟩ : TangentBundle I4 M) =
    ⟨rho.act t p, mfderiv ((𝓡 1).prod I4) I4
      (fun q : Circle × M => rho.act q.1 q.2) (t, p) (0, v)⟩
  congr 1
  have hd := mfderiv_comp (I := I4) (I' := (𝓡 1).prod I4) (I'' := I4) p
    (rho.smooth.mdifferentiable (by simp) (t, p))
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  rw [mfderiv_prod_right] at hd
  exact congrArg (fun L => L v) hd

lemma action_tangent_orbit_continuous (rho : CircleAction M) (p : M)
    (v : TangentSpace I4 p) :
    Continuous (fun t : Circle => (⟨rho.act t p, mfderiv I4 I4 (rho.act t) p v⟩ :
      TangentBundle I4 M)) :=
  (action_tangent_continuous rho).comp
    (continuous_id.prodMk (continuous_const (y := (⟨p, v⟩ : TangentBundle I4 M))))

lemma cov2_orbit_continuous (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2EvaluationContinuous u) (p : M) (v w : TangentSpace I4 p) :
    Continuous (fun t : Circle => actionPullbackCov2 rho t u p v w) := by
  have h := (action_tangent_orbit_continuous rho p v).prodMk
    (action_tangent_orbit_continuous rho p w)
  exact hu.comp (h.subtype_mk (fun _ => rfl))

lemma cov2_haar_integrable_of_continuous (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2EvaluationContinuous u) : Cov2HaarIntegrable rho u := by
  intro c x hx i j
  exact (cov2_orbit_continuous rho u hu ((chartAt FourSpace c).symm x)
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i))
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector j))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Ordinary continuity of an actual vector section into the tangent bundle. -/

lemma trivialization_eq_chart_differential (c p : M)
    (hp : p ∈ (chartAt FourSpace c).source) (v : TangentSpace I4 p) :
    (trivializationAt FourSpace (TangentSpace I4) c ⟨p, v⟩).2 =
      mfderiv I4 I4 (chartAt FourSpace c) p v := by
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hp v,
    TangentBundle.continuousLinearMapAt_trivializationAt hp]
  rfl

lemma cov2_evaluation_in_trivialization (U : RawCov2 M) (c : M)
    (q : TangentPair M) (hq : q.val.1.proj ∈ (chartAt FourSpace c).source) :
    U q.val.1.proj q.val.1.2 q.val.2.2 = ∑ i : Fin 4, ∑ j : Fin 4,
      (trivializationAt FourSpace (TangentSpace I4) c q.val.1).2 i *
        (cov2InChart U c (chartAt FourSpace c q.val.1.proj) i j *
          (trivializationAt FourSpace (TangentSpace I4) c q.val.2).2 j) := by
  rcases q with ⟨⟨⟨p, v⟩, ⟨r, w⟩⟩, hpr⟩
  change p = r at hpr
  subst r
  have hr := congrArg (fun L => L v w) (cov2_chart_recovery U c p hq)
  rw [← hr]
  change matrixToBilinear (cov2InChart U c (chartAt FourSpace c p))
    (mfderiv I4 I4 (chartAt FourSpace c) p v)
    (mfderiv I4 I4 (chartAt FourSpace c) p w) = _
  rw [← trivialization_eq_chart_differential c p hq v,
    ← trivialization_eq_chart_differential c p hq w]
  simp [matrixToBilinear, coordProj]

variable {k : ℕ∞ω}

lemma cov2_evaluation_continuous (U : RawCov2 M) (hU : Cov2ContDiff k U) :
    Continuous (fun q : TangentPair M => U q.val.1.proj q.val.1.2 q.val.2.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let c := q.val.1.proj
  have hp1 : Continuous (fun z : TangentPair M => z.val.1) := continuous_subtype_val.fst
  have hp2 : Continuous (fun z : TangentPair M => z.val.2) := continuous_subtype_val.snd
  have hproj : ContinuousAt (fun z : TangentPair M => z.val.1.proj) q :=
    ((FiberBundle.continuous_proj FourSpace (TangentSpace I4)).comp hp1).continuousAt
  have hchart : ContinuousAt (chartAt FourSpace c) c :=
    (chartAt FourSpace c).continuousOn.continuousAt (chart_source_mem_nhds FourSpace c)
  have hcoord : ContinuousAt (cov2InChart U c) (chartAt FourSpace c c) :=
    (hU c).continuousOn.continuousAt
      ((chartAt FourSpace c).open_target.mem_nhds (mem_chart_target FourSpace c))
  have hc := hcoord.comp_of_eq (hchart.comp_of_eq hproj rfl) rfl
  have ht1 : ContinuousAt (trivializationAt FourSpace (TangentSpace I4) c) q.val.1 :=
    (trivializationAt FourSpace (TangentSpace I4) c).continuousOn.continuousAt
      ((trivializationAt FourSpace (TangentSpace I4) c).open_source.mem_nhds (by
        change q.val.1.proj ∈ (chartAt FourSpace c).source
        exact mem_chart_source FourSpace c))
  have ht2 : ContinuousAt (trivializationAt FourSpace (TangentSpace I4) c) q.val.2 :=
    (trivializationAt FourSpace (TangentSpace I4) c).continuousOn.continuousAt
      ((trivializationAt FourSpace (TangentSpace I4) c).open_source.mem_nhds (by
        change q.val.2.proj ∈ (chartAt FourSpace c).source
        rw [← q.property]
        exact mem_chart_source FourSpace c))
  have hlocal : ContinuousAt (fun z : TangentPair M => ∑ i : Fin 4, ∑ j : Fin 4,
      (trivializationAt FourSpace (TangentSpace I4) c z.val.1).2 i *
        (cov2InChart U c (chartAt FourSpace c z.val.1.proj) i j *
          (trivializationAt FourSpace (TangentSpace I4) c z.val.2).2 j)) q := by
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    exact ((coordProj i).continuous.continuousAt.comp (ht1.comp_of_eq hp1.continuousAt rfl).snd).mul
      (((continuous_apply_apply i j).continuousAt.comp hc).mul
        ((coordProj j).continuous.continuousAt.comp (ht2.comp_of_eq hp2.continuousAt rfl).snd))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hproj.preimage_mem_nhds (chart_source_mem_nhds FourSpace c)] with z hz
  exact cov2_evaluation_in_trivialization U c z hz

theorem cov2Pi0_smul (rho : CircleAction M) (c : ℝ) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (hcu : Cov2HaarIntegrable rho (c • u)) :
    cov2Pi0 rho (c • u) = c • cov2Pi0 rho u := by
  ext p v w
  rw [SobolevPerpHaar.cov2Pi0_apply rho (c • u) hcu]
  change (∫ t, c * actionPullbackCov2 rho t u p v w ∂circleHaar) =
    c * cov2Pi0 rho u p v w
  rw [integral_const_mul,SobolevPerpHaar.cov2Pi0_apply rho u hu]

theorem linearOn_of_sub_smul {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (S : Set X) (nx : X → ℝ≥0∞)
    (hS : SectionBanachSpace S nx) (A : X → Y)
    (hsub : ∀ u ∈ S, ∀ v ∈ S, A (u-v) = A u-A v)
    (hsmul : ∀ (c : ℝ) (u : X), u ∈ S → A (c • u) = c • A u) :
    SectionLinearOn S A := by
  refine ⟨?_,?_,hsmul⟩
  · simpa only [sub_self] using hsub 0 hS.zero_mem 0 hS.zero_mem
  · intro u hu v hv
    have hh := hsub (u+v) (hS.add_mem u hu v hv) v hv
    rw [add_sub_cancel_right] at hh
    exact (eq_sub_iff_add_eq.mp hh).symm

end K24.Global.SobolevPerpHaar
end K24SOBPERP_Haar_Bundle


/- Inlined source: K24SOBPROJ_CovectorHaar.lean
   SHA256 892baeb49bce0927e9193a8df99dc88096c87a721e79db951765dc9af6f5ee2d. -/
noncomputable section K24SOBPROJ_CovectorHaar_Bundle

/- Selective reuse of inspected K24PERPAll source
   7bb2fa1c57a44839e328e75f211222926999affd (evidence ab18f17),
   whose actual Haar algebra and native bundle continuity originate in HP0
   source161bcd0d3ad79c38a467a899ad203fe5325efdb3, standalone SHA256
   24b7d61cbab4bcad271b5104d98197da7e93859ac4aea232586eb78048d34c90.
   Restricted scalar linearity originates in PERP
   source6d71e461e74d9ee72ab49b23b4e1e48cdad42637. No Holder/Sobolev
   projection regularity or norm continuity is assumed in these helpers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16
open Filter MeasureTheory Bundle
open scoped NNReal ENNReal Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace K24.Global.SobolevProjectionCovectorHaar
open SobolevPerpHaar
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

lemma circleHaar_leftInvariant : circleHaar.IsMulLeftInvariant := by
  unfold circleHaar
  infer_instance

attribute [local instance] circleHaar_leftInvariant

lemma coefficientsToCovector_apply (a : Fin 4 → ℝ) (v : FourSpace) :
    coefficientsToCovector a v = ∑ i : Fin 4, a i * v i := by
  simp [coefficientsToCovector, coordProj]

lemma integrable_covector_coordinates (a : Circle → Fin 4 → ℝ)
    (ha : ∀ i, Integrable (fun t => a t i) circleHaar) (v : FourSpace) :
    Integrable (fun t => coefficientsToCovector (a t) v) circleHaar := by
  simp_rw [coefficientsToCovector_apply]
  exact integrable_finsetSum _ (fun i _ => (ha i).mul_const _)

lemma integral_covector_coordinates (a : Circle → Fin 4 → ℝ)
    (ha : ∀ i, Integrable (fun t => a t i) circleHaar) (v : FourSpace) :
    coefficientsToCovector (fun i => ∫ t, a t i ∂circleHaar) v =
      ∫ t, coefficientsToCovector (a t) v ∂circleHaar := by
  simp_rw [coefficientsToCovector_apply]
  rw [integral_finsetSum _ (fun i _ => (ha i).mul_const _)]
  simp_rw [integral_mul_const]

lemma action_smooth (rho : CircleAction M) (t : Circle) : ContMDiff I4 I4 ∞ (rho.act t) :=
  rho.smooth.comp (contMDiff_const.prodMk contMDiff_id)

lemma action_derivative_mul (rho : CircleAction M) (s t : Circle) (p : M) :
    mfderiv I4 I4 (rho.act (s * t)) p =
      (mfderiv I4 I4 (rho.act s) (rho.act t p)).comp (mfderiv I4 I4 (rho.act t) p) := by
  have heq : rho.act (s * t) = rho.act s ∘ rho.act t := funext (rho.mul_act s t)
  rw [heq]
  exact mfderiv_comp p ((action_smooth rho s).mdifferentiable (by simp) _)
    ((action_smooth rho t).mdifferentiable (by simp) _)

lemma pullback_covector_mul (rho : CircleAction M) (s t : Circle) (u : RawCovector M) :
    actionPullbackCovector rho s (actionPullbackCovector rho t u) =
      actionPullbackCovector rho (t * s) u := by
  funext p
  ext v
  simp only [actionPullbackCovector, pullbackCovector, ContinuousLinearMap.comp_apply]
  rw [action_derivative_mul, rho.mul_act]
  rfl

lemma pullback_cov2_mul (rho : CircleAction M) (s t : Circle) (u : RawCov2 M) :
    actionPullbackCov2 rho s (actionPullbackCov2 rho t u) =
      actionPullbackCov2 rho (t * s) u := by
  funext p
  ext v w
  simp only [actionPullbackCov2, pullbackCov2, bilinearPullback_apply]
  rw [action_derivative_mul, rho.mul_act]
  rfl

lemma covector_chart_eval (u : RawCovector M) (p : M) (v : TangentSpace I4 p) :
    coefficientsToCovector (covectorInChart u p (chartAt FourSpace p p))
      (mfderiv I4 I4 (chartAt FourSpace p) p v) = u p v := by
  have h := covector_chart_recovery u p p (mem_chart_source FourSpace p)
  exact congrArg (fun L => L v) h

lemma covector_orbit_integrable (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (p : M) (v : TangentSpace I4 p) :
    Integrable (fun t => actionPullbackCovector rho t u p v) circleHaar := by
  have h := integrable_covector_coordinates
    (fun t => covectorInChart (actionPullbackCovector rho t u) p (chartAt FourSpace p p))
    (hu p _ (mem_chart_target FourSpace p)) (mfderiv I4 I4 (chartAt FourSpace p) p v)
  simpa only [covector_chart_eval] using h

lemma covectorPi0_apply (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (p : M) (v : TangentSpace I4 p) :
    covectorPi0 rho u p v = ∫ t, actionPullbackCovector rho t u p v ∂circleHaar := by
  change coefficientsToCovector
    (fun i => ∫ t, covectorInChart (actionPullbackCovector rho t u) p
      (chartAt FourSpace p p) i ∂circleHaar)
      (mfderiv I4 I4 (chartAt FourSpace p) p v) = _
  rw [integral_covector_coordinates _ (hu p _ (mem_chart_target FourSpace p))]
  simp only [covector_chart_eval]

lemma covectorPi0_invariant (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) : IsInvariantCovector rho (covectorPi0 rho u) := by
  intro s
  funext p
  ext v
  change covectorPi0 rho u (rho.act s p) (mfderiv I4 I4 (rho.act s) p v) = _
  rw [covectorPi0_apply rho u hu, covectorPi0_apply rho u hu]
  calc
    _ = ∫ t, actionPullbackCovector rho (s * t) u p v ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      change actionPullbackCovector rho s (actionPullbackCovector rho t u) p v = _
      rw [pullback_covector_mul, mul_comm]
    _ = _ := integral_mul_left_eq_self (μ := circleHaar)
      (fun t => actionPullbackCovector rho t u p v) s

lemma cov2Pi0_invariant (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) : IsInvariantCov2 rho (cov2Pi0 rho u) := by
  intro s
  funext p
  ext v w
  change cov2Pi0 rho u (rho.act s p) (mfderiv I4 I4 (rho.act s) p v)
    (mfderiv I4 I4 (rho.act s) p w) = _
  rw [cov2Pi0_apply rho u hu, cov2Pi0_apply rho u hu]
  calc
    _ = ∫ t, actionPullbackCov2 rho (s * t) u p v w ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      change actionPullbackCov2 rho s (actionPullbackCov2 rho t u) p v w = _
      rw [pullback_cov2_mul, mul_comm]
    _ = _ := integral_mul_left_eq_self (μ := circleHaar)
      (fun t => actionPullbackCov2 rho t u p v w) s

lemma covector_integrable_of_invariant (rho : CircleAction M) (u : RawCovector M)
    (hu : IsInvariantCovector rho u) : CovectorHaarIntegrable rho u := by
  intro c x hx i
  simp_rw [show ∀ t, actionPullbackCovector rho t u = u from hu]
  exact integrable_const _

lemma cov2_integrable_of_invariant (rho : CircleAction M) (u : RawCov2 M)
    (hu : IsInvariantCov2 rho u) : Cov2HaarIntegrable rho u := by
  intro c x hx i j
  simp_rw [show ∀ t, actionPullbackCov2 rho t u = u from hu]
  exact integrable_const _

lemma covectorPi0_eq_of_invariant (rho : CircleAction M) (u : RawCovector M)
    (hu : IsInvariantCovector rho u) : covectorPi0 rho u = u := by
  funext p
  ext v
  rw [covectorPi0_apply rho u (covector_integrable_of_invariant rho u hu)]
  simp_rw [show ∀ t, actionPullbackCovector rho t u = u from hu]
  simp

lemma cov2Pi0_eq_of_invariant (rho : CircleAction M) (u : RawCov2 M)
    (hu : IsInvariantCov2 rho u) : cov2Pi0 rho u = u := by
  funext p
  ext v w
  rw [cov2Pi0_apply rho u (cov2_integrable_of_invariant rho u hu)]
  simp_rw [show ∀ t, actionPullbackCov2 rho t u = u from hu]
  simp

lemma covector_integrable_sub (rho : CircleAction M) (u z : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (hz : CovectorHaarIntegrable rho z) :
    CovectorHaarIntegrable rho (u - z) := by
  intro c x hx i
  exact (hu c x hx i).sub (hz c x hx i)

lemma covectorPi0_sub (rho : CircleAction M) (u z : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (hz : CovectorHaarIntegrable rho z) :
    covectorPi0 rho (u - z) = covectorPi0 rho u - covectorPi0 rho z := by
  funext p
  ext v
  rw [covectorPi0_apply rho (u - z) (covector_integrable_sub rho u z hu hz)]
  change (∫ t, actionPullbackCovector rho t u p v - actionPullbackCovector rho t z p v
    ∂circleHaar) = covectorPi0 rho u p v - covectorPi0 rho z p v
  rw [integral_sub (covector_orbit_integrable rho u hu p v)
    (covector_orbit_integrable rho z hz p v), covectorPi0_apply rho u hu,
    covectorPi0_apply rho z hz]

theorem cov2_projection (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) :
    IsInvariantCov2 rho (cov2Pi0 rho u) ∧
    Cov2HaarIntegrable rho (cov2Pi0 rho u) ∧
    cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
    Cov2HaarIntegrable rho (cov2PiPerp rho u) ∧
    IsNonzeroCov2 rho (cov2PiPerp rho u) := by
  have hi := cov2Pi0_invariant rho u hu
  have hint := cov2_integrable_of_invariant rho _ hi
  have hid := cov2Pi0_eq_of_invariant rho _ hi
  refine ⟨hi, hint, hid, cov2_integrable_sub rho u _ hu hint, ?_⟩
  change cov2Pi0 rho (u - cov2Pi0 rho u) = 0
  rw [cov2Pi0_sub rho u _ hu hint, hid, sub_self]

theorem covector_projection (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) :
    IsInvariantCovector rho (covectorPi0 rho u) ∧
    CovectorHaarIntegrable rho (covectorPi0 rho u) ∧
    covectorPi0 rho (covectorPi0 rho u) = covectorPi0 rho u ∧
    CovectorHaarIntegrable rho (covectorPiPerp rho u) ∧
    IsNonzeroCovector rho (covectorPiPerp rho u) := by
  have hi := covectorPi0_invariant rho u hu
  have hint := covector_integrable_of_invariant rho _ hi
  have hid := covectorPi0_eq_of_invariant rho _ hi
  refine ⟨hi, hint, hid, covector_integrable_sub rho u _ hu hint, ?_⟩
  change covectorPi0 rho (u - covectorPi0 rho u) = 0
  rw [covectorPi0_sub rho u _ hu hint, hid, sub_self]

theorem covectorPiPerp_sub (rho : CircleAction M) (u z : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (hz : CovectorHaarIntegrable rho z) :
    covectorPiPerp rho (u - z) = covectorPiPerp rho u - covectorPiPerp rho z := by
  simp only [covectorPiPerp, covectorPi0_sub rho u z hu hz]
  abel

theorem cov2PiPerp_sub (rho : CircleAction M) (u z : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (hz : Cov2HaarIntegrable rho z) :
    cov2PiPerp rho (u - z) = cov2PiPerp rho u - cov2PiPerp rho z := by
  simp only [cov2PiPerp, cov2Pi0_sub rho u z hu hz]
  abel

def CovectorEvaluationContinuous (u : RawCovector M) : Prop :=
  Continuous (fun q : TangentBundle I4 M => u q.proj q.2)

lemma covector_orbit_continuous (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorEvaluationContinuous u) (p : M) (v : TangentSpace I4 p) :
    Continuous (fun t : Circle => actionPullbackCovector rho t u p v) :=
  hu.comp (action_tangent_orbit_continuous rho p v)

lemma covector_haar_integrable_of_continuous (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorEvaluationContinuous u) : CovectorHaarIntegrable rho u := by
  intro c x hx i
  exact (covector_orbit_continuous rho u hu ((chartAt FourSpace c).symm x)
    (mfderiv I4 I4 (chartAt FourSpace c).symm x (basisVector i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem continuous_covector_projection (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorEvaluationContinuous u) :
    CovectorHaarIntegrable rho u ∧
    IsInvariantCovector rho (covectorPi0 rho u) ∧
    CovectorHaarIntegrable rho (covectorPi0 rho u) ∧
    covectorPi0 rho (covectorPi0 rho u) = covectorPi0 rho u ∧
    CovectorHaarIntegrable rho (covectorPiPerp rho u) ∧
    IsNonzeroCovector rho (covectorPiPerp rho u) := by
  have hint := covector_haar_integrable_of_continuous rho u hu
  exact ⟨hint, covector_projection rho u hint⟩

variable {k : ℕ∞ω}

lemma covector_evaluation_in_trivialization (eta : RawCovector M) (c : M)
    (q : TangentBundle I4 M) (hq : q.proj ∈ (chartAt FourSpace c).source) :
    eta q.proj q.2 = ∑ i : Fin 4,
      covectorInChart eta c (chartAt FourSpace c q.proj) i *
        (trivializationAt FourSpace (TangentSpace I4) c q).2 i := by
  have hr := congrArg (fun L => L q.2) (covector_chart_recovery eta c q.proj hq)
  rw [← hr]
  change coefficientsToCovector (covectorInChart eta c (chartAt FourSpace c q.proj))
    (mfderiv I4 I4 (chartAt FourSpace c) q.proj q.2) = _
  rw [← trivialization_eq_chart_differential c q.proj hq q.2]
  simp [coefficientsToCovector, coordProj]

lemma covector_evaluation_continuous (eta : RawCovector M)
    (heta : CovectorContDiff k eta) :
    Continuous (fun q : TangentBundle I4 M => eta q.proj q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let c := q.proj
  have hproj : ContinuousAt (fun z : TangentBundle I4 M => z.proj) q :=
    (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).continuousAt
  have hchart : ContinuousAt (chartAt FourSpace c) c :=
    (chartAt FourSpace c).continuousOn.continuousAt (chart_source_mem_nhds FourSpace c)
  have hcoord : ContinuousAt (covectorInChart eta c) (chartAt FourSpace c c) :=
    (heta c).continuousOn.continuousAt
      ((chartAt FourSpace c).open_target.mem_nhds (mem_chart_target FourSpace c))
  have hc := hcoord.comp_of_eq (hchart.comp_of_eq hproj rfl) rfl
  have htriv : ContinuousAt (trivializationAt FourSpace (TangentSpace I4) c) q :=
    (trivializationAt FourSpace (TangentSpace I4) c).continuousOn.continuousAt
      ((trivializationAt FourSpace (TangentSpace I4) c).open_source.mem_nhds (by
        change q.proj ∈ (chartAt FourSpace c).source
        exact mem_chart_source FourSpace c))
  have hlocal : ContinuousAt (fun z : TangentBundle I4 M => ∑ i : Fin 4,
      covectorInChart eta c (chartAt FourSpace c z.proj) i *
        (trivializationAt FourSpace (TangentSpace I4) c z).2 i) q := by
    apply tendsto_finsetSum
    intro i hi
    exact ((continuous_apply i).continuousAt.comp hc).mul
      ((coordProj i).continuous.continuousAt.comp htriv.snd)
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hproj.preimage_mem_nhds (chart_source_mem_nhds FourSpace c)] with z hz
  exact covector_evaluation_in_trivialization eta c z hz

theorem covectorPi0_smul (rho : CircleAction M) (c : ℝ) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (hcu : CovectorHaarIntegrable rho (c • u)) :
    covectorPi0 rho (c • u) = c • covectorPi0 rho u := by
  ext p v
  rw [covectorPi0_apply rho (c • u) hcu]
  change (∫ t, c * actionPullbackCovector rho t u p v ∂circleHaar) =
    c * covectorPi0 rho u p v
  rw [integral_const_mul,covectorPi0_apply rho u hu]

theorem covector_haar_integrable_of_contDiff (rho : CircleAction M)
    (u : RawCovector M) (hu : CovectorContDiff k u) : CovectorHaarIntegrable rho u :=
  covector_haar_integrable_of_continuous rho u (covector_evaluation_continuous u hu)

end K24.Global.SobolevProjectionCovectorHaar
end K24SOBPROJ_CovectorHaar_Bundle


/- Inlined source: K24SOBGLOBAL_SquareSum.lean
   SHA256 b395da131068a14ee60e8c81a7723771453e3dcab14e882f1f7a4973e147cb66. -/
noncomputable section K24SOBGLOBAL_SquareSum_Bundle

set_option autoImplicit false
open Filter
open scoped NNReal ENNReal Topology BigOperators

namespace K24.Global.SobolevGlobal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable {C : BoundedLocalCover M} (P : SobolevPartition C)
variable {κ : Type*} [Fintype κ]

theorem componentSobolevENorm_sq (s : ℝ) (f : C.Index → κ → FourSpace → ℝ) :
    (P.componentSobolevENorm s f) ^ (2 : ℕ) = P.componentSobolevSquare s f := by
  unfold SobolevPartition.componentSobolevENorm
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem localSobolevENN_le_component (s : ℝ) (f : C.Index → κ → FourSpace → ℝ)
    (ν : C.Index) (a : κ) :
    localSobolevENN s (P.localize ν (f ν a)) ≤ P.componentSobolevENorm s f := by
  have hp : (localSobolevENN s (P.localize ν (f ν a))) ^ (2 : ℕ) ≤
      P.componentSobolevSquare s f := by
    have hsingle : (localSobolevENN s (P.localize ν (f ν a))) ^ (2 : ℕ) ≤
        ∑ b : κ, (localSobolevENN s (P.localize ν (f ν b))) ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun b : κ => (localSobolevENN s (P.localize ν (f ν b))) ^ (2 : ℕ))
        (fun _ _ => bot_le) (Finset.mem_univ a)
    have houter : (∑ b : κ, (localSobolevENN s (P.localize ν (f ν b))) ^ (2 : ℕ)) ≤
        P.componentSobolevSquare s f := ENNReal.le_tsum ν
    exact hsingle.trans houter
  rw [← componentSobolevENorm_sq P s f] at hp
  exact (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp hp

/-- Fatou for the literal partition square sum. Only convergence of the actual
local extended norms is needed; no finite index set or cover-degree bound is
inserted into the norm. -/
theorem componentSobolevENorm_limit_le (s : ℝ)
    (f : ℕ → C.Index → κ → FourSpace → ℝ) (g : C.Index → κ → FourSpace → ℝ)
    (hconv : ∀ ν a, Tendsto
      (fun n => localSobolevENN s (P.localize ν (f n ν a))) atTop
      (𝓝 (localSobolevENN s (P.localize ν (g ν a)))))
    (K : ℝ≥0∞) (hbound : ∀ᶠ n in atTop, P.componentSobolevENorm s (f n) ≤ K) :
    P.componentSobolevENorm s g ≤ K := by
  apply (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp
  rw [componentSobolevENorm_sq]
  unfold SobolevPartition.componentSobolevSquare
  apply ENNReal.summable.tsum_le_of_sum_le
  intro t
  have ht : Tendsto (fun n => ∑ ν ∈ t, ∑ a : κ,
      (localSobolevENN s (P.localize ν (f n ν a))) ^ (2 : ℕ)) atTop
      (𝓝 (∑ ν ∈ t, ∑ a : κ,
        (localSobolevENN s (P.localize ν (g ν a))) ^ (2 : ℕ))) := by
    apply tendsto_finsetSum
    intro ν hν
    apply tendsto_finsetSum
    intro a ha
    exact ENNReal.Tendsto.pow (hconv ν a)
  apply le_of_tendsto ht
  filter_upwards [hbound] with n hn
  have hn2 := pow_le_pow_left' hn 2
  rw [componentSobolevENorm_sq] at hn2
  exact (ENNReal.sum_le_tsum t).trans hn2

end K24.Global.SobolevGlobal
end K24SOBGLOBAL_SquareSum_Bundle


/- Inlined source: K24SOBPROJ_NativeDescent.lean
   SHA256 f98a9a813752341defea5129c37cc560154e70ac3a1b0bb07e3efd7fdc8a2932. -/
noncomputable section K24SOBPROJ_NativeDescent_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff
namespace K24.Global.SobolevProjection
open SobolevGlobal SobolevGlobalGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {C : BoundedLocalCover M} (P : SobolevPartition C)

/-- The accepted all-k embedding applies at all three original real orders. -/
theorem original_order_threshold {s : ℝ} (hs : 4 < s) {j : ℕ} (hj : j ≤ 2) :
    ((2 - j : ℕ) : ℝ) + 2 < s - j := by
  rw [Nat.cast_sub hj]
  norm_num
  linarith

/-- Faithful continuous localized coefficients recover the actual native tensor class. -/
theorem cov2ContDiff_of_localSobolev (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r)
    (u : RawCov2 M)
    (hc : ∀ ν a, Continuous (P.localize ν (SobolevPartition.cov2Components u ν a)))
    (hm : ∀ ν a, LocalSobolevMem r (P.localize ν (SobolevPartition.cov2Components u ν a))) :
    Cov2ContDiff k u := by
  obtain ⟨A, hA⟩ := SobolevProjectionClassical.continuous_localSobolev_classical_bound k r hr
  apply cov2ContDiff_of_localized C P k u
  intro ν a
  exact (hA _ (hc ν a) (hm ν a)).1

/-- Faithful continuous localized coefficients recover the actual native covector class. -/
theorem covectorContDiff_of_localSobolev (k : ℕ) (r : ℝ) (hr : (k : ℝ) + 2 < r)
    (u : RawCovector M)
    (hc : ∀ ν a, Continuous (P.localize ν (SobolevPartition.covectorComponents u ν a)))
    (hm : ∀ ν a, LocalSobolevMem r (P.localize ν (SobolevPartition.covectorComponents u ν a))) :
    CovectorContDiff k u := by
  obtain ⟨A, hA⟩ := SobolevProjectionClassical.continuous_localSobolev_classical_bound k r hr
  apply SobolevProjectionCovector.covectorContDiff_of_localized C P k u
  intro ν a
  exact (hA _ (hc ν a) (hm ν a)).1

theorem cov2Sobolev_of_continuous_localized (k : ℕ) (r : ℝ)
    (hr : (k : ℝ) + 2 < r) (u : RawCov2 M)
    (hc : ∀ ν a, Continuous (P.localize ν (SobolevPartition.cov2Components u ν a)))
    (hn : P.cov2SobolevENorm r u < ⊤) : P.Cov2Sobolev k r u :=
  ⟨cov2ContDiff_of_localSobolev P k r hr u hc (P.local_mem_of_component_finite hn), hn⟩

theorem covectorSobolev_of_continuous_localized (k : ℕ) (r : ℝ)
    (hr : (k : ℝ) + 2 < r) (u : RawCovector M)
    (hc : ∀ ν a, Continuous (P.localize ν (SobolevPartition.covectorComponents u ν a)))
    (hn : P.covectorSobolevENorm r u < ⊤) : P.CovectorSobolev k r u :=
  ⟨covectorContDiff_of_localSobolev P k r hr u hc (P.local_mem_of_component_finite hn), hn⟩

/-- Actual scalar Haar means commute with the original cutoff and lifted tensor coefficient. -/
theorem localize_cov2Pi0 (rho : CircleAction M) (u : RawCov2 M)
    (hu : Cov2HaarIntegrable rho u) (ν : C.Index) (a : Fin 4 × Fin 4) :
    P.localize ν (SobolevPartition.cov2Components (cov2Pi0 rho u) ν a) =
      fun x => ∫ t, P.localize ν
        (SobolevPartition.cov2Components (actionPullbackCov2 rho t u) ν a) x ∂circleHaar := by
  simp only [P.localize_eq_cutoff_mul]
  funext x
  change P.cutoff ν x * cov2Pi0 rho u ((C.chart ν).lift x)
      ((C.chart ν).tangentMap x (basisVector a.1))
      ((C.chart ν).tangentMap x (basisVector a.2)) = _
  rw [SobolevPerpHaar.cov2Pi0_apply rho u hu, ← integral_const_mul]
  rfl

/-- Actual scalar Haar means commute with the original cutoff and lifted covector coefficient. -/
theorem localize_covectorPi0 (rho : CircleAction M) (u : RawCovector M)
    (hu : CovectorHaarIntegrable rho u) (ν : C.Index) (a : Fin 4) :
    P.localize ν (SobolevPartition.covectorComponents (covectorPi0 rho u) ν a) =
      fun x => ∫ t, P.localize ν
        (SobolevPartition.covectorComponents (actionPullbackCovector rho t u) ν a) x ∂circleHaar := by
  simp only [P.localize_eq_cutoff_mul]
  funext x
  change P.cutoff ν x * covectorPi0 rho u ((C.chart ν).lift x)
      ((C.chart ν).tangentMap x (basisVector a)) = _
  rw [SobolevProjectionCovectorHaar.covectorPi0_apply rho u hu, ← integral_const_mul]
  rfl

theorem continuous_localized_cov2_orbit (rho : CircleAction M) (u : RawCov2 M)
    (k : ℕ) (hu : Cov2ContDiff k u) (ν : C.Index) (a : Fin 4 × Fin 4) (x : FourSpace) :
    Continuous (fun t => P.localize ν
      (SobolevPartition.cov2Components (actionPullbackCov2 rho t u) ν a) x) := by
  simp only [P.localize_eq_cutoff_mul, Pi.mul_apply]
  exact continuous_const.mul (SobolevPerpHaar.cov2_orbit_continuous rho u
    (SobolevPerpHaar.cov2_evaluation_continuous u hu) ((C.chart ν).lift x)
    ((C.chart ν).tangentMap x (basisVector a.1))
    ((C.chart ν).tangentMap x (basisVector a.2)))

theorem continuous_localized_covector_orbit (rho : CircleAction M) (u : RawCovector M)
    (k : ℕ) (hu : CovectorContDiff k u) (ν : C.Index) (a : Fin 4) (x : FourSpace) :
    Continuous (fun t => P.localize ν
      (SobolevPartition.covectorComponents (actionPullbackCovector rho t u) ν a) x) := by
  simp only [P.localize_eq_cutoff_mul, Pi.mul_apply]
  exact continuous_const.mul (SobolevProjectionCovectorHaar.covector_orbit_continuous rho u
    (SobolevProjectionCovectorHaar.covector_evaluation_continuous u hu) ((C.chart ν).lift x)
    ((C.chart ν).tangentMap x (basisVector a)))

include P in
/-- Native tensor subtraction, without a symmetry premise. -/
theorem cov2ContDiff_sub (k : ℕ) (u v : RawCov2 M)
    (hu : Cov2ContDiff k u) (hv : Cov2ContDiff k v) : Cov2ContDiff k (u - v) := by
  apply cov2ContDiff_of_localized C P k (u - v)
  intro ν a
  rw [cov2Components_sub]
  change ContDiff ℝ k (P.localize ν (SobolevPartition.cov2Components u ν a -
    SobolevPartition.cov2Components v ν a))
  rw [localize_sub]
  exact (contDiff_localize_cov2Components P u k hu ν a).sub
    (contDiff_localize_cov2Components P v k hv ν a)

theorem cov2Sobolev_sub (k : ℕ) (r : ℝ) (u v : RawCov2 M)
    (hu : P.Cov2Sobolev k r u) (hv : P.Cov2Sobolev k r v) : P.Cov2Sobolev k r (u - v) := by
  refine ⟨cov2ContDiff_sub P k u v hu.1 hv.1, ?_⟩
  exact lt_of_le_of_lt (cov2SobolevENorm_sub_le P r u v hu.2 hv.2)
    (ENNReal.add_lt_top.mpr ⟨hu.2, hv.2⟩)

end K24.Global.SobolevProjection
end K24SOBPROJ_NativeDescent_Bundle


/- Inlined source: K24SOBPERP_Evaluation.lean
   SHA256 ccc0c679eeaadfcd1ea4f0ad82423a01860a03b176555bc5e25c2c2c85a59a6f. -/
noncomputable section K24SOBPERP_Evaluation_excerpt_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16
open Filter MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff Matrix.Norms.Elementwise

namespace K24.Global.SobolevPerp
open SobolevGlobal
theorem continuous_localSobolev_point_bound {s : ℝ} (hs : 2 < s) :
    ∃ A : ℝ≥0, ∀ f : SobolevModel → ℝ, Continuous f → LocalSobolevMem s f →
      ∀ x, ENNReal.ofReal |f x| ≤ (A : ℝ≥0∞) * localSobolevENN s f := by
  obtain ⟨A, hA⟩ := bessel_continuous_norm_bound hs
  refine ⟨A, fun f hfc hf x => ?_⟩
  obtain ⟨G, hG⟩ := besselMem_exists_boundedContinuous hs hf.choose_spec
  have heq := eq_complexify_of_distribution_eq hfc hf.choose G hG
  have hn : |f x| ≤ (A : ℝ) * ‖besselRepresentative hf.choose_spec‖ := by
    have heval : ‖G x‖ = |f x| := by rw [heq]; simp [complexifyLocal]
    rw [← heval]
    exact (G.norm_coe_le_norm x).trans (hA _ hf.choose_spec G hG)
  rw [localSobolevENN, dif_pos hf.choose, besselSobolevENN_of_mem hf.choose_spec]
  simpa only [ENNReal.ofReal_mul A.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
    ENNReal.ofReal_le_ofReal hn

end K24.Global.SobolevPerp
end K24SOBPERP_Evaluation_excerpt_Bundle


/- Inlined source: K24SOBPROJ_Measurability.lean
   SHA256 c6fc99407bc1b4ee7201017b63cbc6dc530debfc5800b4b5700e10f66602e1d7. -/
noncomputable section K24SOBPROJ_Measurability_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16
open MeasureTheory TemperedDistribution Filter
open scoped NNReal ENNReal Topology SchwartzMap
namespace K24.Global.SobolevProjection

/-- Continuity in the actual pointwise distribution topology suffices for
strong measurability of its genuine L2 representative. Lusin-Souslin supplies
the measurable inverse of the canonical injective L2 distribution map. -/
theorem stronglyMeasurable_of_continuous_distribution
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (f : A → LocalL2) (hf : Continuous (fun a => (f a : LocalDistribution))) :
    StronglyMeasurable f := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : MeasurableSpace LocalL2 := borel LocalL2
  letI : BorelSpace LocalL2 := ⟨rfl⟩
  letI : MeasurableSpace LocalDistribution := borel LocalDistribution
  letI : BorelSpace LocalDistribution := ⟨rfl⟩
  have hL : MeasurableEmbedding (fun v : LocalL2 => (v : LocalDistribution)) :=
    (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.measurableEmbedding
      localL2_distribution_injective
  exact (hL.measurable_comp_iff.mp hf.measurable).stronglyMeasurable

/-- The original Bessel representative family is strongly measurable when
the original distribution family is continuous; norm continuity is not assumed. -/
theorem stronglyMeasurable_besselRepresentative
    {A : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    {s : ℝ} (T : A → LocalDistribution) (hT : ∀ a, BesselMem s (T a))
    (hcont : Continuous T) : StronglyMeasurable (fun a => besselRepresentative (hT a)) := by
  apply stronglyMeasurable_of_continuous_distribution
  have hh : (fun a => (besselRepresentative (hT a) : LocalDistribution)) =
      fun a => besselPotential SobolevModel ℂ s (T a) := by
    funext a
    exact (besselRepresentative_spec (hT a)).symm
  rw [hh]
  exact (besselPotential SobolevModel ℂ s).continuous.comp hcont

end K24.Global.SobolevProjection

end K24SOBPROJ_Measurability_Bundle


/- Inlined source: K24SOBPROJ_LocalPairings.lean
   SHA256 8d9ca41245ab406471ea4a5ef4ba74e102e7b7fc1077827c380bf98178a4f84d. -/
noncomputable section K24SOBPROJ_LocalPairings_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16
open MeasureTheory TemperedDistribution Filter
open scoped NNReal ENNReal Topology SchwartzMap
namespace K24.Global.SobolevProjection
open SobolevGlobal SobolevPerp

theorem localFunctionDistribution_apply (f : SobolevModel → ℝ)
    (hf : MemLp (complexifyLocal f) 2 volume) (φ : 𝓢(SobolevModel, ℂ)) :
    localFunctionDistribution f hf φ = ∫ x, φ x * complexifyLocal f x := by
  unfold localFunctionDistribution
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
  rfl

/-- The actual coefficient distributions vary continuously in the pointwise
Schwartz-dual topology under separate continuity and a genuine uniform C0 bound. -/
theorem continuous_localFunctionDistribution
    (f : Circle → SobolevModel → ℝ)
    (hfx : ∀ t, Continuous (f t)) (hft : ∀ x, Continuous (fun t => f t x))
    (hf : ∀ t, MemLp (complexifyLocal (f t)) 2 volume)
    (B : ℝ≥0) (hb : ∀ t x, |f t x| ≤ B) :
    Continuous (fun t => localFunctionDistribution (f t) (hf t)) := by
  apply PointwiseConvergenceCLM.continuous_of_continuous_eval
  intro φ
  simp_rw [localFunctionDistribution_apply]
  apply continuous_of_dominated
    (bound := fun x => ‖φ x‖ * (B : ℝ))
  · intro t
    exact (φ.continuous.mul (Complex.continuous_ofReal.comp (hfx t))).aestronglyMeasurable
  · intro t
    filter_upwards with x
    simpa only [norm_mul, complexifyLocal, Complex.norm_real, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (hb t x) (norm_nonneg (φ x))
  · exact φ.integrable.norm.mul_const B
  · filter_upwards with x
    exact continuous_const.mul (Complex.continuous_ofReal.comp (hft x))

/-- Original real-order local norms give a true uniform pointwise bound. -/
theorem localSobolev_family_point_bound {s : ℝ} (hs : 2 < s)
    (f : Circle → SobolevModel → ℝ) (hfx : ∀ t, Continuous (f t))
    (hf : ∀ t, LocalSobolevMem s (f t)) (K : ℝ≥0)
    (hb : ∀ t, localSobolevENN s (f t) ≤ (K : ℝ≥0∞)) :
    ∃ B : ℝ≥0, ∀ t x, |f t x| ≤ B := by
  obtain ⟨A, hA⟩ := continuous_localSobolev_point_bound hs
  refine ⟨A * K, fun t x => ?_⟩
  have hh : ENNReal.ofReal |f t x| ≤ ((A * K : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_mul]
    exact (hA (f t) (hfx t) (hf t) x).trans
      (mul_le_mul (le_refl _) (hb t) bot_le bot_le)
  have hr := ENNReal.toReal_mono ENNReal.coe_ne_top hh
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.coe_toReal] using hr

/-- Separate continuity is enough for joint strong measurability here; the
circle parameter is second-countable and metrizable. -/
theorem stronglyMeasurable_local_family
    (f : Circle → SobolevModel → ℝ) (hfx : ∀ t, Continuous (f t))
    (hft : ∀ x, Continuous (fun t => f t x)) :
    StronglyMeasurable (fun z : Circle × SobolevModel => complexifyLocal (f z.1) z.2) := by
  exact stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun x => Complex.continuous_ofReal.comp (hft x))
    (fun t => (Complex.continuous_ofReal.comp (hfx t)).stronglyMeasurable)

/-- Every actual Schwartz pairing is integrable on the product, justifying
Fubini for the actual scalar Haar average. -/
theorem integrable_local_pairing_product
    (f : Circle → SobolevModel → ℝ) (hfx : ∀ t, Continuous (f t))
    (hft : ∀ x, Continuous (fun t => f t x))
    (B : ℝ≥0) (hb : ∀ t x, |f t x| ≤ B) (φ : 𝓢(SobolevModel, ℂ)) :
    Integrable (fun z : Circle × SobolevModel => φ z.2 * complexifyLocal (f z.1) z.2)
      (circleHaar.prod volume) := by
  have hm : StronglyMeasurable
      (fun z : Circle × SobolevModel => φ z.2 * complexifyLocal (f z.1) z.2) :=
    (φ.continuous.comp continuous_snd).stronglyMeasurable.mul
      (stronglyMeasurable_local_family f hfx hft)
  apply ((φ.integrable.norm.mul_const (B : ℝ)).comp_snd circleHaar).mono' hm.aestronglyMeasurable
  filter_upwards with z
  simpa only [norm_mul, complexifyLocal, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left (hb z.1 z.2) (norm_nonneg (φ z.2))

end K24.Global.SobolevProjection
end K24SOBPROJ_LocalPairings_Bundle


/- Inlined source: K24SOBPROJ_LocalAverage.lean
   SHA256 f660ce7cfe898f9896b4df483953f8f9acf0081bd543dc02b1b4edc0c7866312. -/
noncomputable section K24SOBPROJ_LocalAverage_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16
open MeasureTheory TemperedDistribution Filter
open scoped NNReal ENNReal Topology SchwartzMap BoundedContinuousFunction
namespace K24.Global.SobolevProjection
open SobolevGlobal

/-- Actual local Haar averaging commutes with the unique Bessel L2
representative. Every measurability, Fubini, and finite-norm premise is proved
from separate continuity and the supplied bound in the original local norm. -/
theorem localSobolev_average {s : ℝ} (hs : 2 < s)
    (f : Circle → SobolevModel → ℝ)
    (hfx : ∀ t, Continuous (f t)) (hft : ∀ x, Continuous (fun t => f t x))
    (hf : ∀ t, LocalSobolevMem s (f t)) (K : ℝ≥0)
    (hb : ∀ t, localSobolevENN s (f t) ≤ (K : ℝ≥0∞)) :
    Continuous (fun x => ∫ t, f t x ∂circleHaar) ∧
      ∃ hg : LocalSobolevMem s (fun x => ∫ t, f t x ∂circleHaar),
        localBesselRepresentative hg =
          ∫ t, localBesselRepresentative (hf t) ∂circleHaar ∧
        Integrable (fun t => localBesselRepresentative (hf t)) circleHaar := by
  obtain ⟨B, hB⟩ := localSobolev_family_point_bound hs f hfx hf K hb
  let D : Circle → LocalDistribution := fun t => localFunctionDistribution (f t) (hf t).choose
  have hDc : Continuous D := continuous_localFunctionDistribution f hfx hft
    (fun t => (hf t).choose) B hB
  let v : Circle → LocalL2 := fun t => localBesselRepresentative (hf t)
  have hvm : StronglyMeasurable v := stronglyMeasurable_besselRepresentative
    D (fun t => (hf t).choose_spec) hDc
  have hvb : ∀ t, ‖v t‖ ≤ (K : ℝ) := by
    intro t
    have hh := hb t
    rw [localSobolevENN_eq_norm (hf t)] at hh
    have hr := ENNReal.toReal_mono ENNReal.coe_ne_top hh
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.coe_toReal] using hr
  have hvi : Integrable v circleHaar :=
    (integrable_const (K : ℝ)).mono' hvm.aestronglyMeasurable (Eventually.of_forall hvb)
  let g : SobolevModel → ℝ := fun x => ∫ t, f t x ∂circleHaar
  have hgc : Continuous g := by
    apply continuous_of_dominated (bound := fun _ : Circle => (B : ℝ))
    · intro x
      exact (hft x).aestronglyMeasurable
    · intro x
      filter_upwards with t
      simpa only [Real.norm_eq_abs] using hB t x
    · exact integrable_const _
    · exact Eventually.of_forall hfx
  have hgb : ∀ x, |g x| ≤ (B : ℝ) := by
    intro x
    have hh := norm_integral_le_of_norm_le_const (μ := circleHaar)
      (f := fun t => f t x) (C := (B : ℝ)) (Eventually.of_forall fun t => ?_)
    · simpa [Real.norm_eq_abs, measureReal_def, g] using hh
    · simpa only [Real.norm_eq_abs] using hB t x
  let G : SobolevModel →ᵇ ℂ := BoundedContinuousFunction.mkOfBound
    ⟨complexifyLocal g, Complex.continuous_ofReal.comp hgc⟩ (2 * (B : ℝ)) (by
      intro x y
      calc
        dist (complexifyLocal g x) (complexifyLocal g y) ≤
            ‖complexifyLocal g x‖ + ‖complexifyLocal g y‖ := dist_le_norm_add_norm _ _
        _ ≤ 2 * (B : ℝ) := by
          simpa only [complexifyLocal, Complex.norm_real, Real.norm_eq_abs, two_mul] using
            add_le_add (hgb x) (hgb y))
  let V : LocalL2 := ∫ t, v t ∂circleHaar
  let T : LocalDistribution := inverseBesselL2 s V
  have hT : BesselMem s T := inverseBesselL2_mem s V
  have hGdist : boundedContinuousDistribution G = T := by
    ext φ
    let L : LocalL2 →L[ℂ] ℂ :=
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp
        ((besselPotential SobolevModel ℂ (-s)).comp (Lp.toTemperedDistributionCLM ℂ volume 2))
    have hL (t : Circle) : L (v t) = D t φ := by
      change inverseBesselL2 s (besselRepresentative (hf t).choose_spec) φ = _
      rw [inverseBesselL2_representative]
    have hprod := integrable_local_pairing_product f hfx hft B hB φ
    have hgint (x : SobolevModel) : complexifyLocal g x =
        ∫ t, complexifyLocal (f t) x ∂circleHaar := by
      exact (Complex.ofRealCLM.integral_comp_comm
        ((hft x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm
    rw [boundedContinuousDistribution_apply]
    change (∫ x, φ x * complexifyLocal g x) = T φ
    calc
      _ = ∫ x : SobolevModel, (∫ t, φ x * complexifyLocal (f t) x ∂circleHaar) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hgint, integral_const_mul]
      _ = ∫ t, (∫ x : SobolevModel, φ x * complexifyLocal (f t) x ∂volume) ∂circleHaar :=
        (integral_integral_swap hprod).symm
      _ = ∫ t, L (v t) ∂circleHaar := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hL, localFunctionDistribution_apply]
      _ = L V := L.integral_comp_comm hvi
      _ = T φ := rfl
  obtain ⟨G', hG'L2, hG'T⟩ := besselMem_exists_boundedContinuous_L2 hs hT
  have heq : G = G' := boundedContinuousDistribution_injective
    (hGdist.trans ((boundedContinuousDistribution_eq_L2 G' hG'L2).trans hG'T).symm)
  have hgl : MemLp (complexifyLocal g) 2 volume := by
    change MemLp (G : SobolevModel → ℂ) 2 volume
    rw [heq]
    exact hG'L2
  have hgd : localFunctionDistribution g hgl = T :=
    (boundedContinuousDistribution_eq_L2 G hgl).symm.trans hGdist
  have hgm : LocalSobolevMem s g := ⟨hgl, by rw [hgd]; exact hT⟩
  refine ⟨hgc, hgm, ?_, hvi⟩
  apply besselRepresentative_unique
  change besselPotential SobolevModel ℂ s (localFunctionDistribution g hgl) =
    (V : LocalDistribution)
  rw [hgd]
  exact besselPotential_inverseBesselL2 s V

end K24.Global.SobolevProjection

end K24SOBPROJ_LocalAverage_Bundle


/- Inlined source: K24SOBPROJ_NativeAverage.lean
   SHA256 859bdd5a642b1bfb342fead700538eae9ecf3c20288230e758c848fa5874296c. -/
noncomputable section K24SOBPROJ_NativeAverage_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff
namespace K24.Global.SobolevProjection
open SobolevGlobal SobolevGlobalGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {C : BoundedLocalCover M} (P : SobolevPartition C)

/-- Local regularity of the genuine Haar mean follows from the original uniformly
bounded pullback classes, with no strong/norm continuity hypothesis. -/
theorem cov2Pi0_local_regular (k : ℕ) (r : ℝ) (hr : 2 < r)
    (rho : CircleAction M) (u : RawCov2 M) (hu : Cov2ContDiff k u)
    (horbit : ∀ t, P.Cov2Sobolev k r (actionPullbackCov2 rho t u))
    (K : ℝ≥0) (hb : ∀ t, P.cov2SobolevENorm r (actionPullbackCov2 rho t u) ≤ K) :
    ∀ ν a, Continuous (P.localize ν (SobolevPartition.cov2Components (cov2Pi0 rho u) ν a)) ∧
      LocalSobolevMem r (P.localize ν (SobolevPartition.cov2Components (cov2Pi0 rho u) ν a)) := by
  have hint := SobolevPerpHaar.cov2_haar_integrable_of_continuous rho u
    (SobolevPerpHaar.cov2_evaluation_continuous u hu)
  intro ν a
  rw [localize_cov2Pi0 P rho u hint ν a]
  have hav := localSobolev_average hr
    (fun t => P.localize ν (SobolevPartition.cov2Components (actionPullbackCov2 rho t u) ν a))
    (fun t => (contDiff_localize_cov2Components P _ k (horbit t).1 ν a).continuous)
    (continuous_localized_cov2_orbit P rho u k hu ν a)
    (fun t => P.local_mem_of_component_finite (horbit t).2 ν a) K
    (fun t => (localSobolevENN_le_component P r _ ν a).trans (hb t))
  exact ⟨hav.1, hav.2.choose⟩

theorem covectorPi0_local_regular (k : ℕ) (r : ℝ) (hr : 2 < r)
    (rho : CircleAction M) (u : RawCovector M) (hu : CovectorContDiff k u)
    (horbit : ∀ t, P.CovectorSobolev k r (actionPullbackCovector rho t u))
    (K : ℝ≥0) (hb : ∀ t, P.covectorSobolevENorm r (actionPullbackCovector rho t u) ≤ K) :
    ∀ ν a, Continuous (P.localize ν (SobolevPartition.covectorComponents (covectorPi0 rho u) ν a)) ∧
      LocalSobolevMem r (P.localize ν (SobolevPartition.covectorComponents (covectorPi0 rho u) ν a)) := by
  have hint := SobolevProjectionCovectorHaar.covector_haar_integrable_of_contDiff rho u hu
  intro ν a
  rw [localize_covectorPi0 P rho u hint ν a]
  have hav := localSobolev_average hr
    (fun t => P.localize ν (SobolevPartition.covectorComponents (actionPullbackCovector rho t u) ν a))
    (fun t => (SobolevProjectionCovector.contDiff_localize_covectorComponents P _ k
      (horbit t).1 ν a).continuous)
    (continuous_localized_covector_orbit P rho u k hu ν a)
    (fun t => P.local_mem_of_component_finite (horbit t).2 ν a) K
    (fun t => (localSobolevENN_le_component P r _ ν a).trans (hb t))
  exact ⟨hav.1, hav.2.choose⟩

/-- Actual C(2-j) tensor regularity at every original real order, including j=1. -/
theorem cov2Pi0_native_of_actionControl (s : ℝ) (hs : 4 < s) (H : ℝ≥0)
    (rho : CircleAction M) (hcontrol : SobolevActionControl P s H rho)
    (j : ℕ) (hj : j ≤ 2) (u : RawCov2 M) (hu : P.Cov2Sobolev (2-j) (s-j) u) :
    Cov2HaarIntegrable rho u ∧ Cov2ContDiff (2-j) (cov2Pi0 rho u) := by
  have hr := original_order_threshold hs hj
  have hr2 : 2 < s - j := by have := Nat.cast_nonneg (α := ℝ) (2-j); linarith
  have hK : ((H * (P.cov2SobolevENorm (s-j) u).toNNReal : ℝ≥0) : ℝ≥0∞) =
      (H : ℝ≥0∞) * P.cov2SobolevENorm (s-j) u := by
    rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hu.2.ne]
  have hav := cov2Pi0_local_regular P (2-j) (s-j) hr2 rho u hu.1
    (fun t => (hcontrol.tensor j hj t u hu).1) (H * (P.cov2SobolevENorm (s-j) u).toNNReal)
    (fun t => by rw [hK]; exact (hcontrol.tensor j hj t u hu).2)
  refine ⟨SobolevPerpHaar.cov2_haar_integrable_of_continuous rho u
    (SobolevPerpHaar.cov2_evaluation_continuous u hu.1), ?_⟩
  exact cov2ContDiff_of_localSobolev P (2-j) (s-j) hr _
    (fun ν a => (hav ν a).1) (fun ν a => (hav ν a).2)

/-- Actual C(2-j) covector regularity at every original real order, including j=1. -/
theorem covectorPi0_native_of_actionControl (s : ℝ) (hs : 4 < s) (H : ℝ≥0)
    (rho : CircleAction M) (hcontrol : SobolevActionControl P s H rho)
    (j : ℕ) (hj : j ≤ 2) (u : RawCovector M) (hu : P.CovectorSobolev (2-j) (s-j) u) :
    CovectorHaarIntegrable rho u ∧ CovectorContDiff (2-j) (covectorPi0 rho u) := by
  have hr := original_order_threshold hs hj
  have hr2 : 2 < s - j := by have := Nat.cast_nonneg (α := ℝ) (2-j); linarith
  have hK : ((H * (P.covectorSobolevENorm (s-j) u).toNNReal : ℝ≥0) : ℝ≥0∞) =
      (H : ℝ≥0∞) * P.covectorSobolevENorm (s-j) u := by
    rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hu.2.ne]
  have hav := covectorPi0_local_regular P (2-j) (s-j) hr2 rho u hu.1
    (fun t => (hcontrol.covector j hj t u hu).1) (H * (P.covectorSobolevENorm (s-j) u).toNNReal)
    (fun t => by rw [hK]; exact (hcontrol.covector j hj t u hu).2)
  refine ⟨SobolevProjectionCovectorHaar.covector_haar_integrable_of_contDiff rho u hu.1, ?_⟩
  exact covectorContDiff_of_localSobolev P (2-j) (s-j) hr _
    (fun ν a => (hav ν a).1) (fun ν a => (hav ν a).2)

end K24.Global.SobolevProjection
end K24SOBPROJ_NativeAverage_Bundle


/- Inlined source: K24SOBPROJ_FiniteNorm.lean
   SHA256 1e5e9e223de69e561fe0800ddb999ed18310edb0096bceb9e94848f3ff236a73. -/
noncomputable section K24SOBPROJ_FiniteNorm_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16
open MeasureTheory TemperedDistribution Filter
open scoped NNReal ENNReal Topology BigOperators
namespace K24.Global.SobolevProjection
open SobolevGlobal

/-- The finite Hilbert product uses exactly the sum of the original squared
coordinate norms. In particular no cardinality constant is introduced. -/
theorem piL2_ennnorm_sq {ι : Type*} [Fintype ι]
    (v : PiLp 2 (fun _ : ι => LocalL2)) :
    (ENNReal.ofReal ‖v‖) ^ (2 : ℕ) =
      ∑ i, (ENNReal.ofReal ‖v i‖) ^ (2 : ℕ) := by
  rw [← ENNReal.ofReal_pow (norm_nonneg _), PiLp.norm_sq_eq_of_L2]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖v i‖)]
  simp only [ENNReal.ofReal_pow (norm_nonneg _)]

/-- Haar averaging in a finite Hilbert product preserves a uniform bound
on the exact sum of squares. Integrability is coordinatewise, and the
coordinate projections commute with the actual Bochner integral. -/
theorem finite_l2_integral_bound {ι : Type*} [Fintype ι]
    (v : Circle → ι → LocalL2)
    (hv : ∀ i, Integrable (fun t => v t i) circleHaar)
    (K : ℝ≥0)
    (hb : ∀ t, (∑ i, (ENNReal.ofReal ‖v t i‖) ^ (2 : ℕ)) ≤
      (K : ℝ≥0∞) ^ (2 : ℕ)) :
    (∑ i, (ENNReal.ofReal ‖∫ t, v t i ∂circleHaar‖) ^ (2 : ℕ)) ≤
      (K : ℝ≥0∞) ^ (2 : ℕ) := by
  let V : Circle → PiLp 2 (fun _ : ι => LocalL2) := fun t => WithLp.toLp 2 (v t)
  have hVi : Integrable V circleHaar := integrable_piLp_iff.mpr hv
  have hVb : ∀ t, ‖V t‖ ≤ (K : ℝ) := by
    intro t
    apply ENNReal.ofReal_le_coe.mp
    apply (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp
    rw [piL2_ennnorm_sq]
    exact hb t
  have hnorm : ‖∫ t, V t ∂circleHaar‖ ≤ (K : ℝ) := by
    simpa [measureReal_def] using norm_integral_le_of_norm_le_const
      (μ := circleHaar) (Eventually.of_forall hVb)
  have heval (i : ι) :
      (∫ t, V t ∂circleHaar) i = ∫ t, v t i ∂circleHaar := by
    exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => LocalL2) i).integral_comp_comm hVi).symm
  calc
    _ = (ENNReal.ofReal ‖∫ t, V t ∂circleHaar‖) ^ (2 : ℕ) := by
      rw [piL2_ennnorm_sq]
      simp_rw [heval]
    _ ≤ _ := pow_le_pow_left' (ENNReal.ofReal_le_coe.mpr hnorm) 2

end K24.Global.SobolevProjection

end K24SOBPROJ_FiniteNorm_Bundle


/- Inlined source: K24SOBPROJ_FiniteNormGlobal.lean
   SHA256 5a2f39e2c15472dee965ef3ede9bab4e45198c60e6c33924a3f9b4cd7cba9e4d. -/
noncomputable section K24SOBPROJ_FiniteNormGlobal_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 16
open MeasureTheory TemperedDistribution Filter
open scoped NNReal ENNReal Topology BigOperators
namespace K24.Global.SobolevProjection
open SobolevGlobal

/-- Exact square-sum control of genuine scalar Haar means, for an arbitrary
index type. The proof integrates each finite Hilbert product and then uses
the universal finite-partial-sum characterization of the ENNReal sum. -/
theorem localSobolev_average_square_sum_le {ι : Type*} {s : ℝ} (hs : 2 < s)
    (f : Circle → ι → SobolevModel → ℝ)
    (hfx : ∀ t i, Continuous (f t i))
    (hft : ∀ i x, Continuous (fun t => f t i x))
    (hf : ∀ t i, LocalSobolevMem s (f t i)) (K : ℝ≥0)
    (hb : ∀ t, (∑' i, (localSobolevENN s (f t i)) ^ (2 : ℕ)) ≤
      (K : ℝ≥0∞) ^ (2 : ℕ)) :
    (∀ i, Continuous (fun x => ∫ t, f t i x ∂circleHaar) ∧
      LocalSobolevMem s (fun x => ∫ t, f t i x ∂circleHaar)) ∧
    (∑' i, (localSobolevENN s (fun x => ∫ t, f t i x ∂circleHaar)) ^ (2 : ℕ)) ≤
      (K : ℝ≥0∞) ^ (2 : ℕ) := by
  have hbound (t : Circle) (i : ι) : localSobolevENN s (f t i) ≤ (K : ℝ≥0∞) := by
    apply (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp
    exact (ENNReal.le_tsum i).trans (hb t)
  have hm (i : ι) := localSobolev_average hs (fun t => f t i)
    (fun t => hfx t i) (hft i) (fun t => hf t i) K (fun t => hbound t i)
  let hg (i : ι) : LocalSobolevMem s (fun x => ∫ t, f t i x ∂circleHaar) :=
    (hm i).2.choose
  have hrep (i : ι) : localBesselRepresentative (hg i) =
      ∫ t, localBesselRepresentative (hf t i) ∂circleHaar := (hm i).2.choose_spec.1
  have hi (i : ι) : Integrable (fun t => localBesselRepresentative (hf t i)) circleHaar :=
    (hm i).2.choose_spec.2
  refine ⟨fun i => ⟨(hm i).1, hg i⟩, ?_⟩
  apply ENNReal.summable.tsum_le_of_sum_le
  intro S
  have hfinite := finite_l2_integral_bound
    (fun t (i : S) => localBesselRepresentative (hf t i))
    (fun i => hi i) K (fun t => ?_)
  · have heq (i : ι) :
        ENNReal.ofReal ‖∫ t, localBesselRepresentative (hf t i) ∂circleHaar‖ =
        localSobolevENN s (fun x => ∫ t, f t i x ∂circleHaar) := by
      rw [← hrep i, localSobolevENN_eq_norm (hg i)]
    simp_rw [heq] at hfinite
    simpa only [Finset.sum_coe_sort (s := S)
      (f := fun i => (localSobolevENN s (fun x => ∫ t, f t i x ∂circleHaar)) ^ (2 : ℕ))]
      using hfinite
  · simp_rw [← localSobolevENN_eq_norm (hf _ _)]
    rw [Finset.sum_coe_sort (s := S)
      (f := fun i => (localSobolevENN s (f t i)) ^ (2 : ℕ))]
    exact (ENNReal.sum_le_tsum S).trans (hb t)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
variable {C : BoundedLocalCover M} (P : SobolevPartition C)
variable {κ : Type*} [Fintype κ]

/-- An actual localized Haar average has exactly the original component norm
bound. This theorem has no native-regularity or norm-orbit-continuity premise. -/
theorem componentSobolevENorm_le_of_localized_average {s : ℝ} (hs : 2 < s)
    (f : Circle → C.Index → κ → FourSpace → ℝ)
    (g : C.Index → κ → FourSpace → ℝ)
    (hfx : ∀ t ν a, Continuous (P.localize ν (f t ν a)))
    (hft : ∀ ν a x, Continuous (fun t => P.localize ν (f t ν a) x))
    (hf : ∀ t ν a, LocalSobolevMem s (P.localize ν (f t ν a)))
    (hg : ∀ ν a, P.localize ν (g ν a) =
      fun x => ∫ t, P.localize ν (f t ν a) x ∂circleHaar)
    (K : ℝ≥0) (hb : ∀ t, P.componentSobolevENorm s (f t) ≤ (K : ℝ≥0∞)) :
    (∀ ν a, Continuous (P.localize ν (g ν a)) ∧
      LocalSobolevMem s (P.localize ν (g ν a))) ∧
    P.componentSobolevENorm s g ≤ (K : ℝ≥0∞) := by
  have havg := localSobolev_average_square_sum_le hs
    (fun t (i : C.Index × κ) => P.localize i.1 (f t i.1 i.2))
    (fun t i => hfx t i.1 i.2) (fun i x => hft i.1 i.2 x)
    (fun t i => hf t i.1 i.2) K (fun t => ?_)
  · refine ⟨?_, ?_⟩
    · intro ν a
      rw [hg ν a]
      exact havg.1 (ν, a)
    · apply (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp
      rw [componentSobolevENorm_sq]
      unfold SobolevPartition.componentSobolevSquare
      simp_rw [hg]
      simpa only [ENNReal.tsum_prod', tsum_fintype] using havg.2
  · have hh := pow_le_pow_left' (hb t) 2
    rw [componentSobolevENorm_sq] at hh
    simpa only [SobolevPartition.componentSobolevSquare, ENNReal.tsum_prod', tsum_fintype]
      using hh

end K24.Global.SobolevProjection

end K24SOBPROJ_FiniteNormGlobal_Bundle


/- Inlined source: K24SOBPROJ_ProjectionExact.lean
   SHA256 a41116cff4b8cc2ab9e70f926bff90c91657cd2814cfead09e65454e924b5789. -/
noncomputable section K24SOBPROJ_ProjectionExact_Bundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped NNReal ENNReal Topology Manifold ContDiff
namespace K24.Global.SobolevProjection
open SobolevGlobal SobolevGlobalGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {C : BoundedLocalCover M} (P : SobolevPartition C)

/-- Exact original tensor projection field for every real s > 4 and j ≤ 2. -/
theorem tensor_projection (s : ℝ) (hs : 4 < s) (H : ℝ≥0)
    (rho : CircleAction M) (hcontrol : SobolevActionControl P s H rho) :
    ∀ j ≤ 2, ∀ u : RawCov2 M, P.Cov2Sobolev (2 - j) (s - j) u →
      Cov2HaarIntegrable rho u ∧
      P.Cov2Sobolev (2 - j) (s - j) (cov2Pi0 rho u) ∧
      P.Cov2Sobolev (2 - j) (s - j) (cov2PiPerp rho u) ∧
      cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
      IsNonzeroCov2 rho (cov2PiPerp rho u) ∧
      P.cov2SobolevENorm (s - j) (cov2Pi0 rho u) ≤
        (H : ℝ≥0∞) * P.cov2SobolevENorm (s - j) u ∧
      P.cov2SobolevENorm (s - j) (cov2PiPerp rho u) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * P.cov2SobolevENorm (s - j) u := by
  intro j hj u hu
  obtain ⟨hint, hnative⟩ := cov2Pi0_native_of_actionControl P s hs H rho hcontrol j hj u hu
  have hr : 2 < s - j := by
    have := original_order_threshold hs hj
    have := Nat.cast_nonneg (α := ℝ) (2-j)
    linarith
  have hK : ((H * (P.cov2SobolevENorm (s-j) u).toNNReal : ℝ≥0) : ℝ≥0∞) =
      (H : ℝ≥0∞) * P.cov2SobolevENorm (s-j) u := by
    rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hu.2.ne]
  have hav := componentSobolevENorm_le_of_localized_average P hr
    (fun t => SobolevPartition.cov2Components (actionPullbackCov2 rho t u))
    (SobolevPartition.cov2Components (cov2Pi0 rho u))
    (fun t ν a => (contDiff_localize_cov2Components P _ (2-j)
      (hcontrol.tensor j hj t u hu).1.1 ν a).continuous)
    (continuous_localized_cov2_orbit P rho u (2-j) hu.1)
    (fun t => P.local_mem_of_component_finite (hcontrol.tensor j hj t u hu).1.2)
    (localize_cov2Pi0 P rho u hint)
    (H * (P.cov2SobolevENorm (s-j) u).toNNReal)
    (fun t => by rw [hK]; exact (hcontrol.tensor j hj t u hu).2)
  have hbound : P.cov2SobolevENorm (s-j) (cov2Pi0 rho u) ≤
      (H : ℝ≥0∞) * P.cov2SobolevENorm (s-j) u := hav.2.trans_eq hK
  have hclass : P.Cov2Sobolev (2-j) (s-j) (cov2Pi0 rho u) :=
    ⟨hnative, hbound.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu.2)⟩
  have halgebra := SobolevProjectionCovectorHaar.cov2_projection rho u hint
  refine ⟨hint, hclass, cov2Sobolev_sub P _ _ u _ hu hclass,
    halgebra.2.2.1, halgebra.2.2.2.2, hbound, ?_⟩
  change P.cov2SobolevENorm (s-j) (u - cov2Pi0 rho u) ≤ _
  calc
    _ ≤ P.cov2SobolevENorm (s-j) u + P.cov2SobolevENorm (s-j) (cov2Pi0 rho u) :=
      cov2SobolevENorm_sub_le P _ u _ hu.2 hclass.2
    _ ≤ P.cov2SobolevENorm (s-j) u + (H : ℝ≥0∞) * P.cov2SobolevENorm (s-j) u :=
      add_le_add (le_refl _) hbound
    _ = _ := by rw [ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]

/-- Exact original covector projection field for every real s > 4 and j ≤ 2. -/
theorem covector_projection (s : ℝ) (hs : 4 < s) (H : ℝ≥0)
    (rho : CircleAction M) (hcontrol : SobolevActionControl P s H rho) :
    ∀ j ≤ 2, ∀ eta : RawCovector M, P.CovectorSobolev (2 - j) (s - j) eta →
      CovectorHaarIntegrable rho eta ∧
      P.CovectorSobolev (2 - j) (s - j) (covectorPi0 rho eta) ∧
      P.CovectorSobolev (2 - j) (s - j) (covectorPiPerp rho eta) ∧
      IsNonzeroCovector rho (covectorPiPerp rho eta) ∧
      P.covectorSobolevENorm (s - j) (covectorPi0 rho eta) ≤
        (H : ℝ≥0∞) * P.covectorSobolevENorm (s - j) eta ∧
      P.covectorSobolevENorm (s - j) (covectorPiPerp rho eta) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * P.covectorSobolevENorm (s - j) eta := by
  intro j hj u hu
  obtain ⟨hint, hnative⟩ := covectorPi0_native_of_actionControl P s hs H rho hcontrol j hj u hu
  have hr : 2 < s - j := by
    have := original_order_threshold hs hj
    have := Nat.cast_nonneg (α := ℝ) (2-j)
    linarith
  have hK : ((H * (P.covectorSobolevENorm (s-j) u).toNNReal : ℝ≥0) : ℝ≥0∞) =
      (H : ℝ≥0∞) * P.covectorSobolevENorm (s-j) u := by
    rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hu.2.ne]
  have hav := componentSobolevENorm_le_of_localized_average P hr
    (fun t => SobolevPartition.covectorComponents (actionPullbackCovector rho t u))
    (SobolevPartition.covectorComponents (covectorPi0 rho u))
    (fun t ν a => (SobolevProjectionCovector.contDiff_localize_covectorComponents P _ (2-j)
      (hcontrol.covector j hj t u hu).1.1 ν a).continuous)
    (continuous_localized_covector_orbit P rho u (2-j) hu.1)
    (fun t => P.local_mem_of_component_finite (hcontrol.covector j hj t u hu).1.2)
    (localize_covectorPi0 P rho u hint)
    (H * (P.covectorSobolevENorm (s-j) u).toNNReal)
    (fun t => by rw [hK]; exact (hcontrol.covector j hj t u hu).2)
  have hbound : P.covectorSobolevENorm (s-j) (covectorPi0 rho u) ≤
      (H : ℝ≥0∞) * P.covectorSobolevENorm (s-j) u := hav.2.trans_eq hK
  have hclass : P.CovectorSobolev (2-j) (s-j) (covectorPi0 rho u) :=
    ⟨hnative, hbound.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu.2)⟩
  have halgebra := SobolevProjectionCovectorHaar.covector_projection rho u hint
  refine ⟨hint, hclass, SobolevProjectionCovector.covectorSobolev_sub P _ _ u _ hu hclass,
    halgebra.2.2.2.2, hbound, ?_⟩
  change P.covectorSobolevENorm (s-j) (u - covectorPi0 rho u) ≤ _
  calc
    _ ≤ P.covectorSobolevENorm (s-j) u + P.covectorSobolevENorm (s-j) (covectorPi0 rho u) :=
      SobolevProjectionCovector.covectorSobolevENorm_sub_le P _ u _ hu.2 hclass.2
    _ ≤ P.covectorSobolevENorm (s-j) u + (H : ℝ≥0∞) * P.covectorSobolevENorm (s-j) u :=
      add_le_add (le_refl _) hbound
    _ = _ := by rw [ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]

end K24.Global.SobolevProjection
end K24SOBPROJ_ProjectionExact_Bundle


open scoped NNReal ENNReal Topology Manifold ContDiff
open K24.Global in
theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] {C : BoundedLocalCover M} (P : SobolevPartition C)
    (s : ℝ) (hs : 4 < s) (H : ℝ≥0) (rho : CircleAction M)
    (hcontrol : SobolevActionControl P s H rho) :
    (∀ j ≤ 2, ∀ u : RawCov2 M, P.Cov2Sobolev (2 - j) (s - j) u →
      Cov2HaarIntegrable rho u ∧
      P.Cov2Sobolev (2 - j) (s - j) (cov2Pi0 rho u) ∧
      P.Cov2Sobolev (2 - j) (s - j) (cov2PiPerp rho u) ∧
      cov2Pi0 rho (cov2Pi0 rho u) = cov2Pi0 rho u ∧
      IsNonzeroCov2 rho (cov2PiPerp rho u) ∧
      P.cov2SobolevENorm (s - j) (cov2Pi0 rho u) ≤
        (H : ℝ≥0∞) * P.cov2SobolevENorm (s - j) u ∧
      P.cov2SobolevENorm (s - j) (cov2PiPerp rho u) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * P.cov2SobolevENorm (s - j) u) ∧
    (∀ j ≤ 2, ∀ eta : RawCovector M, P.CovectorSobolev (2 - j) (s - j) eta →
      CovectorHaarIntegrable rho eta ∧
      P.CovectorSobolev (2 - j) (s - j) (covectorPi0 rho eta) ∧
      P.CovectorSobolev (2 - j) (s - j) (covectorPiPerp rho eta) ∧
      IsNonzeroCovector rho (covectorPiPerp rho eta) ∧
      P.covectorSobolevENorm (s - j) (covectorPi0 rho eta) ≤
        (H : ℝ≥0∞) * P.covectorSobolevENorm (s - j) eta ∧
      P.covectorSobolevENorm (s - j) (covectorPiPerp rho eta) ≤
        ((1 + H : ℝ≥0) : ℝ≥0∞) * P.covectorSobolevENorm (s - j) eta) := by
  exact ⟨K24.Global.SobolevProjection.tensor_projection P s hs H rho hcontrol,
    K24.Global.SobolevProjection.covector_projection P s hs H rho hcontrol⟩

#print axioms solution
#check @solution
