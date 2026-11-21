-- Prove2me | solution 1 for MasulloRH.rational_theta_annihilator_jet_trace
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:21:04.64475+00:00
-- url     : https://prove2.me/submissions/07027aca-ac1f-4c3b-a2b9-727fe6e98afa

import Mathlib
import Definitions.Def_MasulloRH_RationalThetaSpace
import Theorems.Thm_MasulloRH_critical_line_jet_convolution_trace
import Theorems.Thm_MasulloRH_dyadic_gaussian_theta_mellin
import Theorems.Thm_MasulloRH_rational_theta_test_factorization
import Theorems.Thm_MasulloRH_sobolev_spectral_synthesis

namespace ThetaRealProof
open _root_.MasulloRH

section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology ContDiff
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace LocalRH
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem integratedOperator_exists
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (W : ℝ → ℝ) (A : ℝ)
    (hcont : ∀ u, Continuous (fun y => U y u))
    (hK : AEStronglyMeasurable K) (hKW : Integrable (fun y => ‖K y‖ * W y))
    (hW : ∀ y, 0 ≤ W y) (hA : 0 ≤ A) (hU : ∀ y, ‖U y‖ ≤ A * W y) :
    ∃ T : H →L[ℂ] H, (∀ u, T u = ∫ y : ℝ, K y • U y u) ∧
      ‖T‖ ≤ A * ∫ y : ℝ, ‖K y‖ * W y := by
  have hdom (u : H) (y : ℝ) :
      ‖K y • U y u‖ ≤ (‖K y‖ * W y) * (A * ‖u‖) := by
    rw [norm_smul]
    calc
      _ ≤ ‖K y‖ * ((A * W y) * ‖u‖) := by
        gcongr
        exact ((U y).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hU y) (norm_nonneg _))
      _ = _ := by ring
  have hi (u : H) : Integrable (fun y => K y • U y u) := by
    apply (hKW.mul_const (A * ‖u‖)).mono' (hK.smul (hcont u).aestronglyMeasurable)
    exact Eventually.of_forall (hdom u)
  let L : H →ₗ[ℂ] H := {
    toFun := fun u => ∫ y : ℝ, K y • U y u
    map_add' := by
      intro u v
      simp only [map_add, smul_add, integral_add (hi u) (hi v)]
    map_smul' := by
      intro c u
      simp only [map_smul, RingHom.id_apply]
      simp_rw [smul_comm (K _) c, integral_smul] }
  have hb (u : H) : ‖L u‖ ≤ (A * ∫ y : ℝ, ‖K y‖ * W y) * ‖u‖ := by
    calc
      _ ≤ ∫ y : ℝ, (‖K y‖ * W y) * (A * ‖u‖) := by
        exact norm_integral_le_of_norm_le (hKW.mul_const _) (Eventually.of_forall (hdom u))
      _ = _ := by rw [integral_mul_const]; ring
  have hC : 0 ≤ A * ∫ y : ℝ, ‖K y‖ * W y := mul_nonneg hA
    (integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (hW y)))
  exact ⟨L.mkContinuous _ hb, fun _ => rfl, L.mkContinuous_norm_le hC hb⟩

theorem integratedOperator_eigen
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ u, T u = ∫ y : ℝ, K y • U y u)
    (character : ℝ → ℂ) (v : H) (hv : ∀ y, U y v = character y • v) :
    T v = (∫ y : ℝ, K y * character y) • v := by
  rw [hT]
  simp_rw [hv, smul_smul]
  exact integral_smul_const _ _

theorem integratedOperator_fourier
    (U : ℝ → H →L[ℂ] H) (K : ℝ → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ u, T u = ∫ y : ℝ, K y • U y u)
    (ξ : ℝ) (v : H)
    (hv : ∀ y : ℝ, U y v = Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • v) :
    T v = (𝓕 K ξ) • v := by
  rw [integratedOperator_eigen U K T hT _ v hv, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => mul_comm _ _

theorem integratedOperator_inverseFourier
    (U : ℝ → H →L[ℂ] H) (m : ℝ → ℂ) (T : H →L[ℂ] H)
    (hm : Integrable m) (hmF : Integrable (𝓕 m))
    (hT : ∀ u, T u = ∫ y : ℝ, (𝓕⁻ m) y • U y u)
    (ξ : ℝ) (hmξ : ContinuousAt m ξ) (v : H)
    (hv : ∀ y : ℝ, U y v = Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • v) :
    T v = m ξ • v := by
  rw [integratedOperator_fourier U (𝓕⁻ m) T hT ξ v hv, hm.fourier_fourierInv_eq hmF hmξ]

end LocalRH
open scoped InnerProductSpace FourierTransform SchwartzMap
open Filter MeasureTheory FourierTransform
private lemma fourier_uniqueness_L1 {f : ℝ → ℂ} (hf : Integrable f)
    (hz : ∀ ξ : ℝ, 𝓕 f ξ = 0) : ∀ᵐ x, f x = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hgc
  let h : ℝ → ℂ := fun x => (g x : ℂ)
  have hhc : HasCompactSupport h := hgc.comp_left (g:=fun z : ℝ => (z:ℂ)) (by simp)
  have hhs : ContDiff ℝ ∞ h := Complex.ofRealCLM.contDiff.comp hg
  let b := hhc.toSchwartzMap hhs
  let t : 𝓢(ℝ,ℂ) := 𝓕⁻ b
  have hswap : (∫ ξ : ℝ, 𝓕 (t:ℝ→ℂ) ξ • f ξ) = ∫ x : ℝ, t x • 𝓕 f x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L:=innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner t.integrable hf
  have he : 𝓕 (t:ℝ→ℂ) = (b:ℝ→ℂ) := by rw [← SchwartzMap.fourier_coe]; simp [t]
  simp only [he,hz,smul_zero,integral_zero] at hswap
  change (∫ x : ℝ, (g x:ℂ) * f x) = 0 at hswap
  simpa only [Complex.real_smul] using hswap

/-- A family of all real characters multiplied by a fixed a.e. nonzero L² weight is total.
The L² hypothesis on the weight follows from the representative of the zero mode. -/
theorem MasulloSynthesis.all_modes_total (w : ℝ → ℂ) (hw : ∀ᵐ x, w x ≠ 0) (v : ℝ → Lp ℂ 2 (volume : Measure ℝ))
    (hv : ∀ ξ : ℝ, (v ξ : ℝ → ℂ) =ᵐ[volume]
      (fun x : ℝ => w x * Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I))) :
    (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro z hz
  have horth (ξ : ℝ) : inner ℂ z (v ξ) = 0 :=
    (Submodule.span ℂ (Set.range v)).inner_left_of_mem_orthogonal (Submodule.subset_span ⟨ξ,rfl⟩) hz
  let f : ℝ → ℂ := fun x => inner ℂ (z x) (v 0 x)
  have hi : Integrable f := L2.integrable_inner z (v 0)
  have hv0 : (v 0 : ℝ→ℂ) =ᵐ[volume] w := by simpa using hv 0
  have hF (ξ : ℝ) : 𝓕 f ξ = 0 := by
    rw [← horth ξ, L2.inner_def, Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards [hv ξ,hv0] with x hx hx0
    simp only [f, hx, hx0, RCLike.inner_apply, smul_eq_mul, conj_trivial]
    rw [show -2*Real.pi*(ξ*x) = -2*Real.pi*x*ξ by ring]
    ring
  have hzero := fourier_uniqueness_L1 hi hF
  apply Lp.ext
  filter_upwards [hzero,hv0,hw,Lp.coeFn_zero (E:=ℂ) (p:=2) (μ:=(volume : Measure ℝ))] with x hx hx0 hxw hz0
  rw [hz0]
  change z x = 0
  change inner ℂ (z x) (v 0 x) = 0 at hx
  rw [RCLike.inner_apply, hx0] at hx
  simpa using (mul_eq_zero.mp hx).resolve_left hxw

open LocalRH
namespace MasulloSynthesis
private lemma schwartz_weighted_integral (g : 𝓢(ℝ,ℂ)) (k : ℕ) :
    Integrable (fun x : ℝ => (1+|x|)^k * ‖g x‖) := by
  have h := (g.integrable.norm.add (g.integrable_pow_mul volume k)).const_mul ((2:ℝ)^(k-1))
  apply h.mono' (by fun_prop)
  refine Eventually.of_forall fun x => ?_
  change ‖(1+|x|)^k * ‖g x‖‖ ≤ 2^(k-1) * (‖g x‖ + ‖x‖ ^ k * ‖g x‖)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, ← one_add_mul, ← mul_assoc]
  gcongr
  simpa using add_pow_le (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg x) k


lemma makeFrequencyOperator {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (U : ℝ → H →L[ℂ] H) (k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (horbit : ∀ u, Continuous (fun y => U y u))
    (hU : ∀ y, ‖U y‖ ≤ B * (1+|y|)^k) (m : 𝓢(ℝ,ℂ)) :
    ∃ T : H →L[ℂ] H, (∀ u, T u = ∫ y : ℝ, (𝓕⁻ (⇑m)) y • U y u) ∧
      ‖T‖ ≤ B * (∫ y : ℝ, (1+|y|)^k * ‖(𝓕⁻ (⇑m)) y‖) ∧
      ∀ (ξ : ℝ) (v : H), (∀ y : ℝ, U y v = Complex.exp (↑(-2*Real.pi*y*ξ) * Complex.I) • v) →
        T v = m ξ • v := by
  let g : 𝓢(ℝ,ℂ) := 𝓕⁻ m
  have hcoe : (⇑g : ℝ → ℂ) = 𝓕⁻ (⇑m) := SchwartzMap.fourierInv_coe m
  have hK : AEStronglyMeasurable (𝓕⁻ (⇑m)) := hcoe ▸ g.continuous.aestronglyMeasurable
  have hw : Integrable (fun x : ℝ => ‖(𝓕⁻ (⇑m)) x‖ * (1+|x|)^k) := by
    simpa only [mul_comm (‖_‖), ← hcoe] using schwartz_weighted_integral g k
  obtain ⟨T,hT,hb⟩ := integratedOperator_exists U (𝓕⁻ (⇑m)) (fun y : ℝ => (1+|y|)^k) B
    horbit hK hw (fun y => by positivity) hB hU
  refine ⟨T, hT, ?_, ?_⟩
  · simpa only [mul_comm (‖_‖)] using hb
  · intro ξ v hv
    apply integratedOperator_inverseFourier U m T m.integrable _ hT ξ m.continuous.continuousAt v hv
    simpa only [← SchwartzMap.fourier_coe] using (𝓕 m : 𝓢(ℝ,ℂ)).integrable


end MasulloSynthesis
end

section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap FourierTransform Topology BigOperators
set_option autoImplicit false
namespace MasulloSynthesis
noncomputable section

abbrev H := Lp ℂ 2 (volume : Measure ℝ)

def weight (a : ℝ) (x : ℝ) : ℂ := ((1+x^2)^a : ℝ)

theorem weight_temperate (a : ℝ) : (weight a).HasTemperateGrowth := by
  have h := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ a
  have h' := Complex.ofRealCLM.hasTemperateGrowth.comp h
  change (fun x : ℝ => (((1+x^2)^a : ℝ):ℂ)).HasTemperateGrowth
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Real.norm_eq_abs, sq_abs] using h'

theorem weight_mul (a b x : ℝ) : weight a x * weight b x = weight (a+b) x := by
  unfold weight
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]

def logDistribution (p : ℝ) : H →L[ℂ] 𝓢'(ℝ,ℂ) :=
  (fourierInvCLM ℂ 𝓢'(ℝ,ℂ)).comp
    ((TemperedDistribution.smulLeftCLM ℂ (weight (p/2))).comp (Lp.toTemperedDistributionCLM ℂ volume 2))

theorem logDistribution_apply (p : ℝ) (u : H) (f : 𝓢(ℝ,ℂ)) :
    logDistribution p u f = ∫ x : ℝ, (weight (p/2) x * (𝓕⁻ f) x) * u x := by
  change 𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ _ (Lp.toTemperedDistribution u)) f = _
  rw [TemperedDistribution.fourierInv_apply,TemperedDistribution.smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply]
  simp only [SchwartzMap.smulLeftCLM_apply_apply (weight_temperate _), smul_eq_mul]

theorem logDistribution_mode (p ν : ℝ) (v : H)
    (hv : (v : ℝ → ℂ) =ᵐ[volume] fun x : ℝ => weight (-p/2) x *
        Complex.exp (↑(-2*Real.pi*x*ν) * Complex.I)) (f : 𝓢(ℝ,ℂ)) :
    logDistribution p v f = f ν := by
  rw [logDistribution_apply]
  have h := congrArg (fun g : 𝓢(ℝ,ℂ) => g ν) (fourier_fourierInv_eq (F := 𝓢(ℝ,ℂ)) f)
  change (𝓕 (𝓕⁻ f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ)) ν = f ν at h
  rw [← h]
  change _ = 𝓕 (⇑(𝓕⁻ f : 𝓢(ℝ,ℂ))) ν
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [hx,smul_eq_mul]
  have hw : weight (p/2) x * weight (-p/2) x = 1 := by
    rw [weight_mul, show p/2 + -p/2 = 0 by ring]
    simp [weight]
  linear_combination (norm := ring_nf) ((𝓕⁻ f) x * Complex.exp (↑(-2*Real.pi*x*ν) * Complex.I)) * hw

theorem logDistribution_intertwines {ι : Type*} (p : ℝ) (v : ι → H) (ν : ι → ℝ)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (heval : ∀ i (f : 𝓢(ℝ,ℂ)), logDistribution p (v i) f = f (ν i))
    (A : H →L[ℂ] H) (b : 𝓢(ℝ,ℂ))
    (hA : ∀ i, A (v i) = b (ν i) • v i) (u : H) :
    logDistribution p (A u) = TemperedDistribution.smulLeftCLM ℂ b (logDistribution p u) := by
  let L := (logDistribution p).comp A
  let R := (TemperedDistribution.smulLeftCLM ℂ b).comp (logDistribution p)
  have he : L = R := ContinuousLinearMap.ext_on hd (by
    rintro _ ⟨i,rfl⟩
    ext f
    simp only [L,R,ContinuousLinearMap.comp_apply,hA,map_smul,TemperedDistribution.smulLeftCLM_apply_apply]
    change b (ν i) * (logDistribution p (v i) f) = _
    rw [heval,heval,SchwartzMap.smulLeftCLM_apply_apply b.hasTemperateGrowth]
    rfl)
  exact DFunLike.congr_fun he u
end
end MasulloSynthesis
end

section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace LocalRH
noncomputable section

abbrev LogL2 := Lp ℂ 2 (volume : Measure ℝ)

def logWeight (p x : ℝ) : ℝ := (1 + |x|) ^ (-p)

lemma logWeight_pos (p x : ℝ) : 0 < logWeight p x := Real.rpow_pos_of_pos (by positivity) _

lemma continuous_logWeight (p : ℝ) : Continuous (logWeight p) := by
  apply Continuous.rpow_const (continuous_const.add continuous_abs)
  exact fun x => Or.inl (show (1 + |x| : ℝ) ≠ 0 by positivity)

lemma logWeight_ratio_le {p : ℝ} (hp : 0 ≤ p) (x y : ℝ) :
    logWeight p x / logWeight p (x+y) ≤ (1 + |y|)^p := by
  have hx : 0 < 1 + |x| := by positivity
  have hxy : 0 < 1 + |x+y| := by positivity
  have hab : 1 + |x+y| ≤ (1 + |x|) * (1 + |y|) := by
    nlinarith [abs_add_le x y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]
  rw [logWeight, logWeight, Real.rpow_neg hx.le, Real.rpow_neg hxy.le, inv_div_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hx p)).2
  rw [mul_comm, ← Real.mul_rpow hx.le (show 0 ≤ 1 + |y| by positivity)]
  exact Real.rpow_le_rpow hxy.le hab hp

private def ratio (p y x : ℝ) : ℂ := (logWeight p x / logWeight p (x+y) : ℝ)

private lemma ratio_norm (p y x : ℝ) : ‖ratio p y x‖ = logWeight p x / logWeight p (x+y) := by
  exact Complex.norm_of_nonneg (div_nonneg (logWeight_pos _ _).le (logWeight_pos _ _).le)

private lemma ratio_mem (p : ℝ) (hp : 0 ≤ p) (y : ℝ) : MemLp (ratio p y) ⊤ volume := by
  apply memLp_top_of_bound _ ((1+|y|)^p) (ae_of_all _ fun x => (ratio_norm p y x).le.trans (logWeight_ratio_le hp x y))
  apply Continuous.aestronglyMeasurable
  exact Complex.continuous_ofReal.comp <| (continuous_logWeight p).div
    ((continuous_logWeight p).comp (continuous_id.add_const y)) (fun x => (logWeight_pos _ _).ne')

private def shift (y : ℝ) : LogL2 →ₗᵢ[ℂ] LogL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x+y) (measurePreserving_add_right volume y)

def weightedTranslation (p : ℝ) (hp : 0 ≤ p) (y : ℝ) : LogL2 →L[ℂ] LogL2 :=
  (((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2) ((ratio_mem p hp y).toLp (ratio p y))).comp
    (shift y).toContinuousLinearMap

lemma weightedTranslation_apply_ae (p : ℝ) (hp : 0 ≤ p) (y : ℝ) (f : LogL2) :
    (weightedTranslation p hp y f : ℝ → ℂ) =ᵐ[volume] fun x =>
      ((logWeight p x / logWeight p (x+y) : ℝ) : ℂ) * f (x+y) := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((ratio_mem p hp y).toLp (ratio p y)) (shift y f)
  have hs := Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)
  refine h.trans ?_
  filter_upwards [(ratio_mem p hp y).coeFn_toLp, hs] with x hx hsx
  change ((ratio_mem p hp y).toLp (ratio p y)) x * (shift y f) x = _
  change (shift y f) x = f (x+y) at hsx
  rw [hx, hsx]; rfl

lemma norm_weightedTranslation_le (p : ℝ) (hp : 0 ≤ p) (y : ℝ) :
    ‖weightedTranslation p hp y‖ ≤ (1+|y|)^p := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [← (shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedTranslation_apply_ae p hp y f,
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hs
  change (shift y f) x = f (x+y) at hs
  rw [hx, hs, norm_mul]
  exact mul_le_mul_of_nonneg_right ((ratio_norm p y x).le.trans (logWeight_ratio_le hp x y)) (norm_nonneg _)

lemma weightedTranslation_add (p : ℝ) (hp : 0 ≤ p) (y z : ℝ) :
    weightedTranslation p hp (y+z) = (weightedTranslation p hp y).comp (weightedTranslation p hp z) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hz := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp
    (weightedTranslation_apply_ae p hp z f)
  filter_upwards [weightedTranslation_apply_ae p hp (y+z) f,
    weightedTranslation_apply_ae p hp y ((weightedTranslation p hp z) f), hz] with x hall hy hz
  change (weightedTranslation p hp z f) (x+y) = _ at hz
  change (weightedTranslation p hp (y+z) f) x = (weightedTranslation p hp y ((weightedTranslation p hp z) f)) x
  rw [hall, hy, hz]
  simp only [Function.comp_apply, ← add_assoc, ← mul_assoc, ← Complex.ofReal_mul]
  field_simp [ne_of_gt (logWeight_pos p (x+y)), ne_of_gt (logWeight_pos p (x+y+z))]

def angularCharacter (ξ x : ℝ) : ℂ := Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)

lemma angularCharacter_add (ξ x y : ℝ) :
    angularCharacter ξ (x+y) = angularCharacter ξ x * angularCharacter ξ y := by
  simp [angularCharacter, mul_add, add_mul, Complex.exp_add]

lemma norm_angularCharacter (ξ x : ℝ) : ‖angularCharacter ξ x‖ = 1 := by
  simp [angularCharacter, Complex.norm_exp]

lemma weightedExponential_memLp (p ξ : ℝ) (hp : 1/2 < p) :
    MemLp (fun x : ℝ => (logWeight p x : ℂ) * angularCharacter ξ x) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm _).2
  · have hdeg : (Module.finrank ℝ ℝ : ℝ) < 2*p := by simp; linarith
    have hint := integrable_one_add_norm (E := ℝ) (μ := volume) hdeg
    apply hint.congr
    apply Filter.Eventually.of_forall
    intro x
    change (1 + ‖x‖)^(-(2*p)) = ‖(logWeight p x : ℂ) * angularCharacter ξ x‖^2
    rw [norm_mul, norm_angularCharacter, mul_one, Complex.norm_of_nonneg (logWeight_pos _ _).le,
      logWeight, ← Real.rpow_mul_natCast (by positivity)]
    simp [Real.norm_eq_abs, mul_comm]
  · apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp (continuous_logWeight p)).mul
      (show Continuous (angularCharacter ξ) by unfold angularCharacter; fun_prop)

def weightedExponential (p ξ : ℝ) (hp : 1/2 < p) : LogL2 := (weightedExponential_memLp p ξ hp).toLp _

lemma weightedTranslation_exponential (p ξ : ℝ) (hp : 1/2 < p) (y : ℝ) :
    weightedTranslation p (by linarith) y (weightedExponential p ξ hp) =
      angularCharacter ξ y • weightedExponential p ξ hp := by
  have he := (weightedExponential_memLp p ξ hp).coeFn_toLp
  have hesh := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp he
  apply Lp.ext
  filter_upwards [weightedTranslation_apply_ae p (by linarith) y (weightedExponential p ξ hp), he,
    hesh, Lp.coeFn_smul (angularCharacter ξ y) (weightedExponential p ξ hp)] with x hU hx hxy hsm
  change weightedExponential p ξ hp x = (logWeight p x : ℂ) * angularCharacter ξ x at hx
  change weightedExponential p ξ hp (x+y) = (logWeight p (x+y) : ℂ) * angularCharacter ξ (x+y) at hxy
  rw [hU, hsm, Pi.smul_apply, smul_eq_mul, hx, hxy, angularCharacter_add, Complex.ofReal_div]
  field_simp [ne_of_gt (logWeight_pos p (x+y))]

private lemma ratio_sub_one_bound {p : ℝ} (hp : 0 ≤ p) (x y : ℝ) :
    |logWeight p x / logWeight p (x+y) - 1| ≤ (1+|y|)^p - 1 := by
  let a := logWeight p x / logWeight p (x+y)
  let D := (1+|y|)^p
  have hD : 1 ≤ D := Real.one_le_rpow (by linarith [abs_nonneg y]) hp
  have ha : a ≤ D := logWeight_ratio_le hp x y
  have hinv := logWeight_ratio_le hp (x+y) (-y)
  simp only [add_neg_cancel_right, abs_neg] at hinv
  have hDa : 1 ≤ D*a := by
    change 1 ≤ D * (logWeight p x / logWeight p (x+y))
    rw [← mul_div_assoc, le_div_iff₀ (logWeight_pos p (x+y)), one_mul]
    exact (div_le_iff₀ (logWeight_pos p x)).mp hinv
  change |a-1| ≤ D-1
  apply abs_le.mpr
  refine ⟨?_, by linarith⟩
  by_cases h : a ≤ 1
  · have h' := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hD)
    nlinarith
  · linarith

private lemma shift_continuous (f : LogL2) : Continuous (fun y : ℝ => shift y f) := by
  let g : C(ℝ × ℝ, ℝ) := ⟨fun z => z.2 + z.1, continuous_snd.add continuous_fst⟩
  exact continuous_const.compMeasurePreservingLp (g := g.curry) g.curry.continuous
    (fun y => measurePreserving_add_right volume y) (by norm_num)

private lemma diff_shift_bound (p : ℝ) (hp : 0 ≤ p) (y : ℝ) (f : LogL2) :
    ‖weightedTranslation p hp y f - shift y f‖ ≤ ((1+|y|)^p-1) * ‖f‖ := by
  rw [← (shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedTranslation_apply_ae p hp y f,
    Lp.coeFn_sub (weightedTranslation p hp y f) (shift y f),
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hsub hs
  change (shift y f) x = f (x+y) at hs
  rw [hsub, Pi.sub_apply, hx, hs, ← sub_one_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact ratio_sub_one_bound hp x y

lemma continuous_weightedTranslation_orbit (p : ℝ) (hp : 0 ≤ p) (f : LogL2) :
    Continuous (fun y : ℝ => weightedTranslation p hp y f) := by
  have hlim : Tendsto (fun y : ℝ => weightedTranslation p hp y f) (𝓝 0) (𝓝 f) := by
    have hg : Continuous (fun y : ℝ => ((1+|y|)^p-1) * ‖f‖) := by
      apply Continuous.mul_const
      apply Continuous.sub _ continuous_const
      apply Continuous.rpow_const (continuous_const.add continuous_abs)
      exact fun x => Or.inl (show (1 + |x| : ℝ) ≠ 0 by positivity)
    have hbound : Tendsto (fun y : ℝ => ((1+|y|)^p-1) * ‖f‖) (𝓝 0) (𝓝 0) := by
      simpa using hg.tendsto 0
    have hdiff : Tendsto (fun y : ℝ => weightedTranslation p hp y f - shift y f) (𝓝 0) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ => norm_nonneg _) (fun y => diff_shift_bound p hp y f) hbound
    have hs0 : shift 0 f = f := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume (0:ℝ))] with x hx
      change (shift 0 f) x = f (x+0) at hx
      simpa only [add_zero] using hx
    have hs := (shift_continuous f).tendsto 0
    rw [hs0] at hs
    simpa only [sub_add_cancel, zero_add] using hdiff.add hs
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd : Tendsto (fun z : ℝ => z-y) (𝓝 y) (𝓝 0) := by simpa using (show Continuous (fun z : ℝ => z-y) from continuous_id.sub continuous_const).tendsto y
  have h := (weightedTranslation p hp y).continuous.continuousAt.tendsto.comp (hlim.comp hd)
  refine h.congr fun z => ?_
  change (weightedTranslation p hp y) ((weightedTranslation p hp (z-y)) f) = _
  rw [← ContinuousLinearMap.comp_apply, ← weightedTranslation_add]
  simp

end
end LocalRH
end

section
open MeasureTheory Filter Set
open scoped Topology
namespace LocalRH
noncomputable section

def paperWeight (p x : ℝ) := (1+x^2)^(-p/2)
theorem paperWeight_pos (p x : ℝ) : 0 < paperWeight p x := Real.rpow_pos_of_pos (by positivity) _
private theorem paperWeight_cont (p : ℝ) : Continuous (paperWeight p) := by
  unfold paperWeight
  exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))

private theorem weightRatio_upper {p : ℝ} (hp : 0 < p) (x : ℝ) :
    paperWeight p x / logWeight p x ≤ 2^(p/2) := by
  apply (div_le_iff₀ (logWeight_pos _ _)).mpr
  simpa only [paperWeight, logWeight, Real.norm_eq_abs, sq_abs] using rpow_neg_one_add_norm_sq_le x hp

private theorem weightRatio_lower {p : ℝ} (hp : 0 < p) (x : ℝ) :
    logWeight p x / paperWeight p x ≤ 1 := by
  rw [div_le_one (paperWeight_pos _ _), paperWeight, Real.rpow_div_two_eq_sqrt _ (by positivity)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hp.le)
  simpa only [Real.norm_eq_abs, sq_abs] using sqrt_one_add_norm_sq_le x

private def weightChange (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x) (C : ℝ) (hC : ∀ x, f x / g x ≤ C) : LogL2 →L[ℂ] LogL2 :=
  let v := fun x : ℝ => ((f x / g x : ℝ) : ℂ)
  let hv : MemLp v ⊤ volume := memLp_top_of_bound
      (Complex.continuous_ofReal.comp (hf.div hg (fun x => (hgp x).ne'))).aestronglyMeasurable C
      (ae_of_all _ (fun x => by
        change ‖((f x / g x : ℝ) : ℂ)‖ ≤ C
        rw [Complex.norm_of_nonneg (div_nonneg (hfp x).le (hgp x).le)]
        exact hC x))
  ((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2) (hv.toLp v)

private theorem weightChange_ae (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x) (C : ℝ) (hC : ∀ x, f x / g x ≤ C) (u : LogL2) :
    (weightChange f g hf hg hfp hgp C hC u : ℝ → ℂ) =ᵐ[volume] fun x => ((f x / g x : ℝ) : ℂ) * u x := by
  let v := fun x : ℝ => ((f x / g x : ℝ) : ℂ)
  have hv : MemLp v ⊤ volume := memLp_top_of_bound
      (Complex.continuous_ofReal.comp (hf.div hg (fun x => (hgp x).ne'))).aestronglyMeasurable C
      (ae_of_all _ (fun x => by
        change ‖((f x / g x : ℝ) : ℂ)‖ ≤ C
        rw [Complex.norm_of_nonneg (div_nonneg (hfp x).le (hgp x).le)]
        exact hC x))
  have hw := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hv.toLp v) u
  refine hw.trans ?_
  filter_upwards [hv.coeFn_toLp] with x hx
  change hv.toLp v x * u x = v x * u x
  rw [hx]

def paperForward (p : ℝ) (hp : 1/2 < p) := weightChange (paperWeight p) (logWeight p)
  (paperWeight_cont p) (continuous_logWeight p) (paperWeight_pos p) (logWeight_pos p) _ (weightRatio_upper (by linarith))
def paperBackward (p : ℝ) (hp : 1/2 < p) := weightChange (logWeight p) (paperWeight p)
  (continuous_logWeight p) (paperWeight_cont p) (logWeight_pos p) (paperWeight_pos p) _ (weightRatio_lower (by linarith))

theorem paperForward_ae (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    (paperForward p hp u : ℝ → ℂ) =ᵐ[volume] fun x => ((paperWeight p x / logWeight p x : ℝ) : ℂ) * u x :=
  weightChange_ae _ _ _ _ _ _ _ _ _
theorem paperBackward_ae (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    (paperBackward p hp u : ℝ → ℂ) =ᵐ[volume] fun x => ((logWeight p x / paperWeight p x : ℝ) : ℂ) * u x :=
  weightChange_ae _ _ _ _ _ _ _ _ _

theorem paper_backward_forward (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    paperBackward p hp (paperForward p hp u) = u := by
  apply Lp.ext
  filter_upwards [paperBackward_ae p hp (paperForward p hp u), paperForward_ae p hp u] with x hx hy
  rw [hx,hy,Complex.ofReal_div,Complex.ofReal_div]
  field_simp [(logWeight_pos p x).ne', (paperWeight_pos p x).ne']

def paperShift (p : ℝ) (hp : 1/2 < p) (y : ℝ) : LogL2 →L[ℂ] LogL2 :=
  (paperForward p hp).comp ((weightedTranslation p (by linarith) y).comp (paperBackward p hp))

theorem paperShift_ae (p : ℝ) (hp : 1/2 < p) (y : ℝ) (u : LogL2) :
    (paperShift p hp y u : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      ((paperWeight p x / paperWeight p (x+y) : ℝ) : ℂ) * u (x+y) := by
  have hs := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp (paperBackward_ae p hp u)
  filter_upwards [paperForward_ae p hp (weightedTranslation p (by linarith) y (paperBackward p hp u)),
    weightedTranslation_apply_ae p (by linarith) y (paperBackward p hp u), hs] with x hx ht hb
  change paperForward p hp (weightedTranslation p (by linarith) y (paperBackward p hp u)) x = _
  change paperBackward p hp u (x+y) = _ at hb
  rw [hx,ht,hb]
  change _ * (_ * ((((logWeight p (x+y) / paperWeight p (x+y)) : ℝ) : ℂ) * u (x+y))) = _
  simp only [Complex.ofReal_div]
  field_simp [(logWeight_pos p x).ne',(logWeight_pos p (x+y)).ne',(paperWeight_pos p (x+y)).ne']

theorem paperShift_continuous (p : ℝ) (hp : 1/2 < p) (u : LogL2) :
    Continuous (fun y => paperShift p hp y u) :=
  (paperForward p hp).continuous.comp (continuous_weightedTranslation_orbit p (by linarith) (paperBackward p hp u))

theorem paperShift_bound (p : ℝ) (hp : 1/2 < p) (y : ℝ) :
    ‖paperShift p hp y‖ ≤ (‖paperForward p hp‖ * ‖paperBackward p hp‖) * (1+|y|)^⌈p⌉₊ := by
  have hw : ‖weightedTranslation p (by linarith) y‖ ≤ (1+|y|)^⌈p⌉₊ := by
    apply (norm_weightedTranslation_le p (by linarith) y).trans
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (Nat.le_ceil p)
  calc
    _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖paperForward p hp‖ * (‖weightedTranslation p (by linarith) y‖ * ‖paperBackward p hp‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc, mul_comm ‖paperBackward p hp‖]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw (norm_nonneg _)) (norm_nonneg _)

end
end LocalRH
end

section
open MeasureTheory Filter LocalRH
open scoped SchwartzMap FourierTransform Topology
noncomputable section
namespace MasulloSynthesis

def ambientMode (p : ℝ) (hp : 1/2 < p) (ξ : ℝ) : H :=
  paperForward p hp (weightedExponential p (-2*Real.pi*ξ) hp)

theorem ambientMode_ae (p : ℝ) (hp : 1/2 < p) (ξ : ℝ) :
    (ambientMode p hp ξ : ℝ → ℂ) =ᵐ[volume] fun x =>
      weight (-p/2) x * Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I) := by
  filter_upwards [paperForward_ae p hp (weightedExponential p (-2*Real.pi*ξ) hp),
    (weightedExponential_memLp p (-2*Real.pi*ξ) hp).coeFn_toLp] with x hx hu
  change paperForward p hp (weightedExponential p (-2*Real.pi*ξ) hp) x = _
  rw [hx]
  change weightedExponential p (-2*Real.pi*ξ) hp x = _ at hu
  rw [hu,Complex.ofReal_div]
  change _ * ((logWeight p x : ℂ) * angularCharacter _ _) =
    (paperWeight p x : ℂ) * Complex.exp _
  have he : angularCharacter (-2*Real.pi*ξ) x = Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I) := by
    unfold angularCharacter
    push_cast
    congr 1; ring
  rw [he]
  field_simp [(logWeight_pos p x).ne']

theorem ambientMode_dense (p : ℝ) (hp : 1/2 < p) :
    Dense (Submodule.span ℂ (Set.range (ambientMode p hp)) : Set H) := by
  have hd := all_modes_total (weight (-p/2)) (ae_of_all volume fun x =>
    (Complex.ofReal_ne_zero.mpr (paperWeight_pos p x).ne')) (ambientMode p hp) (ambientMode_ae p hp)
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,hd]
  rfl

theorem ambientMode_shift (p : ℝ) (hp : 1/2 < p) (ξ y : ℝ) :
    paperShift p hp y (ambientMode p hp ξ) =
      Complex.exp (↑(-2*Real.pi*y*ξ)*Complex.I) • ambientMode p hp ξ := by
  simp only [ambientMode,paperShift,ContinuousLinearMap.comp_apply,paper_backward_forward,
    weightedTranslation_exponential,map_smul]
  congr 1
  unfold angularCharacter
  push_cast
  congr 1; ring

theorem ambient_localizes_integral (p : ℝ) (hp : 1/2 < p) (b : 𝓢(ℝ,ℂ)) :
    ∃ A : H →L[ℂ] H, (∀ u, A u = ∫ y : ℝ, (𝓕⁻ (b:ℝ→ℂ)) y • paperShift p hp y u) ∧
    ∀ u, logDistribution p (A u) =
      TemperedDistribution.smulLeftCLM ℂ b (logDistribution p u) := by
  obtain ⟨A,hA,_,hmode⟩ := makeFrequencyOperator (paperShift p hp) ⌈p⌉₊
    (‖paperForward p hp‖ * ‖paperBackward p hp‖) (by positivity) (paperShift_continuous p hp)
    (paperShift_bound p hp) b
  refine ⟨A,hA,logDistribution_intertwines p (ambientMode p hp) id (ambientMode_dense p hp)
    (fun ξ => logDistribution_mode p ξ _ (ambientMode_ae p hp ξ)) A b ?_⟩
  exact fun ξ => hmode ξ _ (ambientMode_shift p hp ξ)

end MasulloSynthesis
end
end

section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace LocalRH
noncomputable section

/-- Translation on the logarithmic scale is induced by normalized dilation of admissible tests. -/
theorem thetaLog_translation (g : 𝓢(ℝ,ℂ)) (hg : g 0 = 0) (hI : (∫ t : ℝ, g t) = 0)
    (a : ℝ) :
    ∃ h : 𝓢(ℝ,ℂ), h 0 = 0 ∧ (∫ t : ℝ, h t) = 0 ∧
      (∀ t : ℝ, h t = (Real.exp (a/2):ℂ) * g (Real.exp a * t)) ∧
      (∀ x : ℝ, (Real.exp (x/2):ℂ) * ∑' n : ℤ, h ((n:ℝ) * Real.exp x) =
        (Real.exp ((x+a)/2):ℂ) * ∑' n : ℤ, g ((n:ℝ) * Real.exp (x+a))) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 (Real.exp a) (Real.exp_pos a).ne')
  let h := (Real.exp (a/2):ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e g
  have hh (t : ℝ) : h t = (Real.exp (a/2):ℂ) * g (Real.exp a * t) := rfl
  refine ⟨h, by simp [hh,hg], ?_, hh, ?_⟩
  · simp only [hh,integral_const_mul,Measure.integral_comp_mul_left,hI,smul_zero,mul_zero]
  · intro x
    simp only [hh,tsum_mul_left,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
    rw [show x/2 + a/2 = (x+a)/2 by ring, Real.exp_add x a]
    congr 1
    apply tsum_congr
    intro n
    congr 1
    ring
/-- Each translate of a normalized admissible theta profile is exactly another such profile. -/
theorem thetaLog_shift_image (g : 𝓢(ℝ,ℂ)) (hg : g 0 = 0) (hI : (∫ t : ℝ, g t) = 0)
    (y : ℝ) :
    ∃ h : 𝓢(ℝ,ℂ), h 0 = 0 ∧ (∫ t : ℝ, h t) = 0 ∧
      (∀ t : ℝ, h t = (Real.exp (-y/2):ℂ) * g (Real.exp (-y) * t)) ∧
      (∀ x : ℝ, (Real.exp (x/2):ℂ) * ∑' n : ℤ, h ((n:ℝ) * Real.exp x) =
        (Real.exp ((x-y)/2):ℂ) * ∑' n : ℤ, g ((n:ℝ) * Real.exp (x-y))) := by
  simpa only [sub_eq_add_neg] using thetaLog_translation g hg hI (-y)
end
end LocalRH
end

section
open LocalRH MeasureTheory Filter FourierTransform
open scoped SchwartzMap FourierTransform Topology
noncomputable section
namespace MasulloSynthesis

def rawTheta (g : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ :=
  (Real.exp (x/2):ℂ) * ∑' n : ℤ, g ((n:ℝ)*Real.exp x)

def physicalPair (p : ℝ) (u : H) (f : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, (weight (p/2) x * f x) * u x

theorem physicalPair_schwartz (p : ℝ) (u : H) (f : 𝓢(ℝ,ℂ)) :
    physicalPair p u f = logDistribution p u (𝓕 f) := by
  simp only [physicalPair,logDistribution_apply,fourierInv_fourier_eq]

theorem physicalPair_shift (p : ℝ) (hp : 1/2<p) (y : ℝ) (u : H) (f : ℝ→ℂ) :
    physicalPair p (paperShift p hp y u) f = physicalPair p u (fun x => f (x-y)) := by
  let F (t : ℝ) := (weight (p/2) t * f (t-y)) * u t
  calc
    _ = ∫ x : ℝ, F (x+y) := by
      apply integral_congr_ae
      filter_upwards [paperShift_ae p hp y u] with x hx
      simp only [F,add_sub_cancel_right,hx]
      have hw (t : ℝ) : weight (p/2) t * (paperWeight p t : ℂ) = 1 := by
        change weight (p/2) t * weight (-p/2) t = 1
        rw [weight_mul,show p/2 + -p/2 = 0 by ring]
        simp [weight]
      rw [Complex.ofReal_div]
      field_simp [(paperWeight_pos p (x+y)).ne']
      linear_combination (norm := ring_nf) f x * u (x+y) * (hw x - hw (x+y))
    _ = _ := integral_add_right_eq_self F y

def allThetaAnn (p : ℝ) (u : H) : Prop :=
  ∀ g : 𝓢(ℝ,ℂ), g 0 = 0 → (∫ x : ℝ, g x) = 0 → physicalPair p u (rawTheta g) = 0

theorem allThetaAnn_shift (p : ℝ) (hp : 1/2<p) {u : H} (hu : allThetaAnn p u) (y : ℝ) :
    allThetaAnn p (paperShift p hp y u) := by
  intro g hg hI
  obtain ⟨h,hh,hJ,_,he⟩ := thetaLog_shift_image g hg hI y
  rw [physicalPair_shift p hp]
  exact (congrArg (physicalPair p u) (funext he)).symm.trans (hu h hh hJ)

theorem multiplier_preserves_allThetaAnn (p : ℝ) (hp : 1/2<p) {u : H} (hu : allThetaAnn p u)
    (b : 𝓢(ℝ,ℂ)) (A : H →L[ℂ] H)
    (hA : ∀ v, A v = ∫ y : ℝ, (𝓕⁻ (b:ℝ→ℂ)) y • paperShift p hp y v) :
    allThetaAnn p (A u) := by
  intro g hg hI
  obtain ⟨_,T,hT,_,_⟩ := rational_theta_test_factorization g hg hI
  have hT' : (T:ℝ→ℂ) = rawTheta g := funext hT
  rw [←hT',physicalPair_schwartz]
  let L := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ (𝓕 T)).comp (logDistribution p)
  change L (A u) = 0
  let F := fun y : ℝ => (𝓕⁻ (b:ℝ→ℂ)) y • paperShift p hp y u
  rw [hA]
  change L (∫ y : ℝ, F y) = 0
  by_cases h : Integrable F
  · rw [← L.integral_comp_comm h]
    apply integral_eq_zero_of_ae
    apply Eventually.of_forall
    intro y
    have ht := allThetaAnn_shift p hp hu y g hg hI
    rw [← hT',physicalPair_schwartz] at ht
    change L (paperShift p hp y u) = 0 at ht
    simp only [F,map_smul,ht,smul_zero]
    rfl
  · rw [integral_undef h,map_zero]

theorem ann_implies_principal (p : ℝ) (hp : 1/2<p) {u : H} (hu : allThetaAnn p u)
    (g : 𝓢(ℝ,ℂ)) (hg : g 0 = 0) (hI : (∫ x : ℝ, g x) = 0)
    (T : 𝓢(ℝ,ℂ)) (hT : ∀ x, T x = rawTheta g x) (q : 𝓢(ℝ,ℂ)) :
    ∫ x : ℝ, (weight (p/2) x * (𝓕⁻ (fun t : ℝ => (𝓕 T) t * q t)) x) * u x = 0 := by
  obtain ⟨A,hA,hD⟩ := ambient_localizes_integral p hp q
  have h := multiplier_preserves_allThetaAnn p hp hu q A hA g hg hI
  rw [← show (T:ℝ→ℂ) = rawTheta g from funext hT,physicalPair_schwartz,hD,
    TemperedDistribution.smulLeftCLM_apply_apply,logDistribution_apply,SchwartzMap.fourierInv_coe] at h
  have hcoe : (⇑(SchwartzMap.smulLeftCLM ℂ q (𝓕 T)) : ℝ→ℂ) = fun t : ℝ => (𝓕 T) t * q t := by
    funext t
    rw [SchwartzMap.smulLeftCLM_apply_apply q.hasTemperateGrowth]
    exact mul_comm _ _
  simpa only [hcoe] using h

end MasulloSynthesis
end
end

section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Exact parameter change between normalized Fourier frequency and the angular
frequency of a critical-line zero. Equality of the natural orders suffices. -/
theorem admissible_frequency_set_eq_critical_jet_set (p : ℝ) (G : ℝ → ℂ)
    (horder : ∀ ν : ℝ, analyticOrderNatAt G ν =
      analyticOrderNatAt riemannZeta ((1/2:ℂ) - 2*Real.pi*Complex.I*(ν:ℂ))) :
    {v : Lp ℂ 2 (volume : Measure ℝ) | ∃ (ν : ℝ) (r : ℕ),
      G ν = 0 ∧ r < analyticOrderNatAt G ν ∧ (r:ℝ)+1/2<p ∧
      (v : ℝ→ℂ) =ᵐ[volume] (fun x : ℝ => (↑((1+x^2)^(-p/2) : ℝ) : ℂ) *
        ((x:ℂ)^r * Complex.exp (↑(-2*Real.pi*x*ν)*Complex.I)))} =
    {v : Lp ℂ 2 (volume : Measure ℝ) |
      ∃ (ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}) (r : ℕ),
        r < analyticOrderNatAt riemannZeta ρ.val ∧ (r:ℝ)+1/2<p ∧
        (v : ℝ→ℂ) =ᵐ[volume] fun x : ℝ =>
          ((1+x^2)^(-p/2) : ℝ) * ((x:ℂ)^r * Complex.exp (↑(ρ.val.im*x)*Complex.I))} := by
  let L (ν : ℝ) : ℂ := 1/2 - 2*Real.pi*Complex.I*(ν:ℂ)
  have hRe (ν : ℝ) : (L ν).re = 1/2 := by simp [L,Complex.mul_re,Complex.mul_im]
  have hIm (ν : ℝ) : (L ν).im = -2*Real.pi*ν := by simp [L,Complex.mul_re,Complex.mul_im]
  have hphase (ν x : ℝ) : -2*Real.pi*x*ν = (L ν).im*x := by rw [hIm]; ring
  ext v
  constructor
  · rintro ⟨ν,r,_,hr,hp,hv⟩
    have hr' : r < analyticOrderNatAt riemannZeta (L ν) := (horder ν) ▸ hr
    let ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2} :=
      ⟨L ν,apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_zero_of_lt hr'),hRe ν⟩
    refine ⟨ρ,r,hr',hp,hv.trans (Eventually.of_forall fun x => ?_)⟩
    dsimp only
    rw [hphase ν x]
  · rintro ⟨ρ,r,hr,hp,hv⟩
    let ν : ℝ := -ρ.val.im/(2*Real.pi)
    have hL : L ν = ρ.val := by
      apply Complex.ext
      · rw [hRe,ρ.prop.2]
      · rw [hIm]
        dsimp [ν]
        field_simp [Real.pi_ne_zero]
    have hr' : r < analyticOrderNatAt G ν := by rw [horder, show (1/2:ℂ) - 2*Real.pi*Complex.I*(ν:ℂ) = ρ.val from hL]; exact hr
    refine ⟨ν,r,apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_zero_of_lt hr'),hr',hp,
      hv.trans (Eventually.of_forall fun x => ?_)⟩
    dsimp only
    rw [hphase ν x,hL]
end

section
open MeasureTheory Set Filter Bornology
open scoped Polynomial FourierTransform SchwartzMap
namespace LocalRH.JetAdmissibility
noncomputable section

def weight (p x : ℝ) : ℂ := ((1+x^2)^(-p/2) : ℝ)
def phase (ν x : ℝ) : ℂ := Complex.exp (↑(-2 * Real.pi * (ν*x)) * Complex.I)
def mode (p ν : ℝ) (P : ℂ[X]) (x : ℝ) : ℂ := weight p x * (P.eval (x:ℂ) * phase ν x)

theorem weight_ne (p x : ℝ) : weight p x ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne'

end
end LocalRH.JetAdmissibility
end

section
open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform Polynomial ContDiff
namespace LocalRH.JetAdmissibility
noncomputable section

private theorem kernel_moment_eq_jet (b : 𝓢(ℝ,ℂ)) (r : ℕ) (ξ : ℝ) :
    iteratedDeriv r b ξ = ((-2:ℂ) * Real.pi * Complex.I)^r *
      ∫ t : ℝ, (t:ℂ)^r * Complex.exp ((↑(-2 * Real.pi * (ξ*t)) : ℂ) * Complex.I) *
        (𝓕⁻ (b : ℝ → ℂ)) t := by
  let f : 𝓢(ℝ,ℂ) := 𝓕⁻ b
  have hi (a : ℕ) : Integrable (fun t : ℝ => t^a • f t) := by
    apply (f.integrable_pow_mul volume a).mono' (by fun_prop)
    exact Eventually.of_forall fun t => by simp
  have h := congrFun (Real.iteratedDeriv_fourier (f:=(f:ℝ→ℂ)) (N:=(r:ℕ∞))
    (fun a _ => hi a) (le_rfl : (r:ℕ∞) ≤ r)) ξ
  have he : 𝓕 (f:ℝ→ℂ) = (b:ℝ→ℂ) := by
    rw [← SchwartzMap.fourier_coe]
    simp [f]
  rw [he, Real.fourier_eq'] at h
  rw [← integral_const_mul]
  change iteratedDeriv r b ξ = ∫ t : ℝ, _ * (_ * _ * ((𝓕⁻ (b:ℝ→ℂ)) t))
  apply h.trans
  apply integral_congr_ae
  refine Eventually.of_forall fun t => ?_
  simp only [Real.inner_apply, smul_eq_mul, ← SchwartzMap.fourierInv_coe]
  dsimp [f]
  rw [mul_pow]
  rw [mul_comm t ξ]
  ring

abbrev JetL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Conversion from derivatives of the frequency test to physical-space monomials. -/
def momentFactor : ℂ := (-2:ℂ)*Real.pi*Complex.I

theorem momentFactor_ne : momentFactor ≠ 0 := by
  unfold momentFactor
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

theorem integral_of_mode (p ν : ℝ) (r : ℕ) (u : JetL2)
    (hu : (u : ℝ→ℂ) =ᵐ[volume] mode p ν (Polynomial.X^r)) (f : 𝓢(ℝ,ℂ)) :
    ∫ x : ℝ, (u x / weight p x) * (𝓕⁻ (f:ℝ→ℂ)) x =
      iteratedDeriv r f ν / momentFactor^r := by
  apply (eq_div_iff (pow_ne_zero _ momentFactor_ne)).mpr
  rw [kernel_moment_eq_jet, mul_comm _ (momentFactor^r)]
  apply congrArg (momentFactor^r * ·)
  apply integral_congr_ae
  filter_upwards [hu] with x hx
  rw [hx, mode, Polynomial.eval_pow, Polynomial.eval_X]
  field_simp [weight_ne p x]
  unfold phase
  ring_nf

end
end LocalRH.JetAdmissibility
end

section
open MeasureTheory Filter
open scoped Polynomial SchwartzMap FourierTransform
namespace MasulloSynthesis
noncomputable section
open LocalRH.JetAdmissibility

theorem logDistribution_eq_unweighted_integral (p : ℝ) (u : H) (f : 𝓢(ℝ,ℂ)) :
    logDistribution p u f = ∫ x : ℝ, (u x / LocalRH.JetAdmissibility.weight p x) * (𝓕⁻ (f:ℝ→ℂ)) x := by
  rw [logDistribution_apply, ← SchwartzMap.fourierInv_coe]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hw : weight (p/2) x * LocalRH.JetAdmissibility.weight p x = 1 := by
    change weight (p/2) x * weight (-p/2) x = 1
    rw [weight_mul, show p/2 + -p/2 = 0 by ring]
    simp [weight]
  field_simp [LocalRH.JetAdmissibility.weight_ne p x]
  linear_combination ((𝓕⁻ f) x * u x) * hw

theorem logDistribution_jet (p ν : ℝ) (r : ℕ) (u : H)
    (hu : (u : ℝ→ℂ) =ᵐ[volume] fun x : ℝ => weight (-p/2) x *
      ((x:ℂ)^r * Complex.exp (↑(-2*Real.pi*x*ν) * Complex.I))) (f : 𝓢(ℝ,ℂ)) :
    logDistribution p u f = iteratedDeriv r f ν / ((-2:ℂ)*Real.pi*Complex.I)^r := by
  rw [logDistribution_eq_unweighted_integral]
  apply integral_of_mode
  refine hu.trans (ae_of_all _ fun x => ?_)
  simp only [mode, phase, LocalRH.JetAdmissibility.weight, weight, Polynomial.eval_pow, Polynomial.eval_X,
    mul_assoc, mul_comm ν]

end
end MasulloSynthesis
end

section
open MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform


open MasulloSynthesis FourierTransform
open scoped FourierTransform

theorem annihilates_theta_of_critical_jet_span
    (p : ℝ) (u : H)
    (hu : u ∈ (Submodule.span ℂ {v : H |
      ∃ (ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}) (r : ℕ),
        r < analyticOrderNatAt riemannZeta ρ.val ∧ (r:ℝ)+1/2<p ∧
        (v : ℝ→ℂ) =ᵐ[volume] fun x : ℝ =>
          ((1+x^2)^(-p/2) : ℝ) * ((x:ℂ)^r * Complex.exp (↑(ρ.val.im*x)*Complex.I))}).topologicalClosure)
    (g Θ : 𝓢(ℝ,ℂ))
    (hΘ : ∀ x : ℝ, Θ x = (Real.exp (x/2):ℂ) * ∑' n : ℤ, g ((n:ℝ)*Real.exp x))
    (hF : ∀ ν : ℝ, (𝓕 Θ) ν = mellin (fun a : ℝ => ∑' n : ℤ, g ((n:ℝ)*a))
      (1/2+((-2*Real.pi:ℝ):ℂ)*Complex.I*(ν:ℂ)))
    (hM : ∀ ν : ℝ, ∀ r < analyticOrderNatAt riemannZeta (1/2+((-2*Real.pi:ℝ):ℂ)*Complex.I*(ν:ℂ)),
      iteratedDeriv r (fun t : ℝ => mellin (fun a : ℝ => ∑' n : ℤ, g ((n:ℝ)*a))
        (1/2+((-2*Real.pi:ℝ):ℂ)*Complex.I*(t:ℂ))) ν = 0) :
    ∫ x : ℝ, ((↑((1+x^2)^(p/2) : ℝ) : ℂ) *
      ((Real.exp (x/2):ℂ) * ∑' n : ℤ, g ((n:ℝ)*Real.exp x))) * u x = 0 := by
  let Z := {v : H |
      ∃ (ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}) (r : ℕ),
        r < analyticOrderNatAt riemannZeta ρ.val ∧ (r:ℝ)+1/2<p ∧
        (v : ℝ→ℂ) =ᵐ[volume] fun x : ℝ =>
          ((1+x^2)^(-p/2) : ℝ) * ((x:ℂ)^r * Complex.exp (↑(ρ.val.im*x)*Complex.I))}
  let test : 𝓢(ℝ,ℂ) := 𝓕 Θ
  let L := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp (logDistribution p)
  have hsub : Submodule.span ℂ Z ≤ LinearMap.ker L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro v ⟨ρ,r,hr,_,hv⟩
    let ν : ℝ := -ρ.val.im/(2*Real.pi)
    have hz : (1/2:ℂ)+((-2*Real.pi:ℝ):ℂ)*Complex.I*(ν:ℂ) = ρ.val := by
      apply Complex.ext
      · simp [Complex.mul_re,Complex.mul_im,ρ.prop.2]
      · have hi (a : ℝ) : ((1/2:ℂ)+((-2*Real.pi:ℝ):ℂ)*Complex.I*(a:ℂ)).im = -2*Real.pi*a := by
          simp [Complex.mul_re,Complex.mul_im]
        rw [hi]
        dsimp [ν]
        field_simp [Real.pi_ne_zero]
    have hv' : (v : ℝ→ℂ) =ᵐ[volume] fun x : ℝ => weight (-p/2) x *
        ((x:ℂ)^r*Complex.exp (↑(-2*Real.pi*x*ν)*Complex.I)) := by
      refine hv.trans (Eventually.of_forall fun x => ?_)
      have hphase : ρ.val.im*x = -2*Real.pi*x*ν := by dsimp [ν]; field_simp [Real.pi_ne_zero]
      simp only [hphase, weight]
    change logDistribution p v test = 0
    rw [logDistribution_jet p ν r v hv']
    have htest : (test:ℝ→ℂ) = _ := funext hF
    rw [htest,hM ν r (hz.symm ▸ hr),zero_div]
  have hu' : logDistribution p u test = 0 :=
    (Submodule.span ℂ Z).topologicalClosure_minimal hsub L.isClosed_ker hu
  simpa only [logDistribution_apply,test,fourierInv_fourier_eq,hΘ,weight] using hu'
end

section
open LocalRH MasulloSynthesis MeasureTheory Filter FourierTransform
open scoped SchwartzMap FourierTransform Topology
noncomputable section

private theorem zetaFiniteOnLine (t : ℝ) :
    analyticOrderAt riemannZeta (1/2+((-2*Real.pi:ℝ):ℂ)*Complex.I*(t:ℂ)) ≠ ⊤ := by
  let z : ℂ := 1/2+((-2*Real.pi:ℝ):ℂ)*Complex.I*(t:ℂ)
  have h1 : z ∈ ({1}:Set ℂ)ᶜ := by
    intro h
    have hh := congrArg Complex.re (show z=1 from h)
    norm_num [z,Complex.mul_re,Complex.mul_im] at hh
  have htwo : analyticOrderAt riemannZeta (2:ℂ) = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  exact analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)

theorem allThetaAnn_iff_jet_span (p : ℝ) (hp : 1/2<p) (u : H) :
    allThetaAnn p u ↔
    u ∈ (Submodule.span ℂ {v : H |
      ∃ (ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}) (r : ℕ),
        r < analyticOrderNatAt riemannZeta ρ.val ∧ (r:ℝ)+1/2<p ∧
        (v : ℝ→ℂ) =ᵐ[volume] fun x : ℝ =>
          ((1+x^2)^(-p/2) : ℝ) * ((x:ℂ)^r * Complex.exp (↑(ρ.val.im*x)*Complex.I))}).topologicalClosure := by
  constructor
  · intro hu
    obtain ⟨g,_,hg,hI,_,horder⟩ := _root_.MasulloRH.dyadic_gaussian_theta_mellin
    obtain ⟨_,T,hT,hF,hZ⟩ := rational_theta_test_factorization g hg hI
    let G : ℝ → ℂ := fun t => (𝓕 T : 𝓢(ℝ,ℂ)) t
    let σ (t : ℝ) : ℂ := 1/2+((-2*Real.pi:ℝ):ℂ)*Complex.I*(t:ℂ)
    have he : G = fun t => mellin (fun y : ℝ => ∑' n : ℤ, g ((n:ℝ)*y)) (σ t) := funext hF
    have ho (ν : ℝ) : analyticOrderAt G ν = analyticOrderAt riemannZeta (σ ν) := he ▸ horder ν
    have hfin (ν : ℝ) : analyticOrderAt G ν ≠ ⊤ := (ho ν) ▸ zetaFiniteOnLine ν
    have hn (ν : ℝ) : analyticOrderNatAt G ν =
        analyticOrderNatAt riemannZeta ((1/2:ℂ) - 2*Real.pi*Complex.I*(ν:ℂ)) := by
      have hs : σ ν = (1/2:ℂ)-2*Real.pi*Complex.I*(ν:ℂ) := by
        dsimp [σ]
        push_cast
        ring
      rw [←hs]
      exact congrArg ENat.toNat (ho ν)
    rw [← admissible_frequency_set_eq_critical_jet_set p G hn]
    apply (_root_.MasulloRH.sobolev_spectral_synthesis p hp G (fun ν => (hZ ν).1) hfin u).mp
    exact fun q _ => ann_implies_principal p hp hu g hg hI T hT q
  · intro hu g hg hI
    obtain ⟨_,T,hT,hF,hZ⟩ := rational_theta_test_factorization g hg hI
    apply annihilates_theta_of_critical_jet_span p u hu g T hT hF
    intro ν r hr
    rw [← funext hF]
    exact (hZ ν).2.2 r hr
end
end

section
open MeasureTheory Filter
open scoped InnerProductSpace SchwartzMap
namespace LocalRH
noncomputable section

private def thetaPairingProfile (p : ℝ) (g : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ :=
  ((↑((1+x^2)^(p/2) : ℝ)):ℂ) * ((Real.exp (x/2):ℂ) * ∑' n : ℤ, g ((n:ℝ)*Real.exp x))

private theorem thetaPairingProfile_memLp (p : ℝ) (g : 𝓢(ℝ,ℂ)) (hg : g 0 = 0)
    (hI : (∫ t : ℝ, g t) = 0) : MemLp (thetaPairingProfile p g) 2 volume := by
  obtain ⟨Θ,hΘ,_,_⟩ := (rational_theta_test_factorization g hg hI).2
  let w (x : ℝ) : ℂ := ((1+x^2)^(p/2) : ℝ)
  have hw : w.HasTemperateGrowth := by
    have h := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (p/2)
    simpa only [w, Function.comp_def, Complex.ofRealCLM_apply, Real.norm_eq_abs, sq_abs] using
      Complex.ofRealCLM.hasTemperateGrowth.comp h
  let t := SchwartzMap.smulLeftCLM ℂ w Θ
  have ht : (t : ℝ → ℂ) = thetaPairingProfile p g := by
    funext x
    rw [SchwartzMap.smulLeftCLM_apply_apply hw Θ, hΘ]
    rfl
  rw [← ht]
  exact t.memLp 2 volume

private theorem inner_thetaPairingProfile (p : ℝ) (g : 𝓢(ℝ,ℂ))
    (v u : Lp ℂ 2 (volume : Measure ℝ))
    (hv : (v:ℝ→ℂ) =ᵐ[volume] fun x => (starRingEnd ℂ) (thetaPairingProfile p g x)) :
    ⟪v,u⟫_ℂ = ∫ x : ℝ, thetaPairingProfile p g x * u x := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  simp [RCLike.inner_apply, hx, mul_comm]

theorem rationalThetaAnnihilator_mem_iff (p : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    u ∈ rationalThetaAnnihilator p ↔
    ∀ g : 𝓢(ℝ,ℂ), g 0 = 0 → (∫ t : ℝ, g t) = 0 →
      ∫ x : ℝ, (((↑((1+x^2)^(p/2) : ℝ)):ℂ) *
        ((Real.exp (x/2):ℂ) * ∑' n : ℤ, g ((n:ℝ)*Real.exp x))) * u x = 0 := by
  rw [rationalThetaAnnihilator, Submodule.mem_orthogonal]
  constructor
  · intro h g hg hI
    have hm := (thetaPairingProfile_memLp p g hg hI).star
    let v := hm.toLp (star (thetaPairingProfile p g))
    have hv : (v:ℝ→ℂ) =ᵐ[volume] fun x => (starRingEnd ℂ) (thetaPairingProfile p g x) :=
      hm.coeFn_toLp
    exact (inner_thetaPairingProfile p g v u hv).symm.trans
      (h v (Submodule.subset_span ⟨g,hg,hI,hv⟩))
  · intro h v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g,hg,hI,he⟩ := hv
      exact (inner_thetaPairingProfile p g v u he).trans (h g hg hI)
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_left,hx,hy]
    | smul a x _ hx => simp [inner_smul_left,hx]
end
end LocalRH
end

end ThetaRealProof

open ThetaRealProof ThetaRealProof.LocalRH MeasureTheory MasulloRH MasulloGRH
open scoped InnerProductSpace

theorem solution (p : ℝ) (hp : 1/2<p) :
    let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}
    let H := Lp ℂ 2 (volume : Measure ℝ)
    rationalThetaAnnihilator p =
      (Submodule.span ℂ {u : H | ∃ (ρ : Z) (r : ℕ),
        r < analyticOrderNatAt riemannZeta ρ.val ∧ (r:ℝ)+1/2 < p ∧
        (u : ℝ→ℂ) =ᵐ[volume] fun x : ℝ => ((1+x^2)^(-p/2) : ℝ) *
          ((x:ℂ)^r * Complex.exp (↑(ρ.val.im*x)*Complex.I))}).topologicalClosure ∧
    ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      ∃! T : rationalThetaAnnihilator p →L[ℂ] rationalThetaAnnihilator p,
        IsRationalThetaConvolution p φ T ∧ IsNuclearOperator T ∧
          HasSum (fun ρ : Z =>
            ((min (analyticOrderNatAt riemannZeta ρ.val) ⌈p-1/2⌉₊ : ℕ) : ℂ) *
              mellin φ (ρ.val-1/2)) (operatorTrace T) := by
  dsimp only
  have he : rationalThetaAnnihilator p = _ := Submodule.ext fun u =>
    (rationalThetaAnnihilator_mem_iff p u).trans (allThetaAnn_iff_jet_span p hp u)
  refine ⟨he,fun φ hφ => ?_⟩
  unfold IsRationalThetaConvolution
  generalize hc : rationalThetaAnnihilator_completeSpace p = hC
  clear hc
  revert hC
  rw [he]
  intro hC
  exact critical_line_jet_convolution_trace p hp φ hφ
