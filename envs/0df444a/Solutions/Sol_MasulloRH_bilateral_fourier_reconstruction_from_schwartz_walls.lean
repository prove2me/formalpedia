-- Prove2me | solution 1 for MasulloRH.bilateral_fourier_reconstruction_from_schwartz_walls
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T04:05:43.379486+00:00
-- url     : https://prove2.me/submissions/2ac976fa-6d45-4a46-bcc2-9d036bdfd9c7

import Mathlib

-- Local source: SynthWallYoung
section StandaloneSynthWallYoung
open Set MeasureTheory Filter
open scoped Topology Convolution SchwartzMap
namespace MasulloRH.SynthWall
noncomputable section

def conv (k f : ℝ→ℂ) : ℝ→ℂ := k ⋆[ContinuousLinearMap.mul ℂ ℂ] f

lemma weighted_cauchy (a v : ℝ→ℝ) (ha : ∀ t,0≤a t) (hv : ∀t,0≤v t)
    (hA : Integrable a) (hV : AEStronglyMeasurable v)
    (hI : Integrable (fun t=>a t*(v t)^2)) :
    Integrable (fun t=>a t*v t) ∧ (∫t,a t*v t)^2 ≤ (∫t,a t)*(∫t,a t*(v t)^2) := by
  let f (t : ℝ) := Real.sqrt (a t)
  let g (t : ℝ) := f t*v t
  have hfm : AEStronglyMeasurable f := Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hfsq t : (f t)^2=a t := Real.sq_sqrt (ha t)
  have hgsq t : (g t)^2=a t*(v t)^2 := by dsimp only [g]; rw [mul_pow,hfsq]
  have hfg t : f t*g t=a t*v t := by dsimp only [g]; rw [←mul_assoc,←sq,hfsq]
  have hf : MemLp f 2 := (memLp_two_iff_integrable_sq hfm).mpr (by simpa only [hfsq] using hA)
  have hgm : AEStronglyMeasurable g := hfm.mul hV
  have hg : MemLp g 2 := (memLp_two_iff_integrable_sq hgm).mpr (by simpa only [hgsq] using hI)
  have hi : Integrable (fun t=>a t*v t) := by
    have hh : Integrable (fun t=>f t*g t) := hf.integrable_mul hg
    simpa only [hfg] using hh
  refine ⟨hi,?_⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ:=volume) (p:=2) (q:=2) (by norm_num [Real.holderConjugate_iff])
    (f:=f) (g:=g) (.of_forall fun t => Real.sqrt_nonneg _) (.of_forall fun t=>mul_nonneg (Real.sqrt_nonneg _) (hv t))
    (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two,←Real.sqrt_eq_rpow,hfg,hfsq,hgsq] at h
  apply ((sq_le_sq₀ (integral_nonneg (fun t => mul_nonneg (ha t) (hv t))) (by positivity)).mpr h).trans_eq
  rw [mul_pow,Real.sq_sqrt (integral_nonneg ha),Real.sq_sqrt (integral_nonneg (fun t=>mul_nonneg (ha t) (sq_nonneg _)))]

/-- Weighted L¹-L² Young inequality for a continuous submultiplicative weight. -/
theorem weighted_young {w : ℝ→ℝ} (hw : Continuous w) (hw0 : ∀x,0≤w x)
    (hwsub : ∀x t,w x≤w t*w (x-t)) {k f : ℝ→ℂ} (hk : Integrable k) (hf : Integrable f)
    (hK : Integrable (fun t=>w t*‖k t‖)) (hF : MemLp (fun t=>w t*‖f t‖) 2 volume) :
    MemLp (fun x=>w x*‖conv k f x‖) 2 volume ∧
      (∫x,(w x*‖conv k f x‖)^2) ≤ (∫t,w t*‖k t‖)^2*(∫t,(w t*‖f t‖)^2) := by
  let K (t : ℝ) := w t*‖k t‖
  let F (t : ℝ) := w t*‖f t‖
  let A := ∫t,K t
  let E (x : ℝ) := ∫t,K t*(F (x-t))^2
  have hK₀ t : 0≤K t := mul_nonneg (hw0 _) (norm_nonneg _)
  have hF₀ t : 0≤F t := mul_nonneg (hw0 _) (norm_nonneg _)
  have hF₂ : Integrable (fun t => (F t)^2) := (memLp_two_iff_integrable_sq hF.1).mp hF
  have hE : Integrable E := hK.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hF₂
  have hEE : (∫ x,E x)=A*(∫t,(F t)^2) := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hK hF₂
  have hmeas : AEStronglyMeasurable (fun x=>w x*‖conv k f x‖) :=
    hw.aestronglyMeasurable.mul ((hk.integrable_convolution _ hf).aestronglyMeasurable.norm)
  have hbound : ∀ᵐ x : ℝ, (w x*‖conv k f x‖)^2 ≤ A*E x := by
    filter_upwards [hK.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hF₂] with x hx
    have hmv : AEStronglyMeasurable (fun t=>F (x-t)) :=
      hF.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
    obtain ⟨hI,hB⟩ := weighted_cauchy K (fun t=>F (x-t)) hK₀ (fun t=>hF₀ _) hK hmv hx
    have hh : w x*‖conv k f x‖ ≤ ∫t,K t*F (x-t) := by
      change w x*‖∫t,k t*f (x-t)‖≤_
      calc
        _ ≤ w x*(∫t,‖k t*f (x-t)‖) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (hw0 _)
        _ = ∫t,w x*‖k t*f (x-t)‖ := (integral_const_mul ..).symm
        _ ≤ _ := by
          apply integral_mono_of_nonneg (.of_forall (fun t=>mul_nonneg (hw0 _) (norm_nonneg _))) hI
          exact .of_forall fun t => by
            dsimp only
            rw [norm_mul]
            apply (mul_le_mul_of_nonneg_right (hwsub x t) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
            dsimp [K,F]; ring
    exact ((sq_le_sq₀ (mul_nonneg (hw0 _) (norm_nonneg _)) (integral_nonneg (fun t=>mul_nonneg (hK₀ _) (hF₀ _)))).mpr hh).trans hB
  have hJ : Integrable (fun x=>(w x*‖conv k f x‖)^2) := by
    apply (hE.const_mul A).mono' (hmeas.pow 2)
    filter_upwards [hbound] with x hx
    change ‖(w x*‖conv k f x‖)^2‖ ≤ A*E x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hx
  refine ⟨(memLp_two_iff_integrable_sq hmeas).mpr hJ,(integral_mono_ae hJ (hE.const_mul A) hbound).trans_eq ?_⟩
  rw [integral_const_mul,hEE]
  change A*(A*_) = A^2*_
  ring

theorem one_abs_submultiplicative (x t : ℝ) : 1+|x| ≤ (1+|t|)*(1+|x-t|) := by
  have h := abs_add_le t (x-t)
  rw [add_sub_cancel] at h
  nlinarith only [h,mul_nonneg (abs_nonneg t) (abs_nonneg (x-t))]

end
end MasulloRH.SynthWall
end StandaloneSynthWallYoung


-- Local source: SynthPowerWeight
section StandaloneSynthPowerWeight
open MeasureTheory Set Filter
open scoped Topology SchwartzMap
namespace MasulloRH.SynthPower
noncomputable section

theorem power_cont (p : ℝ) : Continuous (fun x : ℝ=>(1+|x|)^p) :=
  (show Continuous (fun x : ℝ=>1+|x|) by fun_prop).rpow_const (fun x=>Or.inl (by dsimp; positivity))

theorem power_sub (p : ℝ) (hp : 0≤p) (x y : ℝ) :
    (1+|x|)^p ≤ (1+|y|)^p*(1+|x-y|)^p := by
  rw [←Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity) (SynthWall.one_abs_submultiplicative x y) hp

theorem one_abs_rpow_schwartz (p : ℝ) (k : 𝓢(ℝ,ℂ)) :
    Integrable (fun x : ℝ=>(1+|x|)^p*‖k x‖) := by
  obtain ⟨n,hn⟩ := exists_nat_ge p
  have hi := ((k.integrable.norm).add (k.integrable_pow_mul volume n)).const_mul ((2:ℝ)^n)
  apply hi.mono' ((power_cont p).mul k.continuous.norm).aestronglyMeasurable
  filter_upwards with x
  change ‖(1+|x|)^p*‖k x‖‖≤2^n*(‖k x‖+‖x‖^n*‖k x‖)
  rw [Real.norm_of_nonneg (by positivity),Real.norm_eq_abs,←one_add_mul,←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg x]) hn).trans
  rw [Real.rpow_natCast]
  by_cases h : |x|≤1
  · exact (pow_le_pow_left₀ (by positivity) (show 1+|x|≤2 by linarith) n).trans
      (le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg (abs_nonneg x) n]))
  · calc
      (1+|x|)^n ≤ (2*|x|)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ ≤ _ := by rw [mul_pow]; gcongr; linarith

theorem schwartz_young (p : ℝ) (hp : 0≤p) (k : 𝓢(ℝ,ℂ)) {f : ℝ→ℂ} (hf : Integrable f)
    (hF : MemLp (fun t:ℝ=>(1+|t|)^p*‖f t‖) 2 volume) :
    MemLp (fun t:ℝ=>(1+|t|)^p*‖SynthWall.conv k f t‖) 2 volume :=
  (SynthWall.weighted_young (power_cont p) (fun t=>by positivity)
    (power_sub p hp) k.integrable hf (one_abs_rpow_schwartz p k) hF).1

end
end MasulloRH.SynthPower
end StandaloneSynthPowerWeight


-- Local source: SynthWallContour
section StandaloneSynthWallContour
open Set MeasureTheory Filter
open scoped Topology Interval
namespace MasulloRH.SynthWall
noncomputable section

def vertical (u t : ℝ) : ℂ := (u:ℂ)+(t:ℂ)*Complex.I
@[simp] theorem vertical_re (u t : ℝ) : (vertical u t).re=u := by simp [vertical]
@[simp] theorem vertical_im (u t : ℝ) : (vertical u t).im=t := by simp [vertical]

def closedStrip (b : ℝ) := {z : ℂ | |z.re| ≤ b}
def openStrip (b : ℝ) := {z : ℂ | |z.re| < b}

/-- A common cofinal sequence of horizontal lines where the full segment is small. -/
def GoodHeights (Q : ℂ→ℂ) (b : ℝ) := ∃ T e : ℕ→ℝ, Tendsto T atTop atTop ∧
  Tendsto e atTop (𝓝 0) ∧ ∀ n u, |u|≤b →
    ‖Q (vertical u (T n))‖≤e n ∧ ‖Q (vertical u (-T n))‖≤e n

private lemma horizontal_vanish {F : ℂ→ℂ} {a c b : ℝ} (hac : a≤c) (ha : |a|≤b) (hc : |c|≤b)
    {T e : ℕ→ℝ} (he : Tendsto e atTop (𝓝 0))
    (h : ∀ n u, |u|≤b → ‖F (vertical u (T n))‖≤e n) :
    Tendsto (fun n => ∫ u in a..c,F (vertical u (T n))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _=>norm_nonneg _) (fun n => intervalIntegral.norm_integral_le_of_norm_le_const (C:=e n) ?_) ?_
  · intro u hu
    rw [uIoc_of_le hac] at hu
    exact h n u (abs_le.mpr ⟨(abs_le.mp ha).1.trans hu.1.le,hu.2.trans (abs_le.mp hc).2⟩)
  · simpa using he.mul_const |c-a|

theorem vertical_integrals_eq (Q : ℂ→ℂ) {a c b : ℝ} (hac : a≤c) (ha : |a|≤b) (hc : |c|≤b)
    (hC : ContinuousOn Q (closedStrip b)) (hD : DifferentiableOn ℂ Q (openStrip b))
    (hh : GoodHeights Q b) (hA : Integrable (fun t=>Q (vertical a t)))
    (hB : Integrable (fun t=>Q (vertical c t))) :
    (∫ t : ℝ,Q (vertical a t)) = ∫ t : ℝ,Q (vertical c t) := by
  obtain ⟨T,e,hT,he,h⟩ := hh
  have hrect n :
      (∫ u in a..c,Q (vertical u (-T n))) - (∫ u in a..c,Q (vertical u (T n))) +
        Complex.I * (∫ t in -T n..T n,Q (vertical c t)) -
        Complex.I * (∫ t in -T n..T n,Q (vertical a t)) = 0 := by
    apply Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn Q
      (⟨a,-T n⟩:ℂ) (⟨c,T n⟩:ℂ)
    · apply hC.mono
      intro z hz
      have hz' : z.re ∈ uIcc a c := hz.1
      rw [uIcc_of_le hac] at hz'
      exact abs_le.mpr ⟨(abs_le.mp ha).1.trans hz'.1,hz'.2.trans (abs_le.mp hc).2⟩
    · apply hD.mono
      intro z hz
      have hz' : z.re∈Ioo (min a c) (max a c) := hz.1
      rw [min_eq_left hac,max_eq_right hac] at hz'
      exact abs_lt.mpr ⟨(abs_le.mp ha).1.trans_lt hz'.1,hz'.2.trans_le (abs_le.mp hc).2⟩
  have h₁ := horizontal_vanish hac ha hc he (T:=fun n => -T n) (fun n u hu => (h n u hu).2)
  have h₂ := horizontal_vanish hac ha hc he (T:=T) (fun n u hu => (h n u hu).1)
  have h₃ := intervalIntegral_tendsto_integral hB (tendsto_neg_atTop_atBot.comp hT) hT
  have h₄ := intervalIntegral_tendsto_integral hA (tendsto_neg_atTop_atBot.comp hT) hT
  have hlim := (((h₁.sub h₂).add (h₃.const_mul Complex.I)).sub (h₄.const_mul Complex.I))
  have hzero := tendsto_nhds_unique hlim (tendsto_const_nhds.congr (fun n => (hrect n).symm))
  simp only [sub_zero,zero_add,sub_eq_zero] at hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero hzero).symm

def twistQ (Q : ℂ→ℂ) (x : ℝ) (s : ℂ) := Complex.exp (-s*(x:ℂ))*Q s

theorem twistQ_norm (Q : ℂ→ℂ) (x u t : ℝ) :
    ‖twistQ Q x (vertical u t)‖=Real.exp (-u*x)*‖Q (vertical u t)‖ := by
  simp [twistQ,Complex.norm_exp,Complex.mul_re]

theorem twistQ_good {Q : ℂ→ℂ} {b : ℝ} (hh : GoodHeights Q b) (x : ℝ) :
    GoodHeights (twistQ Q x) b := by
  obtain ⟨T,e,hT,he,h⟩ := hh
  let C := Real.exp (b*|x|)
  refine ⟨T,fun n=>C*e n,hT,by simpa using he.const_mul C,fun n u hu => ?_⟩
  have h' : Real.exp (-u*x)≤C := Real.exp_le_exp.mpr (by
    have h₁ := le_abs_self (-u*x)
    rw [abs_mul,abs_neg] at h₁
    exact h₁.trans (mul_le_mul_of_nonneg_right hu (abs_nonneg _)))
  have hh' := h n u hu
  constructor <;> rw [twistQ_norm] <;>
    exact mul_le_mul h' (by first | exact hh'.1 | exact hh'.2) (norm_nonneg _) (Real.exp_nonneg _)

theorem twistQ_integrable (Q : ℂ→ℂ) {u b : ℝ} (hu : |u|≤b)
    (hC : ContinuousOn Q (closedStrip b)) (hA : Integrable (fun t=>Q (vertical u t))) (x : ℝ) :
    Integrable (fun t=>twistQ Q x (vertical u t)) := by
  have hct : Continuous (fun t => Q (vertical u t)) :=
    hC.comp_continuous (by unfold vertical; fun_prop) (fun t => by simpa [closedStrip] using hu)
  have hf : Continuous (fun t => twistQ Q x (vertical u t)) :=
    (show Continuous (fun t=> Complex.exp (-vertical u t*(x:ℂ))) by unfold vertical; fun_prop).mul hct
  apply (hA.norm.const_mul (Real.exp (-u*x))).mono' hf.aestronglyMeasurable
  exact .of_forall (fun t => (twistQ_norm Q x u t).le)

theorem wall_inverse_shift (Q : ℂ→ℂ) {a c b : ℝ} (hac : a≤c) (ha : |a|≤b) (hc : |c|≤b)
    (hC : ContinuousOn Q (closedStrip b)) (hD : DifferentiableOn ℂ Q (openStrip b))
    (hh : GoodHeights Q b) (hA : Integrable (fun t=>Q (vertical a t)))
    (hB : Integrable (fun t=>Q (vertical c t))) (x : ℝ) :
    (∫ t : ℝ,twistQ Q x (vertical a t)) = ∫ t : ℝ,twistQ Q x (vertical c t) := by
  apply vertical_integrals_eq _ hac ha hc _ _ (twistQ_good hh x)
    (twistQ_integrable Q ha hC hA x) (twistQ_integrable Q hc hC hB x)
  · exact (show Continuous (fun s : ℂ => Complex.exp (-s*(x:ℂ))) by fun_prop).continuousOn.mul hC
  · exact (show Differentiable ℂ (fun s : ℂ => Complex.exp (-s*(x:ℂ))) by fun_prop).differentiableOn.mul hD

end
end MasulloRH.SynthWall
end StandaloneSynthWallContour


-- Local source: SynthWallReconstruction
section StandaloneSynthWallReconstruction
open Set MeasureTheory Filter FourierTransform
open scoped Topology FourierTransform SchwartzMap Convolution
namespace MasulloRH.SynthWall
noncomputable section

def freq : ℝ := -2*Real.pi
theorem freq_ne_zero : freq ≠ 0 := by dsimp [freq]; positivity

def profile (Q : ℂ→ℂ) (σ : ℝ) (ξ : ℝ) := Q (vertical σ (freq*ξ))
def tilt (σ : ℝ) (f : ℝ→ℂ) (x : ℝ) := (Real.exp (σ*x):ℂ)*f x

theorem tilt_norm (σ : ℝ) (f : ℝ→ℂ) (x : ℝ) :
    ‖tilt σ f x‖=Real.exp (σ*x)*‖f x‖ := by rw [tilt,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]

theorem fourierInv_profile_integral (Q : ℂ→ℂ) (σ x : ℝ) :
    (Real.exp (-σ*x):ℂ)*(𝓕⁻ (profile Q σ)) x =
      |freq⁻¹| • ∫ t : ℝ,twistQ Q x (vertical σ t) := by
  rw [Real.fourierInv_eq',←integral_const_mul,←Measure.integral_comp_mul_left]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [RCLike.inner_apply,conj_trivial,smul_eq_mul,profile,twistQ,Complex.ofReal_exp,
    ←mul_assoc,←Complex.exp_add]
  congr 2
  dsimp [vertical,freq]
  push_cast
  ring

theorem fourierInv_profile_shift (Q : ℂ→ℂ) {a c b : ℝ} (hac : a≤c) (ha : |a|≤b) (hc : |c|≤b)
    (hC : ContinuousOn Q (closedStrip b)) (hD : DifferentiableOn ℂ Q (openStrip b))
    (hh : GoodHeights Q b) (hA : Integrable (fun t=>Q (vertical a t)))
    (hB : Integrable (fun t=>Q (vertical c t))) (x : ℝ) :
    (Real.exp (-a*x):ℂ)*(𝓕⁻ (profile Q a)) x = (Real.exp (-c*x):ℂ)*(𝓕⁻ (profile Q c)) x := by
  rw [fourierInv_profile_integral,fourierInv_profile_integral,wall_inverse_shift Q hac ha hc hC hD hh hA hB]

end
end MasulloRH.SynthWall
end StandaloneSynthWallReconstruction


-- Local source: SynthPowerReconstruction
section StandaloneSynthPowerReconstruction
open Set MeasureTheory Filter FourierTransform
open scoped Topology FourierTransform SchwartzMap Convolution
namespace MasulloRH.SynthPower
noncomputable section
open SynthWall

/-- One wall is a Schwartz Fourier multiplier acting on a function with an integrable
squared spatial moment of order p. The argument uses Mathlib's 2π-frequency convention. -/
def WallFactor (p : ℝ) (Q : ℂ→ℂ) (σ : ℝ) : Prop :=
  ∃ f : ℝ→ℂ, ∃ m : 𝓢(ℝ,ℂ), Integrable f ∧ MemLp (fun x : ℝ=>(1+|x|)^p*‖f x‖) 2 volume ∧
    ∀ ξ, profile Q σ ξ=(𝓕 f) ξ*m ξ

private theorem fourier_norm (f : ℝ→ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫x,‖f x‖ := by
  rw [Real.fourier_eq]
  exact (norm_integral_le_integral_norm _).trans_eq (by simp only [Circle.norm_smul])

theorem factor_inverse (p : ℝ) (hp : 0≤p) {Q : ℂ→ℂ} {σ b : ℝ} (hC : ContinuousOn Q (closedStrip b))
    (hσ : |σ|≤b) (hw : WallFactor p Q σ) :
    Integrable (fun t=>Q (vertical σ t)) ∧ Continuous (𝓕⁻ (profile Q σ)) ∧
    Integrable (𝓕⁻ (profile Q σ)) ∧
    MemLp (fun x : ℝ=>(1+|x|)^p*‖(𝓕⁻ (profile Q σ)) x‖) 2 volume ∧
    𝓕 (𝓕⁻ (profile Q σ))=profile Q σ := by
  obtain ⟨f,m,hf,hF,hQ⟩ := hw
  let k : 𝓢(ℝ,ℂ) := 𝓕⁻ m
  let g := conv k f
  have hg : Integrable g := k.integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  have hbdd : BddAbove (Set.range fun x => ‖k x‖) := ⟨SchwartzMap.seminorm ℝ 0 0 k,by
    rintro _ ⟨x,rfl⟩; exact SchwartzMap.norm_le_seminorm ℝ k x⟩
  have hgc : Continuous g := hbdd.continuous_convolution_left_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) k.continuous hf
  have hgF : 𝓕 g=profile Q σ := by
    funext ξ
    rw [hQ]
    change 𝓕 (k ⋆[ContinuousLinearMap.mul ℂ ℂ] f) ξ=_
    rw [Real.fourier_mul_convolution_eq k.integrable hf,←SchwartzMap.fourier_coe]
    rw [show 𝓕 k=m from fourier_fourierInv_eq m,mul_comm]
  have hC' : Continuous (profile Q σ) := hC.comp_continuous
    (show Continuous (fun ξ=>vertical σ (freq*ξ)) by unfold vertical; fun_prop)
    (fun t=>by simpa [closedStrip] using hσ)
  have hI : Integrable (profile Q σ) := by
    apply (m.integrable.norm.const_mul (∫x,‖f x‖)).mono' hC'.aestronglyMeasurable
    filter_upwards with ξ
    rw [hQ,norm_mul]
    exact mul_le_mul_of_nonneg_right (fourier_norm f ξ) (norm_nonneg _)
  have hEq : 𝓕⁻ (profile Q σ)=g := by
    rw [←hgF]
    exact hgc.fourierInv_fourier_eq hg (hgF ▸ hI)
  rw [hEq]
  exact ⟨(integrable_comp_mul_left_iff _ freq_ne_zero).mp hI,hgc,hg,schwartz_young p hp k hf hF,hgF⟩

theorem reconstruct (p : ℝ) (hp : 0≤p) {Q : ℂ→ℂ} {b : ℝ} (hb : 0≤b)
    (hC : ContinuousOn Q (closedStrip b)) (hD : DifferentiableOn ℂ Q (openStrip b))
    (hh : GoodHeights Q b) (hwa : WallFactor p Q (-b)) (hwb : WallFactor p Q b) :
    ∃ q : ℝ→ℂ, Continuous q ∧ Integrable (fun x => Real.exp (b*|x|)*‖q x‖) ∧
      MemLp (fun x => (1+|x|)^p*(Real.exp (b*|x|)*‖q x‖)) 2 volume ∧
      ∀ σ : ℝ, |σ|=b → tilt σ q=𝓕⁻ (profile Q σ) ∧ 𝓕 (tilt σ q)=profile Q σ := by
  classical
  obtain ⟨hA,hAC,hAI,hAL,hAF⟩ := factor_inverse p hp hC (show |(-b)|≤b by simp [abs_of_nonneg hb]) hwa
  obtain ⟨hB,hBC,hBI,hBL,hBF⟩ := factor_inverse p hp hC (show |b|≤b by rw [abs_of_nonneg hb]) hwb
  let q (x : ℝ) := (Real.exp (-b*x):ℂ)*(𝓕⁻ (profile Q b)) x
  have hqC : Continuous q := (show Continuous (fun x : ℝ=>(Real.exp (-b*x):ℂ)) by fun_prop).mul hBC
  have hshift (x : ℝ) := fourierInv_profile_shift Q (show -b≤b by linarith)
    (show |(-b)|≤b by simp [abs_of_nonneg hb]) (show |b|≤b by rw [abs_of_nonneg hb]) hC hD hh hA hB x
  have ht (σ : ℝ) (hσ : |σ|=b) : tilt σ q=𝓕⁻ (profile Q σ) := by
    have hsign : σ=b ∨ σ= -b := (abs_eq hb).mp hσ
    rcases hsign with rfl | rfl
    · funext x
      simp only [tilt,q,←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,neg_mul,add_neg_cancel,Real.exp_zero,Complex.ofReal_one,one_mul]
    · funext x
      change (Real.exp (-b*x):ℂ)*q x=_
      rw [show q x=(Real.exp (- -b*x):ℂ)*(𝓕⁻ (profile Q (-b))) x from (hshift x).symm]
      simp only [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,neg_neg,neg_mul,neg_add_cancel,Real.exp_zero,Complex.ofReal_one,one_mul]
  let fa := fun x => ‖(𝓕⁻ (profile Q (-b))) x‖
  let fb := fun x => ‖(𝓕⁻ (profile Q b)) x‖
  have hsplit : (fun x => Real.exp (b*|x|)*‖q x‖)=(Ici 0).piecewise fb fa := by
    funext x
    by_cases hx : 0≤x
    · rw [piecewise_eq_of_mem _ _ _ (show x∈Ici 0 from hx),abs_of_nonneg hx,←tilt_norm,ht b (abs_of_nonneg hb)]
    · rw [piecewise_eq_of_notMem _ _ _ (show x∉Ici (0:ℝ) from hx),abs_of_nonpos (le_of_not_ge hx),show b*(-x)=(-b)*x by ring,
        ←tilt_norm,ht (-b) (by rw [abs_neg,abs_of_nonneg hb])]
  have hsq : (fun x=>(1+|x|)^p*(Real.exp (b*|x|)*‖q x‖))=
      (Ici 0).piecewise (fun x:ℝ=>(1+|x|)^p*fb x) (fun x:ℝ=>(1+|x|)^p*fa x) := by
    funext x
    rw [congrFun hsplit x]
    by_cases hx : x∈Ici 0 <;> simp [hx]
  refine ⟨q,hqC,hsplit ▸ Integrable.piecewise measurableSet_Ici hBI.norm.integrableOn hAI.norm.integrableOn,
    hsq ▸ MemLp.piecewise measurableSet_Ici (hBL.restrict _) (hAL.restrict _),fun σ hσ => ⟨ht σ hσ,?_⟩⟩
  rw [ht σ hσ]
  rcases (abs_eq hb).mp hσ with rfl|rfl
  · exact hBF
  · exact hAF

end
end MasulloRH.SynthPower
end StandaloneSynthPowerReconstruction


-- Local source: SynthWallPublic
section StandaloneSynthWallPublic
open Set MeasureTheory Filter FourierTransform
open scoped Topology FourierTransform SchwartzMap
theorem solution (b p : ℝ) (hb : 0≤b) (hp : 0≤p) (Q : ℂ→ℂ) :
    let v := fun (u t : ℝ) => (u:ℂ)+(t:ℂ)*Complex.I
    let P := fun (u ξ : ℝ) => Q (v u ((-2*Real.pi)*ξ))
    let tilt := fun (u : ℝ) (q : ℝ→ℂ) (x : ℝ) => (Real.exp (u*x):ℂ)*q x
    ContinuousOn Q {s : ℂ | |s.re|≤b} →
    DifferentiableOn ℂ Q {s : ℂ | |s.re|<b} →
    (∃ T e : ℕ→ℝ, Tendsto T atTop atTop ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ (n : ℕ) (u : ℝ), |u|≤b → ‖Q (v u (T n))‖≤e n ∧ ‖Q (v u (-T n))‖≤e n) →
    (∀ u : ℝ, |u|=b → ∃ f : ℝ→ℂ, ∃ m : 𝓢(ℝ,ℂ), Integrable f ∧
      MemLp (fun x : ℝ => (1+|x|)^p*‖f x‖) 2 volume ∧ ∀ ξ, P u ξ=(𝓕 f) ξ*m ξ) →
    ∃ q : ℝ→ℂ, Continuous q ∧ Integrable (fun x : ℝ => Real.exp (b*|x|)*‖q x‖) ∧
      MemLp (fun x : ℝ => (1+|x|)^p*(Real.exp (b*|x|)*‖q x‖)) 2 volume ∧
      ∀ u : ℝ, |u|=b → tilt u q=𝓕⁻ (P u) ∧ 𝓕 (tilt u q)=P u := by
  intro v P tilt hC hD hT hw
  exact MasulloRH.SynthPower.reconstruct p hp hb hC hD hT (hw (-b) (by simp [abs_of_nonneg hb])) (hw b (abs_of_nonneg hb))

end StandaloneSynthWallPublic

