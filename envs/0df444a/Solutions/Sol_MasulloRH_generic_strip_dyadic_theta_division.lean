-- Prove2me | solution 1 for MasulloRH.generic_strip_dyadic_theta_division
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T04:10:10.77205+00:00
-- url     : https://prove2.me/submissions/0ab415f7-6816-4b40-b9ec-50067de21560

import Definitions.Def_MasulloRH_GaussianThetaDivision
import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_MasulloRH_RegularizedTrace
import Definitions.Def_MasulloRH_WeightedStripJetSpace
import Mathlib
import Theorems.Thm_MasulloRH_bilateral_fourier_reconstruction_from_schwartz_walls
import Theorems.Thm_MasulloRH_dyadic_gaussian_theta_mellin
import Theorems.Thm_MasulloRH_dyadic_theta_minimum_modulus_in_zero_separated_strips
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_sub_one_le

-- Local source: StripTestAmplitude
section StandaloneStripTestAmplitude
open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff BigOperators
namespace MasulloRH.StripTrace
noncomputable section

def lap (f : ℝ → ℂ) (s : ℂ) := ∫ y : ℝ, Complex.exp (s*y)*f y

theorem mellin_eq_lap (φ : ℝ → ℂ) (w : ℂ) : mellin φ w = lap (fun y => φ (Real.exp y)) w := by
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have him : Real.exp '' univ = Ioi 0 := by rw [image_univ,Real.range_exp]
  unfold mellin lap
  rw [← him,integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn,setIntegral_univ]
  apply integral_congr_ae; filter_upwards with x
  rw [abs_of_pos (Real.exp_pos _),Complex.real_smul,smul_eq_mul,Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp,
    Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2; ring

end
end MasulloRH.StripTrace
end StandaloneStripTestAmplitude


-- Local source: StripJetZeroData
section StandaloneStripJetZeroData
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace MasulloRH.StripJetSpace
noncomputable section

abbrev Z (b : ℝ) := ZetaZerosInTraceStrip b
abbrev mult {b : ℝ} (z : Z b) := analyticOrderNatAt riemannZeta z.val

theorem mult_pos {b : ℝ} (z : Z b) : 0 < mult z := by
  have h1 : z.val ≠ 1 := fun h => (not_lt_of_ge (le_of_eq (congrArg Complex.re h).symm)) z.prop.2.2.1
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hf := analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  have hne := (analyticOn_riemannZeta _ h1).analyticOrderAt_ne_zero.mpr z.prop.1
  exact Nat.pos_of_ne_zero (fun h => (ENat.toNat_eq_zero.mp h).elim hne hf)

end
end MasulloRH.StripJetSpace
end StandaloneStripJetZeroData


-- Local source: SynthSeparationGeometry
section StandaloneSynthSeparationGeometry
open Set Filter MeasureTheory
open scoped Topology
namespace MasulloRH.SynthesisStrip
noncomputable section

abbrev DivisorZero := ZetaZerosInTraceStrip (1/2)
def sepWeight (z : DivisorZero) : ℝ := 1/(1+z.val.im^2)

theorem sepWeight_pos (z : DivisorZero) : 0<sepWeight z := by unfold sepWeight; positivity

theorem sepWeight_summable : Summable sepWeight := by
  apply Summable.of_nonneg_of_le (fun z => (sepWeight_pos z).le) _ (weighted_zero_summability (1/2) (by norm_num))
  intro z
  apply div_le_div_of_nonneg_right _ (by positivity : 0≤1+z.val.im^2)
  exact_mod_cast StripJetSpace.mult_pos z

private theorem zeros_countable : Countable DivisorZero := by
  have h := sepWeight_summable.countable_support
  rw [show Function.support sepWeight=univ by ext z; simp [Function.support,(sepWeight_pos z).ne']] at h
  exact Set.countable_univ_iff.mp h

def excluded (c : ℝ) (a : DivisorZero→ℝ) : Set ℝ :=
  (⋃ z, Metric.ball (a z) (c*sepWeight z)) ∪ (⋃ z, Metric.ball (-(a z)) (c*sepWeight z))

def sepMass : ℝ := ∑' z, sepWeight z
private theorem mass_nn : 0 ≤ sepMass := tsum_nonneg fun z => (sepWeight_pos z).le

theorem excluded_le (c : ℝ) (hc : 0≤c) (a : DivisorZero→ℝ) :
    volume (excluded c a) ≤ ENNReal.ofReal (4*c*sepMass) := by
  let _ := zeros_countable
  have hb (v : DivisorZero→ℝ) : volume (⋃ z, Metric.ball (v z) (c*sepWeight z)) ≤ ENNReal.ofReal ((2*c)*sepMass) := by
    apply (measure_iUnion_le _).trans
    simp only [Real.volume_ball,←mul_assoc,←ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (by positivity : 0≤2*c) (sepWeight_pos z).le)
      (sepWeight_summable.mul_left (2*c)),tsum_mul_left,sepMass,le_refl]
  apply (measure_union_le _ _).trans ((add_le_add (hb a) (hb (fun z => -a z))).trans_eq ?_)
  rw [← ENNReal.ofReal_add (mul_nonneg (by positivity : 0≤2*c) mass_nn) (mul_nonneg (by positivity : 0≤2*c) mass_nn)]
  congr 1; ring

theorem outside_excluded {c x : ℝ} {a : DivisorZero→ℝ} (h : x∉excluded c a) (z : DivisorZero) :
    c*sepWeight z ≤ |x-a z| ∧ c*sepWeight z ≤ |x+a z| := by
  simp only [excluded,mem_union,mem_iUnion,Metric.mem_ball,Real.dist_eq,sub_neg_eq_add,not_or,not_exists,not_lt] at h
  exact ⟨h.1 z,h.2 z⟩

theorem ae_separated (a : DivisorZero→ℝ) :
    ∀ᵐ x : ℝ, ∃ c : ℝ, 0<c ∧ ∀ z, c*sepWeight z≤|x-a z| ∧ c*sepWeight z≤|x+a z| := by
  rw [ae_iff,← nonpos_iff_eq_zero]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let c := (ε:ℝ)/(4*(1+sepMass))
  have hm := mass_nn
  have hc : 0<c := by dsimp [c]; positivity
  have hs : {x : ℝ | ¬∃ c : ℝ, 0<c ∧ ∀ z, c*sepWeight z≤|x-a z| ∧ c*sepWeight z≤|x+a z|} ⊆ excluded c a := by
    intro x hx
    by_contra ho
    exact hx ⟨c,hc,outside_excluded ho⟩
  apply (measure_mono hs).trans ((excluded_le c hc.le a).trans ?_)
  rw [zero_add,←ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  have hcn : c*(4*(1+sepMass))=(ε:ℝ) := by dsimp [c]; field_simp
  nlinarith

theorem horizontal_separated (a : DivisorZero→ℝ) :
    ∃ c : ℝ, 0<c ∧ ∀ n : ℕ, ∃ t ∈ Icc (n:ℝ) (n+1),
      ∀ z, c*sepWeight z≤|t-a z| ∧ c*sepWeight z≤|t+a z| := by
  let c : ℝ := 1/(8*(1+sepMass))
  have hm := mass_nn
  have hc : 0<c := by dsimp [c]; positivity
  have he : volume (excluded c a)<1 := by
    apply (excluded_le c hc.le a).trans_lt
    rw [←ENNReal.ofReal_one]
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
    have hcn : c*(8*(1+sepMass))=1 := by dsimp [c]; field_simp
    nlinarith
  refine ⟨c,hc,fun n => ?_⟩
  have hsub : ¬Icc (n:ℝ) (n+1) ⊆ excluded c a := by
    intro hs
    have q := (measure_mono hs).trans_lt he
    simpa using q
  obtain ⟨t,ht,ho⟩ := Set.not_subset.mp hsub
  exact ⟨t,ht,outside_excluded ho⟩

end
end MasulloRH.SynthesisStrip
end StandaloneSynthSeparationGeometry


-- Local source: SynthGeneratorAnchor
section StandaloneSynthGeneratorAnchor
open Set MeasureTheory Filter
open scoped Topology
namespace MasulloRH.SynthesisStrip
noncomputable section

private theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin,norm_div,norm_mul,Complex.norm_I,mul_one,show ‖(2:ℂ)‖=2 by norm_num,div_le_iff₀ (by norm_num)]
  apply (norm_sub_le _ _).trans
  simp only [Complex.norm_exp,Complex.mul_I_re,Complex.neg_im,neg_neg]
  linarith [Real.exp_le_exp.mpr (le_abs_self z.im),Real.exp_le_exp.mpr (neg_le_abs z.im)]

private theorem norm_gamma_one (w : ℂ) (hw : w.re=1) : ‖Complex.Gamma w‖ ≤ 1 := by
  rw [Complex.Gamma_eq_integral (by linarith),Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  rw [←integral_exp_neg_Ioi_zero]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_nonneg _),Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.sub_re,hw,Complex.one_re,sub_self,Real.rpow_zero,mul_one]

private theorem inv_gamma_one_high (w : ℂ) (hw : w.re=1) (hi : 1≤|w.im|) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ Real.exp (Real.pi*|w.im|) := by
  have hw' : 1≤‖1-w‖ := hi.trans (by simpa using Complex.abs_im_le_norm (1-w))
  have hw0 : 1-w≠0 := by intro he; rw [he,norm_zero] at hw'; linarith
  have hgt := norm_gamma_one ((1-w)+1) (by simp [hw])
  rw [Complex.Gamma_add_one _ hw0,norm_mul] at hgt
  have hG : ‖Complex.Gamma (1-w)‖ ≤ 1 :=
    (le_mul_of_one_le_left (norm_nonneg _) hw').trans hgt
  have hg₁ : Complex.Gamma w≠0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hg₂ : Complex.Gamma (1-w)≠0 := by
    intro he
    have hh := Complex.Gamma_add_one (1-w) hw0
    rw [he,mul_zero] at hh
    exact Complex.Gamma_ne_zero_of_re_pos (by simp [hw]) hh
  have hs₀ : Complex.sin (Real.pi*w)≠0 := by
    intro h
    have hh := Complex.Gamma_mul_Gamma_one_sub w
    rw [h,div_zero] at hh
    exact mul_ne_zero hg₁ hg₂ hh
  have hπ : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hEq : (Complex.Gamma w)⁻¹=Complex.Gamma (1-w)*Complex.sin (Real.pi*w)/(Real.pi:ℂ) := by
    have he := (eq_div_iff hs₀).mp (Complex.Gamma_mul_Gamma_one_sub w)
    field_simp [hg₁,hπ]
    rw [mul_comm w (Real.pi:ℂ)]
    linear_combination -he
  rw [hEq,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  apply (div_le_self (by positivity) (by linarith [Real.pi_gt_three] : 1≤Real.pi)).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) hG).trans
  have h := norm_sin_le_exp ((Real.pi:ℂ)*w)
  simpa [Complex.mul_im,abs_mul,abs_of_pos Real.pi_pos] using h

theorem inv_gamma_one_bound :
    ∃ C : ℝ, 0<C ∧ ∀ w : ℂ, w.re=1 → ‖(Complex.Gamma w)⁻¹‖ ≤ C*Real.exp (Real.pi*|w.im|) := by
  let f (t : ℝ) := ‖(Complex.Gamma (1+(t:ℂ)*Complex.I))⁻¹‖
  have hc : Continuous f := Complex.differentiable_one_div_Gamma.continuous.norm.comp (by fun_prop)
  obtain ⟨M,hM⟩ := (isCompact_Icc (α:=ℝ) (a:=-1) (b:=1)).bddAbove_image hc.continuousOn
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun w hw => ?_⟩
  have h1 : 1≤Real.exp (Real.pi*|w.im|) := Real.one_le_exp (mul_nonneg Real.pi_pos.le (abs_nonneg _))
  by_cases hh : 1≤|w.im|
  · exact (inv_gamma_one_high w hw hh).trans (le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_right _ _))
  have hI := abs_lt.mp (lt_of_not_ge hh)
  have hM' := hM (mem_image_of_mem f (show w.im∈Icc (-1:ℝ) 1 from ⟨hI.1.le,hI.2.le⟩))
  have he : (1:ℂ)+(w.im:ℂ)*Complex.I=w := by apply Complex.ext <;> simp [hw]
  dsimp only [f] at hM'
  rw [he] at hM'
  exact hM'.trans ((le_max_left _ _).trans (le_mul_of_one_le_right (le_trans (by norm_num : (0:ℝ)≤1) (le_max_right _ _)) h1))

def explicitGenerator (s : ℂ) : ℂ := (1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))*completedRiemannZeta s

theorem generator_anchor :
    ∃ C : ℝ, 0<C ∧ ∀ s : ℂ, s.re=2 →
      1 ≤ ‖explicitGenerator s‖ * (C*Real.exp (Real.pi*|s.im|)) := by
  obtain ⟨M,hM,hm⟩ := inv_gamma_one_bound
  let a := 2-Real.pi^2/6
  have ha : 0<a := by dsimp [a]; nlinarith [Real.pi_lt_d2,Real.pi_pos]
  refine ⟨8*M*Real.pi/a,by positivity,fun s hs => ?_⟩
  have hζ := Zeta23.RvM.norm_riemannZeta_sub_one_le (s:=s) hs.ge
  have hl : a≤‖riemannZeta s‖ := by
    have h := norm_sub_le (riemannZeta s) (riemannZeta s-1)
    simp at h; dsimp [a]; linarith
  have hf (c : ℂ) (hc : c.re = -2 ∨ c.re = -1) : 1/2 ≤ ‖1-(2:ℂ)^c‖ := by
    have h := norm_sub_norm_le (1:ℂ) ((2:ℂ)^c)
    rw [norm_one,show ‖(2:ℂ)^c‖=(2:ℝ)^c.re from Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2) c] at h
    rcases hc with hh|hh <;> rw [hh] at h <;> norm_num at h <;> linarith
  have ha₁ := hf (-s) (Or.inl (by simp [hs]))
  have ha₂ := hf (1-s) (Or.inr (by simp [hs]; norm_num))
  have hs2 : (s/2).re=1 := by simp [Complex.div_ofNat_re,hs]
  have hn := hm (s/2) hs2
  have hge := Complex.Gamma_ne_zero_of_re_pos (s:=s/2) (by rw [hs2]; norm_num)
  rw [norm_inv,inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr hge)] at hn
  have hh : 1 ≤ ‖Complex.Gamma (s/2)‖*(M*Real.exp (Real.pi*|s.im|)) := by
    apply hn.trans
    rw [mul_comm (M*Real.exp _),Complex.div_ofNat_im,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    gcongr; linarith [abs_nonneg s.im]
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hs0 : s≠0 := by intro he; rw [he,Complex.zero_re] at hs; norm_num at hs
  have hcomp := (eq_div_iff hΓ).mp (riemannZeta_def_of_ne_zero hs0)
  have hpow : ‖(Real.pi:ℂ)^(-s/2)‖=Real.pi⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,Complex.div_ofNat_re,Complex.neg_re,hs]
    norm_num [Real.rpow_neg_one]
  rw [explicitGenerator,← hcomp,Complex.Gammaℝ_def]
  simp only [norm_mul,hpow]
  have hmain := mul_le_mul (mul_le_mul ha₁ ha₂ (by norm_num) (norm_nonneg _)) hl ha.le
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    1 ≤ ‖Complex.Gamma (s/2)‖*(M*Real.exp (Real.pi*|s.im|)) := hh
    _ ≤ _ := by
      have hpi := Real.pi_pos
      field_simp
      nlinarith only [hmain,ha]

end
end MasulloRH.SynthesisStrip
end StandaloneSynthGeneratorAnchor


-- Local source: ThetaGeneralBounds
section StandaloneThetaGeneralBounds
open Set Filter MeasureTheory Asymptotics
open scoped Topology SchwartzMap FourierTransform
namespace MasulloRH
noncomputable section

private def latticeWeight (k : ℕ) (n : ℕ) : ℝ := (((n:ℝ)+1)^k)⁻¹

private lemma summable_latticeWeight (k : ℕ) (hk : 1 < k) : Summable (latticeWeight k) := by
  have h : -((k:ℕ):ℝ) < -1 := by exact_mod_cast (show -((k:ℕ):ℤ) < -1 by omega)
  have hz := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr h)
  apply hz.congr
  intro n
  dsimp [latticeWeight]
  rw [Nat.cast_add, Nat.cast_one, Real.rpow_neg (by positivity), Real.rpow_natCast]

def thetaNat (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℕ, f (((n:ℝ)+1)*x)

private lemma thetaTerm_bound (f : 𝓢(ℝ,ℂ)) (k n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖f (((n:ℝ)+1)*x)‖ ≤ ((SchwartzMap.seminorm ℝ k 0) f) * (x^k)⁻¹ * latticeWeight k n := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ f k (((n:ℝ)+1)*x)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hn hx), mul_pow] at h
  rw [latticeWeight, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hn _), ← div_eq_mul_inv, le_div_iff₀ (pow_pos hx _)]
  nlinarith only [h]

private lemma thetaNat_summable (f : 𝓢(ℝ,ℂ)) (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => f (((n:ℝ)+1)*x)) :=
  ((summable_latticeWeight 2 (by norm_num)).mul_left _).of_norm_bounded (fun n => thetaTerm_bound f 2 n hx)

private lemma thetaNat_bound (f : 𝓢(ℝ,ℂ)) (k : ℕ) (hk : 1 < k) {x : ℝ} (hx : 0 < x) :
    ‖thetaNat f x‖ ≤ (((SchwartzMap.seminorm ℝ k 0) f) * ∑' n, latticeWeight k n) * (x^k)⁻¹ := by
  apply (norm_tsum_le_tsum_norm ((thetaNat_summable f x hx).norm)).trans
  apply (Summable.tsum_le_tsum (fun n => thetaTerm_bound f k n hx) (thetaNat_summable f x hx).norm
    ((summable_latticeWeight k hk).mul_left _)).trans_eq
  rw [tsum_mul_left]; ring

lemma thetaNat_continuousOn (f : 𝓢(ℝ,ℂ)) : ContinuousOn (thetaNat f) (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  have hu : Summable (fun n : ℕ => (SchwartzMap.seminorm ℝ 2 0 f) * ((x/2)^2)⁻¹ * latticeWeight 2 n) :=
    (summable_latticeWeight 2 (by norm_num)).mul_left _
  have hc : ContinuousOn (thetaNat f) (Ioi (x/2)) := by
    apply continuousOn_tsum (fun n => (f.continuous.comp (continuous_const.mul continuous_id)).continuousOn) hu
    intro n y hy
    have hx' : 0 < x/2 := by positivity
    have hy' : x/2 < y := hy
    apply (thetaTerm_bound f 2 n (lt_trans hx' hy')).trans
    gcongr
    dsimp [latticeWeight]; positivity
  exact ((hc.continuousAt (isOpen_Ioi.mem_nhds (show x/2 < x by linarith)))).continuousWithinAt

def reflectS (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) f

def theta (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℤ, f ((n:ℝ)*x)

lemma theta_split (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) {x : ℝ} (hx : 0 < x) :
    theta f x = thetaNat (f + reflectS f) x := by
  have h₁ := thetaNat_summable f x hx
  have h₂ := thetaNat_summable (reflectS f) x hx
  have hpos : Summable (fun n : ℕ => f ((((n:ℤ)+1 : ℤ) : ℝ)*x)) := by simpa using h₁
  have hneg : Summable (fun n : ℕ => f (((-((n:ℤ)+1) : ℤ) : ℝ)*x)) := by
    apply h₂.congr
    intro n
    change f (-(((n:ℝ)+1)*x)) = _
    push_cast; congr 1; ring
  have hsum := tsum_of_add_one_of_neg_add_one (f:=fun n : ℤ => f ((n:ℝ)*x)) hpos hneg
  change (∑' n : ℤ, f ((n:ℝ)*x)) = _
  rw [hsum]
  simp only [Int.cast_add, Int.cast_one, Int.cast_natCast, Int.cast_neg, Int.cast_zero, zero_mul, hf, add_zero]
  change _ = ∑' n : ℕ, (f (((n:ℝ)+1)*x) + f (-(((n:ℝ)+1)*x)))
  rw [h₁.tsum_add (g:=fun n : ℕ => f (-(((n:ℝ)+1)*x))) h₂]
  simp only [neg_mul]

/-- Uniform positive-scale decay of the Schwartz lattice sum in every integral order above one. -/
theorem thetaSchwartz_bound (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) (k : ℕ) (hk : 1 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖∑' n : ℤ, f ((n:ℝ)*x)‖ ≤ C * (x^k)⁻¹ := by
  refine ⟨(SchwartzMap.seminorm ℝ k 0) (f+reflectS f) * ∑' n, latticeWeight k n, ?_, ?_⟩
  · apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro n; dsimp [latticeWeight]; positivity
  · intro x hx
    change ‖theta f x‖ ≤ _
    rw [theta_split f hf hx]
    exact thetaNat_bound _ k hk hx

end
end MasulloRH
end StandaloneThetaGeneralBounds


-- Local source: ThetaPoisson
section StandaloneThetaPoisson
open MeasureTheory Filter Set FourierTransform
open scoped SchwartzMap FourierTransform Topology
set_option autoImplicit false
namespace MasulloSynthesis
noncomputable section

theorem theta_poisson_scaled (f : 𝓢(ℝ,ℂ)) {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, f ((n:ℝ)*a)) =
    (a⁻¹:ℝ) • ∑' n : ℤ, (𝓕 f) ((n:ℝ)*a⁻¹) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha.ne')
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hg (x : ℝ) : g x = f (a*x) := rfl
  have hscale (ξ : ℝ) : (𝓕 g) ξ = (a⁻¹:ℝ) • (𝓕 f) (ξ*a⁻¹) := by
    change 𝓕 (⇑g) ξ = (a⁻¹:ℝ) • 𝓕 (⇑f) (ξ*a⁻¹)
    rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
    let F (x : ℝ) := Complex.exp (↑(-2*Real.pi*x*(ξ*a⁻¹)) * Complex.I) • f x
    calc
      _ = ∫ x : ℝ, F (a*x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [F]
          rw [hg]
          congr 3
          field_simp
      _ = _ := by
        have h := Measure.integral_comp_mul_left F a
        simpa only [abs_of_pos (inv_pos.mpr ha)] using h
  have h := g.tsum_eq_tsum_fourier 0
  simp only [zero_add, hg, hscale, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at h
  rw [← tsum_const_smul'']
  simpa [mul_comm a] using h
end
end MasulloSynthesis
end StandaloneThetaPoisson


-- Local source: StripThetaRows
section StandaloneStripThetaRows
open MeasureTheory Filter Set FourierTransform
open scoped Topology FourierTransform SchwartzMap
namespace MasulloRH.StripTheta
noncomputable section

def logTheta (g : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ :=
  (Real.exp (x/2):ℂ)* ∑' n : ℤ,g ((n:ℝ)*Real.exp x)

theorem logTheta_continuous (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) : Continuous (logTheta g) := by
  apply (show Continuous (fun x : ℝ => (Real.exp (x/2):ℂ)) by fun_prop).mul
  have he : (fun x : ℝ => ∑' n : ℤ,g ((n:ℝ)*Real.exp x)) = thetaNat (g+reflectS g) ∘ Real.exp :=
    funext (fun x => theta_split g h0 (Real.exp_pos x))
  rw [he]
  exact (thetaNat_continuousOn _).comp_continuous Real.continuous_exp Real.exp_pos

theorem logTheta_poisson (g : 𝓢(ℝ,ℂ)) (x : ℝ) : logTheta g x=logTheta (𝓕 g) (-x) := by
  simp only [logTheta,MasulloSynthesis.theta_poisson_scaled g (Real.exp_pos x),Real.exp_neg,
    Complex.real_smul,←mul_assoc,←Complex.ofReal_mul]
  congr 2
  rw [←Real.exp_neg,←Real.exp_add]
  congr 1
  ring

private theorem logTheta_decay_right (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (k : ℕ) (hk : 1<k) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, ‖logTheta g x‖≤C*Real.exp ((1/2-(k:ℝ))*x) := by
  obtain ⟨C,hC,h⟩ := thetaSchwartz_bound g h0 k hk
  refine ⟨C,hC,fun x => ?_⟩
  rw [logTheta,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply (mul_le_mul_of_nonneg_left (h _ (Real.exp_pos x)) (Real.exp_nonneg _)).trans_eq
  rw [←Real.exp_nat_mul,←Real.exp_neg,mul_left_comm,←Real.exp_add]
  congr 2
  ring

/-- Theta rows of two-moment tests decay faster than any fixed exponential in both log tails. -/
theorem logTheta_exp_decay (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (hI : (∫ t : ℝ,g t)=0) (a : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, ‖logTheta g x‖ ≤ C*Real.exp (-a*|x|) := by
  obtain ⟨j,hj⟩ := exists_nat_ge a
  let k := j+2
  have hk : 1<k := by dsimp [k]; omega
  have hka : 1/2-(k:ℝ) ≤ -a := by dsimp [k]; push_cast; linarith
  have hF : (𝓕 g : 𝓢(ℝ,ℂ)) 0=0 := by
    change 𝓕 (⇑g) 0=0; simpa [Real.fourier_real_eq_integral_exp_smul] using hI
  obtain ⟨A,hA,h₁⟩ := logTheta_decay_right g h0 k hk
  obtain ⟨B,hB,h₂⟩ := logTheta_decay_right (𝓕 g) hF k hk
  refine ⟨max A B,hA.trans (le_max_left _ _),fun x => ?_⟩
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    exact (h₁ x).trans (mul_le_mul (le_max_left _ _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hka hx)) (Real.exp_nonneg _) (hA.trans (le_max_left _ _)))
  · rw [abs_of_nonpos hx,logTheta_poisson g x]
    exact (h₂ (-x)).trans (mul_le_mul (le_max_right _ _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hka (neg_nonneg.mpr hx))) (Real.exp_nonneg _)
      (hB.trans (le_max_right _ _)))

end
end MasulloRH.StripTheta
end StandaloneStripThetaRows


-- Local source: StripPhysicalJets
section StandaloneStripPhysicalJets
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace MasulloRH.StripPhysical
noncomputable section

/-- A polynomial factor uses only the strict margin between the two exponential rates. -/
theorem polynomial_exp_bound {a b : ℝ} (h : |a|<b) (r : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, |x|^r*Real.exp (a*x) ≤ C*Real.exp (b*|x|) := by
  let d := b-|a|
  have hd : 0<d := sub_pos.mpr h
  let C : ℝ := (r.factorial:ℝ)/d^r
  refine ⟨C,by dsimp [C]; positivity,fun x => ?_⟩
  have hbd := Real.pow_div_factorial_le_exp _ (mul_nonneg hd.le (abs_nonneg x)) r
  have hp : |x|^r ≤ C * Real.exp (d*|x|) := by
    have hb := (div_le_iff₀ (by positivity : 0<(r.factorial:ℝ))).mp hbd
    rw [mul_pow] at hb
    dsimp [C]
    rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hd _)]
    simpa only [mul_comm] using hb
  have he : a*x ≤ |a| *|x| := by rw [← abs_mul]; exact le_abs_self _
  calc
    _ ≤ (C*Real.exp (d*|x|))*Real.exp (|a| *|x|) :=
      mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (by dsimp [C]; positivity)
    _ = _ := by rw [mul_assoc,← Real.exp_add]; dsimp [d]; ring_nf

end
end MasulloRH.StripPhysical
end StandaloneStripPhysicalJets


-- Local source: StripPhysicalMoments
section StandaloneStripPhysicalMoments
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace MasulloRH.StripPhysical
noncomputable section

def moment (k : ℝ→ℂ) (z : ℂ) (j : ℕ) : ℂ :=
  ∫ y : ℝ, k y*(y:ℂ)^j*Complex.exp (z*(y:ℂ))

theorem moment_integrable {b : ℝ} {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) {z : ℂ} (hz : |z.re|<b) (j : ℕ) :
    Integrable (fun y : ℝ => k y*(y:ℂ)^j*Complex.exp (z*(y:ℂ))) := by
  obtain ⟨C,_,hb⟩ := polynomial_exp_bound hz j
  apply (hW.mul_const C).mono'
  · apply (hk.mul (show Continuous (fun y : ℝ => (y:ℂ)^j) by fun_prop).aestronglyMeasurable).mul
    exact (show Continuous (fun y : ℝ => Complex.exp (z*(y:ℂ))) by fun_prop).aestronglyMeasurable
  · apply Eventually.of_forall
    intro y
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left (hb y) (norm_nonneg (k y))).trans_eq (by ring)

end
end MasulloRH.StripPhysical
end StandaloneStripPhysicalMoments


-- Local source: StripFilterMoment
section StandaloneStripFilterMoment
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace MasulloRH.StripFilter
noncomputable section

def vertical (σ t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I

open scoped SchwartzMap

end
end MasulloRH.StripFilter
end StandaloneStripFilterMoment


-- Local source: StripLaplaceMoments
section StandaloneStripLaplaceMoments
open MeasureTheory Filter Set
open scoped Topology
namespace MasulloRH.StripTrace
noncomputable section
open StripPhysical

private def kernelIntegrand (k : ℝ→ℂ) (j : ℕ) (s : ℂ) (y : ℝ) : ℂ :=
  k y*(y:ℂ)^j*Complex.exp (s*(y:ℂ))

private theorem kernel_meas {k : ℝ→ℂ} (hk : AEStronglyMeasurable k) (j : ℕ) (s : ℂ) :
    AEStronglyMeasurable (kernelIntegrand k j s) := by
  apply (hk.mul (show Continuous (fun y : ℝ => (y:ℂ)^j) by fun_prop).aestronglyMeasurable).mul
  exact (show Continuous (fun y : ℝ => Complex.exp (s*(y:ℂ))) by fun_prop).aestronglyMeasurable

theorem moment_hasDerivAt {a : ℝ} {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (a*|y|))) (j : ℕ) {s : ℂ} (hs : |s.re|<a) :
    HasDerivAt (fun t : ℂ => moment k t j) (moment k s (j+1)) s := by
  let c := (|s.re|+a)/2
  have hc : 0≤c := by dsimp [c]; linarith [abs_nonneg s.re]
  have hsc : |s.re|<c := by dsimp [c]; linarith
  have hca : c<a := by dsimp [c]; linarith
  let U := {t : ℂ | |t.re|<c}
  have hU : U∈𝓝 s := (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).mem_nhds hsc
  obtain ⟨C,hC,hbd⟩ := polynomial_exp_bound (show |c|<a by simpa [abs_of_nonneg hc] using hca) (j+1)
  have hb (y : ℝ) (t : ℂ) (ht : t∈U) :
      ‖kernelIntegrand k (j+1) t y‖ ≤ (‖k y‖*Real.exp (a*|y|)) * C := by
    have h1 : t.re*y ≤ c*|y| := (le_abs_self _).trans
      ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right (show |t.re|<c from ht).le (abs_nonneg _)))
    have h2 := hbd |y|
    rw [abs_abs] at h2
    dsimp only [kernelIntegrand]
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [mul_assoc]
    refine (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1)
      (pow_nonneg (abs_nonneg _) _)).trans h2) (norm_nonneg _)).trans_eq ?_
    ring
  have hd (y : ℝ) (t : ℂ) : HasDerivAt (fun w : ℂ => kernelIntegrand k j w y)
      (kernelIntegrand k (j+1) t y) t := by
    have hh := (((hasDerivAt_id t).mul_const (y:ℂ)).cexp.const_mul (k y*(y:ℂ)^j))
    dsimp only [id_eq,one_mul] at hh
    unfold kernelIntegrand
    convert! hh using 1 <;> first | rfl | (rw [pow_succ]; ring) | ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=kernelIntegrand k j)
    (F':=kernelIntegrand k (j+1)) hU (.of_forall (kernel_meas hk j))
    (moment_integrable hk hW hs j) (kernel_meas hk _ _)
    (.of_forall hb) (hW.mul_const C) (.of_forall (fun y t _ => hd y t))).2

theorem lap_iteratedDeriv {a : ℝ} {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (a*|y|))) (j : ℕ) {s : ℂ} (hs : |s.re|<a) :
    iteratedDeriv j (lap k) s = moment k s j := by
  induction j generalizing s with
  | zero =>
    simp only [iteratedDeriv_zero,lap,moment,pow_zero,mul_one]
    apply integral_congr_ae; exact .of_forall (fun y => mul_comm _ _)
  | succ j ih =>
    have hn : ∀ᶠ t : ℂ in 𝓝 s, |t.re|<a :=
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).mem_nhds hs
    have he : iteratedDeriv j (lap k) =ᶠ[𝓝 s] fun t => moment k t j := hn.mono (fun _ h => ih h)
    rw [iteratedDeriv_succ,he.deriv_eq,(moment_hasDerivAt hk hW j hs).deriv]

end
end MasulloRH.StripTrace
end StandaloneStripLaplaceMoments


-- Local source: SynthGenerator
section StandaloneSynthGenerator
open Set MeasureTheory Filter
open scoped Topology SchwartzMap
namespace MasulloRH.SynthesisStrip
noncomputable section
open StripTrace (lap)
open StripTheta (logTheta)

def generatorTest : 𝓢(ℝ,ℂ) := Classical.choose dyadic_gaussian_theta_mellin
theorem generatorTest_zero : generatorTest 0=0 := (Classical.choose_spec dyadic_gaussian_theta_mellin).2.1
theorem generatorTest_int : (∫x : ℝ,generatorTest x)=0 := (Classical.choose_spec dyadic_gaussian_theta_mellin).2.2.1

def seed : ℝ→ℂ := logTheta generatorTest
theorem seed_cont : Continuous seed := StripTheta.logTheta_continuous _ generatorTest_zero
theorem seed_decay (a : ℝ) : ∃ C : ℝ, 0≤C ∧ ∀ x, ‖seed x‖≤C*Real.exp (-a*|x|) :=
  StripTheta.logTheta_exp_decay _ generatorTest_zero generatorTest_int a

theorem int_exp : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  let f (x : ℝ) := Real.exp (-|x|)
  have hr : IntegrableOn f (Ioi 0) := (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).congr_fun
    (fun x hx => by simp [f,abs_of_pos (show 0<x from hx)]) measurableSet_Ioi
  have hl : IntegrableOn f (Iic 0) := (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<1) 0).congr_fun
    (fun x hx => by simp [f,abs_of_nonpos (show x≤0 from hx)]) measurableSet_Iic
  change Integrable f
  simpa using hl.union hr

theorem seed_weighted (a : ℝ) : Integrable (fun x => ‖seed x‖*Real.exp (a*|x|)) := by
  obtain ⟨C,hC,h⟩ := seed_decay (a+1)
  apply (int_exp.const_mul C).mono' (seed_cont.norm.mul (by fun_prop)).aestronglyMeasurable
  filter_upwards with x
  change ‖‖seed x‖*Real.exp (a*|x|)‖ ≤ _
  rw [Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_right (h x) (Real.exp_nonneg _)).trans_eq (by rw [mul_assoc,←Real.exp_add]; congr 2; ring)

/-- Uncentered Mellin argument, so the disc used for minimum modulus is centered at 2+it. -/
def E (s : ℂ) : ℂ := lap seed (s-1/2)

theorem E_entire : Differentiable ℂ E := by
  have he (s : ℂ) : HasDerivAt (lap seed) (StripPhysical.moment seed s 1) s := by
    have he := StripTrace.moment_hasDerivAt seed_cont.aestronglyMeasurable (seed_weighted (|s.re|+1)) 0
      (s:=s) (by linarith)
    have hm : (fun t : ℂ => StripPhysical.moment seed t 0)=lap seed := by
      funext t; unfold StripPhysical.moment lap; simp only [pow_zero,mul_one]; exact integral_congr_ae (.of_forall (fun x => mul_comm _ _))
    rwa [hm] at he
  exact (show Differentiable ℂ (lap seed) from fun s => (he s).differentiableAt).comp (differentiable_id.sub_const _)

def orbital (x : ℝ) : ℂ := ∑' n : ℤ, generatorTest ((n:ℝ)*x)

theorem E_eq_mellin (s : ℂ) : E s=mellin orbital s := by
  rw [StripTrace.mellin_eq_lap]
  unfold E lap
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [seed,logTheta,orbital]; rw [Complex.ofReal_exp,←mul_assoc,←Complex.exp_add]
  congr 2; push_cast; ring

theorem E_strip (s : ℂ) (h0 : 0<s.re) (h1 : s.re<1) :
    E s=explicitGenerator s ∧ (E s=0 ↔ riemannZeta s=0) ∧
      analyticOrderAt E s=analyticOrderAt riemannZeta s := by
  have h := (Classical.choose_spec dyadic_gaussian_theta_mellin).2.2.2.1 s h0 h1
  rw [show E=mellin orbital from funext E_eq_mellin]
  exact ⟨h.1.2,h.2⟩

theorem E_eq_explicit {s : ℂ} (h₀ : s≠0) (h₁ : s≠1) : E s=explicitGenerator s := by
  let U : Set ℂ := ({0,1}:Set ℂ)ᶜ
  have ho : IsOpen U := (isClosed_singleton.union isClosed_singleton).isOpen_compl
  have ha : AnalyticOnNhd ℂ explicitGenerator U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    apply DifferentiableOn.mul _ (fun z hz => (differentiableAt_completedZeta (by
      intro h; apply hz; simp [h]) (by intro h; apply hz; simp [h])).differentiableWithinAt)
    exact (show Differentiable ℂ (fun s : ℂ => (1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))) by fun_prop).differentiableOn
  have hu := (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (show ({0,1}:Set ℂ).Countable by simp)).isPreconnected
  have he : E =ᶠ[𝓝 (1/2:ℂ)] explicitGenerator := by
    have hpos : ∀ᶠ z : ℂ in 𝓝 (1/2:ℂ), 0<z.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have hlt : ∀ᶠ z : ℂ in 𝓝 (1/2:ℂ), z.re<1 := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num)
    filter_upwards [hpos,hlt] with z hz hZ
    exact (E_strip z hz hZ).1
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (U:=U)
    (fun z _ => E_entire.analyticAt z) ha hu (show (1/2:ℂ)∈U by dsimp [U]; norm_num) he
  simp [U,h₀,h₁]

theorem E_anchor : ∃ C : ℝ, 0<C ∧ ∀ s : ℂ, s.re=2 → 1 ≤ ‖E s‖*(C*Real.exp (Real.pi*|s.im|)) := by
  obtain ⟨C,hC,h⟩ := generator_anchor
  refine ⟨C,hC,fun s hs => ?_⟩
  have hn0 : s≠0 := by intro he; simp [he] at hs
  have hn1 : s≠1 := by intro he; simp [he] at hs
  rw [E_eq_explicit hn0 hn1]
  exact h s hs

end
end MasulloRH.SynthesisStrip
end StandaloneSynthGenerator


-- Local source: SynthMinimumGenerator
section StandaloneSynthMinimumGenerator
open MeasureTheory
namespace MasulloRH.SynthesisStrip

/-- Transfer the verified minimum-modulus estimate to the logarithmic theta transform. -/
theorem E_minimum (a b : ℝ) (ha : 0<a) (hb : b<1) (d : ℝ) (hd : 0<d) (A : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ s : ℂ, a ≤ s.re → s.re≤b →
      (∀ v : ℂ, riemannZeta v=0 → 0<v.re → v.re<1 → |v.im-s.im|≤3 →
        d/(1+|s.im|)^A ≤ ‖s-v‖) →
      E s≠0 ∧ max 0 (-Real.log ‖E s‖) ≤ D*(1+|s.im|)^2 := by
  obtain ⟨D,hD,h⟩ := MasulloRH.dyadic_theta_minimum_modulus_in_zero_separated_strips a b ha hb d hd A
  refine ⟨D,hD,fun s h₁ h₂ hs => ?_⟩
  have he := (E_strip s (ha.trans_le h₁) (h₂.trans_lt hb)).1
  rw [he]
  exact h s h₁ h₂ hs

end MasulloRH.SynthesisStrip
end StandaloneSynthMinimumGenerator


-- Local source: SynthWallDivision
section StandaloneSynthWallDivision
open Set
open scoped SchwartzMap ContDiff

namespace MasulloRH.SynthWall
noncomputable section

private def Q (x : ℝ) := (1+|x|)^2
private theorem q_nonneg (x : ℝ) : 0 ≤ Q x := sq_nonneg _

private def GaussianGrowth (f : ℝ→ℂ) : Prop :=
  ∃ A B : ℝ, 0≤A ∧ 0≤B ∧ ∀ x, ‖f x‖ ≤ B*Real.exp (A*Q x)

private theorem bounded_growth {f : ℝ→ℂ} {C : ℝ} (hf : ∀ x, ‖f x‖≤C) :
    GaussianGrowth f := ⟨0,|C|,le_rfl,abs_nonneg _,fun x => by simpa using (hf x).trans (le_abs_self _)⟩

private theorem grow_const (a : ℂ) : GaussianGrowth (fun _ => a) :=
  bounded_growth (C:=‖a‖) (fun _ => le_rfl)

private theorem grow_add {f g : ℝ→ℂ} (hf : GaussianGrowth f) (hg : GaussianGrowth g) :
    GaussianGrowth (fun x => f x+g x) := by
  obtain ⟨A,B,hA,hB,hf⟩ := hf
  obtain ⟨a,b,ha,hb,hg⟩ := hg
  refine ⟨A+a,B+b,by positivity,by positivity,fun x => ?_⟩
  apply (norm_add_le _ _).trans ((add_le_add (hf x) (hg x)).trans ?_)
  rw [add_mul B]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hB
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ha) (q_nonneg _)
  · apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hb
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (q_nonneg _)

private theorem grow_mul {f g : ℝ→ℂ} (hf : GaussianGrowth f) (hg : GaussianGrowth g) :
    GaussianGrowth (fun x => f x*g x) := by
  obtain ⟨A,B,hA,hB,hf⟩ := hf
  obtain ⟨a,b,ha,hb,hg⟩ := hg
  refine ⟨A+a,B*b,by positivity,by positivity,fun x => ?_⟩
  rw [norm_mul]
  apply (mul_le_mul (hf x) (hg x) (norm_nonneg _) (by positivity)).trans_eq
  rw [add_mul,Real.exp_add]
  ring

private theorem grow_sum {ι : Type*} (s : Finset ι) (f : ι→ℝ→ℂ)
    (hf : ∀ i∈s, GaussianGrowth (f i)) :
    GaussianGrowth (fun x => ∑ i∈s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using grow_const 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact grow_add (hf i (by simp)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem reciprocal_deriv_growth (E : ℝ→ℂ) (hE : ContDiff ℝ ∞ E) (hn : ∀ x, E x≠0)
    (he : ∀ j : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedDeriv j E x‖≤C)
    (hi : GaussianGrowth (fun x => (E x)⁻¹)) (j : ℕ) :
    GaussianGrowth (iteratedDeriv j (fun x => (E x)⁻¹)) := by
  let g : ℝ→ℂ := fun x => (E x)⁻¹
  have hg : ContDiff ℝ ∞ g := hE.inv hn
  change GaussianGrowth (iteratedDeriv j g)
  induction j using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|n
    · simpa using hi
    · let d := n+1
      let T (i : ℕ) (x : ℝ) := (d.choose i:ℂ)*iteratedDeriv i g x*iteratedDeriv (d-i) E x
      have hfinite : GaussianGrowth (fun x => ∑ i∈Finset.range d, T i x) := by
        apply grow_sum
        intro i hi'
        obtain ⟨c,hc⟩ := he (d-i)
        exact grow_mul (grow_mul (grow_const _) (ih i (Finset.mem_range.mp hi'))) (bounded_growth hc)
      have hfun : iteratedDeriv d g = fun x => ((-1:ℂ)*(∑ i∈Finset.range d, T i x))*g x := by
        funext x
        have hone : g*E=fun _ => (1:ℂ) := funext (fun x => inv_mul_cancel₀ (hn x))
        have hprod := iteratedDeriv_mul (n:=d) (f:=g) (g:=E) (hg.contDiffAt.of_le (mod_cast le_top)) (hE.contDiffAt.of_le (mod_cast le_top)) (x:=x)
        rw [hone] at hprod
        change iteratedDeriv d (fun _ : ℝ => (1:ℂ)) x = ∑ i∈Finset.range (d+1), T i x at hprod
        simp only [d,iteratedDeriv_const, Nat.succ_ne_zero, ↓reduceIte] at hprod
        change 0 = ∑ i∈Finset.range (d+1), T i x at hprod
        rw [Finset.sum_range_succ] at hprod
        have heq : T d x = iteratedDeriv d g x * E x := by simp [T]
        rw [heq] at hprod
        change _ = _ * (E x)⁻¹
        rw [←div_eq_mul_inv,eq_div_iff (hn x)]
        linear_combination -hprod
      rw [show n+1=d from rfl,hfun]
      exact grow_mul (grow_mul (grow_const _) hfinite) hi

private def PolyBound (k : ℕ) (f : ℝ→ℂ) := ∃ C : ℝ, 0≤C ∧ ∀ x, |x|^k*‖f x‖≤C

private theorem poly_add {k : ℕ} {f g : ℝ→ℂ} (hf : PolyBound k f) (hg : PolyBound k g) :
    PolyBound k (fun x => f x+g x) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D,add_nonneg hC hD,fun x => ?_⟩
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity : 0≤|x|^k)).trans
  rw [mul_add]
  exact add_le_add (hf x) (hg x)

private theorem poly_sum {ι : Type*} (k : ℕ) (s : Finset ι) (f : ι→ℝ→ℂ)
    (hf : ∀ i∈s, PolyBound k (f i)) : PolyBound k (fun x => ∑ i∈s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0,le_rfl,?_⟩
    simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact poly_add (hf _ (by simp)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Division of a faster-than-Gaussian smooth window by a smooth nonzero multiplier
whose derivatives are bounded and whose reciprocal grows at most like a Gaussian. -/
theorem schwartz_division (E D : ℝ→ℂ) (hE : ContDiff ℝ ∞ E) (hD : ContDiff ℝ ∞ D)
    (hn : ∀ x, E x≠0) (he : ∀ j : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedDeriv j E x‖≤C)
    (A : ℝ) (hA : 0≤A) (hi : ∀ x, ‖(E x)⁻¹‖ ≤ Real.exp (A*(1+|x|)^2))
    (hd : ∀ j k : ℕ, ∀ C : ℝ, 0≤C → ∃ B : ℝ, 0≤B ∧ ∀ x : ℝ,
      |x|^k*‖iteratedDeriv j D x‖*Real.exp (C*(1+|x|)^2)≤B) :
    ∃ W : 𝓢(ℝ,ℂ), ∀ x : ℝ, W x=D x/E x := by
  let g : ℝ→ℂ := fun x => (E x)⁻¹
  have hg : ContDiff ℝ ∞ g := hE.inv hn
  have hgi : GaussianGrowth g := ⟨A,1,hA,by norm_num,fun x => by simpa [Q,g] using hi x⟩
  refine ⟨{toFun := D*g,smooth' := hD.mul hg,decay' := ?_},fun x => (div_eq_mul_inv _ _).symm⟩
  intro k n
  let T (i : ℕ) (x : ℝ) := (n.choose i : ℂ)*iteratedDeriv i D x*iteratedDeriv (n-i) g x
  have hT : PolyBound k (fun x => ∑ i∈Finset.range (n+1), T i x) := by
    apply poly_sum
    intro i _
    obtain ⟨a,b,ha,hb,h⟩ := reciprocal_deriv_growth E hE hn he hgi (n-i)
    obtain ⟨Q₀,hQ,hD'⟩ := hd i k a ha
    refine ⟨(n.choose i:ℝ)*b*Q₀,by positivity,fun x => ?_⟩
    dsimp only [T]
    simp only [norm_mul,Complex.norm_natCast]
    calc
      _ ≤ |x|^k*((n.choose i:ℝ)*‖iteratedDeriv i D x‖*(b*Real.exp (a*Q x))) := by gcongr; exact h x
      _ = ((n.choose i:ℝ)*b)*(|x|^k*‖iteratedDeriv i D x‖*Real.exp (a*Q x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hD' x) (by positivity)
  obtain ⟨B,_,h⟩ := hT
  refine ⟨B,fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs,iteratedDeriv_mul (n:=n) (f:=D) (g:=g)
    (hD.contDiffAt.of_le (mod_cast le_top)) (hg.contDiffAt.of_le (mod_cast le_top))]
  exact h x

end
end MasulloRH.SynthWall
end StandaloneSynthWallDivision


-- Local source: SynthDamping
section StandaloneSynthDamping
open Set MeasureTheory Filter
open scoped Topology
namespace MasulloRH.SynthesisStrip
noncomputable section

/-- Quartic damping after scaling in the Laplace variable. -/
def damp (ε : ℝ) (s : ℂ) := Complex.exp (-((ε:ℂ)*s)^4)

theorem damp_entire (ε : ℝ) : Differentiable ℂ (damp ε) := by unfold damp; fun_prop
theorem damp_scale (ε : ℝ) (s : ℂ) : damp ε s=damp 1 ((ε:ℂ)*s) := by simp [damp]

theorem quartic_re (s : ℂ) : (s^4).re = s.re^4-6*s.re^2*s.im^2+s.im^4 := by
  rw [pow_succ,pow_succ,pow_two]
  simp only [Complex.mul_re,Complex.mul_im]
  ring

private theorem quartic_lower (s : ℂ) {b : ℝ} (hb : |s.re|≤b) :
    s.im^4/2-18*b^4 ≤ (s^4).re := by
  have hp := pow_le_pow_left₀ (abs_nonneg _) hb 4
  rw [show |s.re|^4=s.re^4 by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]] at hp
  rw [quartic_re]
  nlinarith only [sq_nonneg (s.im^2-6*s.re^2),sq_nonneg (s.re^2),hp]

/-- On any fixed real-part band the quartic dominates every quadratic exponential,
with one full exponential left for integration. -/
theorem damp_dominates (ε b L : ℝ) (hε : 0<ε) (hL : 0≤L) :
    ∃ C : ℝ, 0<C ∧ ∀ s : ℂ, |s.re|≤b →
    ‖damp ε s‖ * Real.exp (L*(1+|s.im|)^2) ≤ C * Real.exp (-2*|s.im|) := by
  let a := ε^4
  let B := 2*L+2
  have ha : 0<a := pow_pos hε 4
  refine ⟨Real.exp (18*a*b^4+2*L+2+B^2/(2*a)),Real.exp_pos _,fun s hs => ?_⟩
  have hq := mul_le_mul_of_nonneg_left (quartic_lower s hs) ha.le
  have hsq : B*s.im^2 ≤ a*s.im^4/2+B^2/(2*a) := by
    have hh := sq_nonneg (a*s.im^2-B)
    field_simp
    nlinarith only [hh]
  have hlin : L*(1+|s.im|)^2+2*|s.im| ≤ 2*L+2+B*s.im^2 := by
    dsimp [B]
    have h2 : (1+|s.im|)^2≤2+2*s.im^2 := by nlinarith [sq_nonneg (|s.im|-1),sq_abs s.im]
    nlinarith only [mul_le_mul_of_nonneg_left h2 hL,sq_nonneg (|s.im|-1),sq_abs s.im,sq_nonneg s.im]
  rw [damp,Complex.norm_exp,←Real.exp_add,←Real.exp_add,Real.exp_le_exp,Complex.neg_re,mul_pow,
    ←Complex.ofReal_pow,Complex.re_ofReal_mul]
  dsimp only [a] at *
  linarith

theorem damp_hasDerivAt (ε : ℝ) (s : ℂ) :
    HasDerivAt (damp ε) (((-4:ℂ)*(ε:ℂ)^4*s^3)*damp ε s) s := by
  have h := ((((hasDerivAt_id s).const_mul (ε:ℂ)).pow 4).neg.cexp)
  unfold damp
  convert! h using 1
  dsimp; ring

theorem damp_deriv_polynomial (ε : ℝ) (j : ℕ) :
    ∃ P : Polynomial ℂ, iteratedDeriv j (damp ε) = fun s => P.eval s * damp ε s := by
  induction j with
  | zero => exact ⟨1,by funext s; simp⟩
  | succ j ih =>
    obtain ⟨P,hP⟩ := ih
    refine ⟨P.derivative+P*(Polynomial.C ((-4:ℂ)*(ε:ℂ)^4)*Polynomial.X^3),?_⟩
    funext s
    rw [iteratedDeriv_succ,hP]
    change deriv ((fun x => P.eval x) * damp ε) s = _
    rw [((P.hasDerivAt s).mul (damp_hasDerivAt ε s)).deriv]
    simp; ring

end
end MasulloRH.SynthesisStrip
end StandaloneSynthDamping


-- Local source: SynthGeneratorDeriv
section StandaloneSynthGeneratorDeriv
open Set Filter MeasureTheory
open scoped Topology
namespace MasulloRH.SynthesisStrip
noncomputable section

theorem E_deriv_band_bound (a : ℝ) (j : ℕ) :
    ∃ M : ℝ, 0≤M ∧ ∀ s : ℂ, |s.re|≤a → ‖iteratedDeriv j E s‖≤M := by
  let g (x : ℝ) := ‖seed x‖*Real.exp ((a+2)*|x|)
  have hi : Integrable g := seed_weighted _
  let C := (j.factorial:ℝ)
  have hc : 0≤C := Nat.cast_nonneg _
  refine ⟨∫x,C*g x,integral_nonneg (fun x => mul_nonneg hc (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))),fun s hs => ?_⟩
  have h₁ : |(s-1/2).re|≤a+1 := by
    simp only [Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]
    exact (abs_sub _ _).trans (by rw [abs_of_pos (by norm_num : (0:ℝ)<1/2)]; linarith)
  have hj : iteratedDeriv j E s=StripPhysical.moment seed (s-1/2) j := by
    unfold E
    rw [iteratedDeriv_comp_sub_const]
    exact StripTrace.lap_iteratedDeriv seed_cont.aestronglyMeasurable (seed_weighted (a+2)) j (h₁.trans_lt (by linarith))
  rw [hj,StripPhysical.moment]
  apply norm_integral_le_of_norm_le (hi.const_mul C)
  filter_upwards with x
  have hr : (s-1/2).re*x≤(a+1)*|x| :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right h₁ (abs_nonneg _)))
  have hp : |x|^j≤C*Real.exp |x| := by
    have h := (div_le_iff₀ (Nat.cast_pos.mpr j.factorial_pos : 0<(j.factorial:ℝ))).mp
      (Real.pow_div_factorial_le_exp (abs x) (abs_nonneg x) j)
    simpa [C,mul_comm] using h
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) (Real.exp_le_exp.mpr hr)
    (Real.exp_nonneg _) (by positivity)).trans_eq
  dsimp only [g]
  rw [show (a+2)*|x|=|x|+(a+1)*|x| by ring,Real.exp_add]
  ring

end
end MasulloRH.SynthesisStrip
end StandaloneSynthGeneratorDeriv


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


-- Local source: SynthDampingDeriv
section StandaloneSynthDampingDeriv
open Set Filter
open scoped Topology
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall (vertical)

theorem vertical_derivatives (f : ℂ→ℂ) (hf : Differentiable ℂ f) (σ : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun t : ℝ => f (vertical σ t)) t =
      Complex.I^j*iteratedDeriv j f (vertical σ t) := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    have hd := (show ContDiff ℂ ⊤ f from hf.contDiff).differentiable_iteratedDeriv j (by simp)
    let w := vertical σ t
    have h₁ : HasDerivAt (fun z : ℂ => (σ:ℂ)+z*Complex.I) Complex.I (t:ℂ) := by
      simpa using (((hasDerivAt_id (t:ℂ)).mul_const Complex.I).const_add (σ:ℂ))
    have h₂ := ((hd w).hasDerivAt.comp (t:ℂ) h₁).comp_ofReal.const_mul (Complex.I^j)
    rw [iteratedDeriv_succ,show iteratedDeriv j (fun t : ℝ => f (vertical σ t)) =
      fun t : ℝ => Complex.I^j*iteratedDeriv j f (vertical σ t) from funext ih]
    apply h₂.deriv.trans
    rw [iteratedDeriv_succ,pow_succ]; ring

theorem vertical_E_bound (σ : ℝ) (j : ℕ) :
    ∃ M : ℝ, 0≤M ∧ ∀ t : ℝ, ‖iteratedDeriv j (fun t : ℝ => E (vertical σ t)) t‖ ≤ M := by
  obtain ⟨M,hM,h⟩ := E_deriv_band_bound |σ| j
  refine ⟨M,hM,fun t => ?_⟩
  rw [vertical_derivatives E E_entire,norm_mul,norm_pow,Complex.norm_I,one_pow,one_mul]
  exact h _ (by simp)

private theorem pow_abs_bound (x : ℝ) (hx : 0≤x) (j : ℕ) :
    x^j≤(j.factorial:ℝ)*Real.exp x := by
  have h := (div_le_iff₀ (Nat.cast_pos.mpr j.factorial_pos : 0<(j.factorial:ℝ))).mp (Real.pow_div_factorial_le_exp x hx j)
  simpa [mul_comm] using h

theorem polynomial_vertical_bound (P : Polynomial ℂ) (σ : ℝ) :
    ∃ M : ℝ, 0≤M ∧ ∀ t : ℝ, ‖P.eval (vertical σ t)‖≤M*Real.exp |t| := by
  let A (i : ℕ) := ‖P.coeff i‖ * (i.factorial:ℝ) * Real.exp |σ|
  refine ⟨∑ i∈ Finset.range (P.natDegree+1),A i, Finset.sum_nonneg (fun i _ => by dsimp [A]; positivity),fun t => ?_⟩
  rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  apply (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  have hn : ‖vertical σ t‖≤|σ|+|t| := by simpa using Complex.norm_le_abs_re_add_abs_im (vertical σ t)
  have hp := (pow_abs_bound _ (norm_nonneg _) i).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hn) (Nat.cast_nonneg _))
  rw [norm_mul,norm_pow]
  apply (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq
  rw [Real.exp_add]; dsimp [A]; ring

theorem vertical_damp_rapid (ε σ : ℝ) (hε : 0<ε) (j k : ℕ) (A : ℝ) (hA : 0≤A) :
    ∃ B : ℝ, 0≤B ∧ ∀ t : ℝ, |t|^k * ‖iteratedDeriv j (fun t : ℝ => damp ε (vertical σ t)) t‖ *
      Real.exp (A*(1+|t|)^2) ≤ B := by
  obtain ⟨P,hP⟩ := damp_deriv_polynomial ε j
  obtain ⟨M,hM,hp⟩ := polynomial_vertical_bound P σ
  obtain ⟨C,hC,hc⟩ := damp_dominates ε |σ| A hε hA
  refine ⟨(k.factorial:ℝ)*M*C,by positivity,fun t => ?_⟩
  have h := hc (vertical σ t) (by simp)
  rw [SynthWall.vertical_im] at h
  rw [vertical_derivatives _ (damp_entire ε),hP,norm_mul,norm_pow,Complex.norm_I,one_pow,one_mul,norm_mul]
  calc
    _ = (|t|^k*‖P.eval (vertical σ t)‖)*(‖damp ε (vertical σ t)‖*Real.exp (A*(1+|t|)^2)) := by ring
    _ ≤ ((k.factorial:ℝ)*Real.exp |t| *(M*Real.exp |t|))*(C*Real.exp (-2*|t|)) :=
      mul_le_mul (mul_le_mul (pow_abs_bound _ (abs_nonneg _) _) (hp t) (norm_nonneg _) (by positivity)) h
        (by positivity) (by positivity)
    _ = _ := by
      rw [show -2*|t|= -(|t|+|t|) by ring,Real.exp_neg,Real.exp_add]
      field_simp

end
end MasulloRH.SynthesisStrip
end StandaloneSynthDampingDeriv


-- Local source: SynthQuotient
section StandaloneSynthQuotient
open Filter Set Metric
open scoped Topology
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall

/-- Total division with an isolated zero filled by the punctured limit. -/
def filledRatio (F G : ℂ→ℂ) (z : ℂ) : ℂ :=
  if G z=0 then limUnder (𝓝[≠] z) (fun w => F w/G w) else F z/G z

private theorem filled_eq_near_nonzero {F G : ℂ→ℂ} {z : ℂ}
    (hg : ContinuousAt G z) (hn : G z≠0) :
    filledRatio F G =ᶠ[𝓝 z] fun w => F w/G w :=
  (hg.eventually_ne hn).mono (fun _ hw => if_neg hw)

private theorem filled_analytic {F G : ℂ→ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hG : AnalyticAt ℂ G z) (hfinite : analyticOrderAt G z≠⊤)
    (horder : G z=0 → analyticOrderAt G z ≤ analyticOrderAt F z) :
    AnalyticAt ℂ (filledRatio F G) z := by
  by_cases hn : G z=0
  · obtain ⟨g,hg,hg0,hg'⟩ := hG.analyticOrderAt_ne_top.mp hfinite
    obtain ⟨f,hf,hf'⟩ := (natCast_le_analyticOrderAt hF).mp
      ((ENat.natCast_toNat_le_self _).trans (horder hn))
    have hraw : (fun w => F w/G w) =ᶠ[𝓝[≠] z] (fun w => f w/g w) := by
      filter_upwards [hg'.filter_mono nhdsWithin_le_nhds,hf'.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with w hw hfw hnw
      have hwz : w-z≠0 := sub_ne_zero.mpr hnw
      rw [hfw,hw]
      simp only [smul_eq_mul]
      exact mul_div_mul_left _ _ (pow_ne_zero _ hwz)
    have hgn : ∀ᶠ w in 𝓝[≠] z, G w≠0 := by
      filter_upwards [hg'.filter_mono nhdsWithin_le_nhds,
        (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
        with w hw hgn hwz
      rw [hw,smul_eq_mul]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hwz)) hgn
    have hfg : AnalyticAt ℂ (fun w => f w/g w) z := hf.div hg hg0
    have hs : filledRatio F G =ᶠ[𝓝[≠] z] (fun w => f w/g w) := by
      apply EventuallyEq.trans _ hraw
      exact hgn.mono (fun _ hw => if_neg hw)
    have hpoint : filledRatio F G z = f z/g z := by
      rw [filledRatio,if_pos hn]
      exact ((hfg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hraw.symm).limUnder_eq
    exact hfg.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hs hpoint).symm
  · exact (hF.fun_div hG hn).congr (filled_eq_near_nonzero hG.continuousAt hn).symm

def centeredE (s : ℂ) := E (s+1/2)

theorem centeredE_analytic (s : ℂ) : AnalyticAt ℂ centeredE s :=
  (E_entire.analyticAt _).comp (analyticAt_id.add analyticAt_const)

theorem centeredE_order (s : ℂ) : analyticOrderAt centeredE s=analyticOrderAt E (s+1/2) := by
  let g := fun w : ℂ => w+1/2
  have ha : AnalyticAt ℂ g s := analyticAt_id.add analyticAt_const
  have hd : deriv g s=1 := ((hasDerivAt_id s).add_const _).deriv
  exact analyticOrderAt_comp_of_deriv_ne_zero (f:=E) ha (by rw [hd]; exact one_ne_zero)

private theorem centeredE_finite (s : ℂ) : analyticOrderAt centeredE s≠⊤ := by
  intro htop
  rw [centeredE_order] at htop
  have h := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (s+1/2) E_entire.analyticAt).mp htop
  obtain ⟨C,_,ha⟩ := E_anchor
  have hc := ha 2 (by norm_num)
  simp [h] at hc
  norm_num at hc

/-- Centered holomorphic quotient with the interior zeros removed. -/
def dividedTransform (ε : ℝ) (F : ℂ→ℂ) (s : ℂ) := damp ε s * filledRatio F centeredE s

theorem dividedTransform_eq (ε : ℝ) (F : ℂ→ℂ) (s : ℂ) (hs : E (s+1/2)≠0) :
    dividedTransform ε F s = damp ε s*F s/E (s+1/2) := by
  have hn : centeredE s ≠ 0 := hs
  rw [dividedTransform,filledRatio,if_neg hn]
  exact (mul_div_assoc _ _ _).symm

theorem dividedTransform_regular (b ε : ℝ) (F : ℂ→ℂ)
    (hF : ContinuousOn F (closedStrip b)) (ha : AnalyticOnNhd ℂ F (openStrip b))
    (ho : ∀ s ∈ openStrip b, E (s+1/2)=0 → analyticOrderAt E (s+1/2)≤analyticOrderAt F s)
    (hwall : ∀ s : ℂ, |s.re|=b → E (s+1/2)≠0) :
    ContinuousOn (dividedTransform ε F) (closedStrip b) ∧
      DifferentiableOn ℂ (dividedTransform ε F) (openStrip b) := by
  have hq (s : ℂ) (hs : s∈openStrip b) : AnalyticAt ℂ (dividedTransform ε F) s :=
    (damp_entire ε).analyticAt s |>.mul (filled_analytic (ha s hs) (centeredE_analytic s)
      (centeredE_finite s) (fun hz => (centeredE_order s).le.trans (ho s hs hz)))
  refine ⟨?_,fun s hs => (hq s hs).differentiableAt.differentiableWithinAt⟩
  intro s hs
  obtain hs|hs := lt_or_eq_of_le (show |s.re|≤b from hs)
  · exact (hq s hs).continuousAt.continuousWithinAt
  · have hg := (centeredE_analytic s).continuousAt
    have hn : centeredE s≠0 := hwall s hs
    have hcont := (hF s hs.le).div hg.continuousWithinAt hn
    have he := filled_eq_near_nonzero (F:=F) hg hn
    exact ((damp_entire ε s).continuousAt.continuousWithinAt).mul
      (hcont.congr_of_eventuallyEq_of_mem (he.filter_mono nhdsWithin_le_nhds) hs.le)

end
end MasulloRH.SynthesisStrip
end StandaloneSynthQuotient


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


-- Local source: SynthQuotientEstimates
section StandaloneSynthQuotientEstimates
open Set Filter MeasureTheory FourierTransform
open scoped Topology SchwartzMap FourierTransform ContDiff
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall

/-- Polynomial separation of the uncentered zeta divisor from a centered Laplace point. -/
def Avoids (d : ℝ) (A : ℕ) (s : ℂ) := ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re<1 →
    |ρ.im-s.im|≤3 → d/(1+|s.im|)^A ≤ ‖s+1/2-ρ‖

private theorem centered_minimum (b : ℝ) (hb : b<1/2) (d : ℝ) (hd : 0<d) (A : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ s ∈ closedStrip b, Avoids d A s →
      centeredE s ≠ 0 ∧ ‖(centeredE s)⁻¹‖ ≤ Real.exp (D*(1+|s.im|)^2) := by
  obtain ⟨D,hD,h⟩ := E_minimum (1/2-b) (1/2+b) (by linarith) (by linarith) d hd A
  refine ⟨D,hD,?_⟩
  intro s hs sep
  have hsr : (s+1/2).re=s.re+1/2 := by simp
  have hsi : (s+1/2).im=s.im := by simp
  obtain ⟨hs₁,hs₂⟩ := abs_le.mp (show |s.re|≤b from hs)
  obtain ⟨hn,hh⟩ := h (s+1/2) (by rw [hsr]; linarith) (by rw [hsr]; linarith)
    (by simpa only [Avoids,hsi] using sep)
  refine ⟨hn,?_⟩
  have hh' := Real.exp_le_exp.mpr ((le_max_right _ _).trans hh)
  rw [Real.exp_neg,Real.exp_log (norm_pos_iff.mpr hn),hsi] at hh'
  simpa only [centeredE,norm_inv] using hh'

/-- On cofinal horizontal lines avoiding the divisor, the regularized quotient
tends uniformly to zero on the full horizontal segments. -/
theorem quotient_good_heights (b ε : ℝ) (hb : b<1/2) (hε : 0<ε)
    (F : ℂ→ℂ) (M : ℝ) (hM : 0≤M) (hF : ∀ s∈closedStrip b, ‖F s‖≤M)
    (d : ℝ) (hd : 0<d) (A : ℕ) (T : ℕ→ℝ) (ht : Tendsto T atTop atTop)
    (hsep : ∀ n u, |u|≤b → Avoids d A (vertical u (T n)) ∧ Avoids d A (vertical u (-T n))) :
    GoodHeights (dividedTransform ε F) b := by
  obtain ⟨D,hD,h⟩ := centered_minimum b hb d hd A
  obtain ⟨C,hC,hc⟩ := damp_dominates ε b D hε hD.le
  have hlocal (s : ℂ) (hs : s∈closedStrip b) (hsep : Avoids d A s) :
      ‖dividedTransform ε F s‖≤(M*C)*Real.exp (-2*|s.im|) := by
    obtain ⟨hn,hi⟩ := h s hs hsep
    rw [dividedTransform_eq _ _ _ hn,div_eq_mul_inv,norm_mul,norm_mul]
    change ‖damp ε s‖*‖F s‖*‖(centeredE s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖damp ε s‖*M*Real.exp (D*(1+|s.im|)^2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hF s hs) (norm_nonneg _)) hi (norm_nonneg _) (by positivity)
      _ = M*(‖damp ε s‖*Real.exp (D*(1+|s.im|)^2)) := by ring
      _ ≤ M*(C*Real.exp (-2*|s.im|)) := mul_le_mul_of_nonneg_left (hc s hs) hM
      _ = _ := (mul_assoc _ _ _).symm
  refine ⟨T,fun n => (M*C)*Real.exp (-2*T n),ht,?_,?_⟩
  · have hn : Tendsto (fun n => -(2*T n)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp ((tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<2)).2 ht)
    simpa [neg_mul] using (Real.tendsto_exp_atBot.comp hn).const_mul (M*C)
  · intro n u hu
    have apply_one (t : ℝ) (ht : |t|=|T n|) (hs : Avoids d A (vertical u t)) :
        ‖dividedTransform ε F (vertical u t)‖ ≤ M*C*Real.exp (-2*T n) := by
      apply (hlocal _ (by simpa [closedStrip] using hu) hs).trans
      simp only [vertical_im,ht]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (mul_nonneg hM hC.le)
      linarith [le_abs_self (T n)]
    exact ⟨apply_one _ rfl (hsep n u hu).1,apply_one _ (abs_neg _) (hsep n u hu).2⟩

/-- A Schwartz multiplier on the Fourier-normalized wall for the centered damped quotient. -/
theorem quotient_wall_multiplier (σ ε : ℝ) (hσ : |σ|<1/2) (hε : 0<ε)
    (d : ℝ) (hd : 0<d) (A : ℕ) (hsep : ∀ t, Avoids d A (vertical σ t)) :
    ∃ W : 𝓢(ℝ,ℂ), ∀ ξ : ℝ, W ξ =
      damp ε (vertical σ (freq*ξ)) / centeredE (vertical σ (freq*ξ)) := by
  obtain ⟨C,hC,h⟩ := centered_minimum |σ| hσ d hd A
  have hcomp (t : ℝ) : centeredE (vertical σ t) = E (vertical (σ+1/2) t) := by
    unfold centeredE vertical
    push_cast
    ring_nf
  have hfun : (fun t => centeredE (vertical σ t))=(fun t => E (vertical (σ+1/2) t)) := funext hcomp
  have hh (t : ℝ) := h (vertical σ t) (by simp [closedStrip]) (hsep t)
  have hsmooth (f : ℂ→ℂ) (hf : Differentiable ℂ f) (a : ℝ) :
      ContDiff ℝ ∞ (fun t : ℝ => f (vertical a t)) :=
    ((hf.contDiff : ContDiff ℂ ∞ f).restrict_scalars ℝ).comp
      (show ContDiff ℝ ∞ (vertical a) from contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const))
  obtain ⟨v,hv⟩ := SynthWall.schwartz_division (fun t => centeredE (vertical σ t)) _
    (hfun ▸ hsmooth _ E_entire (σ+1/2)) (hsmooth _ (damp_entire ε) σ) (fun t => (hh t).1)
    (fun j => by obtain ⟨B,_,hB⟩ := vertical_E_bound (σ+1/2) j; exact ⟨B,hfun ▸ hB⟩)
    C hC.le (fun t => by simpa using (hh t).2) (vertical_damp_rapid ε σ hε)
  let scale : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 freq freq_ne_zero)
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scale v,fun ξ => hv (freq*ξ)⟩

end
end MasulloRH.SynthesisStrip
end StandaloneSynthQuotientEstimates


-- Local source: SynthSeparation
section StandaloneSynthSeparation
open Set Filter MeasureTheory
open scoped Topology
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall (vertical)

private def asZero (ρ : ℂ) (hz : riemannZeta ρ=0) (h₀ : 0<ρ.re) (h₁ : ρ.re<1) : DivisorZero :=
  ⟨ρ,hz,h₀,h₁,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

private theorem local_radius {c : ℝ} (hc : 0<c) (z : DivisorZero) (t : ℝ) (ht : |z.val.im-t|≤3) :
    (c/16)/(1+|t|)^2 ≤ c*sepWeight z := by
  have hh : |z.val.im|≤3+|t| := by
    have h := abs_add_le (z.val.im-t) t
    rw [sub_add_cancel] at h
    linarith
  have hh' := pow_le_pow_left₀ (abs_nonneg _) hh 2
  rw [sq_abs] at hh'
  have hq : 1+z.val.im^2 ≤ 16*(1+|t|)^2 := by nlinarith [abs_nonneg t,sq_nonneg |t|]
  dsimp [sepWeight]
  rw [←div_mul_eq_div_div, mul_one_div]
  exact div_le_div_of_nonneg_left hc.le (by positivity) hq

theorem ae_wall_separation :
    ∀ᵐ b : ℝ, ∃ d : ℝ, 0<d ∧ ∀ t : ℝ, Avoids d 2 (vertical b t) ∧ Avoids d 2 (vertical (-b) t) := by
  filter_upwards [ae_separated (fun z => z.val.re-1/2)] with b h
  obtain ⟨c,hc,h⟩ := h
  refine ⟨c/16,by positivity,fun t => ?_⟩
  have hside (u : ℝ) (hs : ∀ z : DivisorZero, c*sepWeight z≤|u-(z.val.re-1/2)|) :
      Avoids (c/16) 2 (vertical u t) := by
    intro ρ hz h₀ h₁ ht
    let z := asZero ρ hz h₀ h₁
    have hr := local_radius hc z t (by simpa [z,asZero] using ht)
    rw [SynthWall.vertical_im]
    apply hr.trans ((hs z).trans ?_)
    have hnorm := Complex.abs_re_le_norm (vertical u t+1/2-ρ)
    have he : (vertical u t+1/2-ρ).re = u-(z.val.re-1/2) := by simp [z,asZero]; ring
    rwa [he] at hnorm
  refine ⟨hside b (fun z => (h z).1),hside (-b) (fun z => ?_)⟩
  rw [show -b-(z.val.re-1/2) = -(b+(z.val.re-1/2)) by ring,abs_neg]
  exact (h z).2

theorem exists_horizontal_separation :
    ∃ d : ℝ, 0<d ∧ ∃ T : ℕ→ℝ, (∀ n : ℕ, T n∈Icc (n:ℝ) (n+1)) ∧
      Tendsto T atTop atTop ∧ ∀ (n : ℕ) (u : ℝ), Avoids d 2 (vertical u (T n)) ∧ Avoids d 2 (vertical u (-(T n))) := by
  obtain ⟨c,hc,h⟩ := horizontal_separated (fun z => z.val.im)
  choose T hT hd using h
  refine ⟨c/16,by positivity,T,hT,tendsto_atTop_mono (fun n => (hT n).1) tendsto_natCast_atTop_atTop,fun n u => ?_⟩
  have hside (t : ℝ) (hs : ∀ z : DivisorZero, c*sepWeight z≤|t-z.val.im|) :
      Avoids (c/16) 2 (vertical u t) := by
    intro ρ hz h₀ h₁ ht
    let z := asZero ρ hz h₀ h₁
    have hr := local_radius hc z t (by simpa [z,asZero] using ht)
    rw [SynthWall.vertical_im]
    apply hr.trans ((hs z).trans ?_)
    simpa [z,asZero] using Complex.abs_im_le_norm (vertical u t+1/2-ρ)
  refine ⟨hside (T n) (fun z => (hd n z).1),hside (-(T n)) (fun z => ?_)⟩
  rw [show -(T n)-z.val.im= -(T n+z.val.im) by ring,abs_neg]
  exact (hd n z).2

end
end MasulloRH.SynthesisStrip
end StandaloneSynthSeparation


-- Local source: SynthL2Walls
section StandaloneSynthL2Walls
open Filter Set MeasureTheory
open scoped Topology
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall (vertical)

def GoodWall (d b : ℝ) : Prop :=
  ∀ t : ℝ, Avoids d 2 (vertical b t) ∧ Avoids d 2 (vertical (-b) t)

private lemma goodWall_mono {e d b : ℝ} (hed : e≤d) (h : GoodWall d b) : GoodWall e b := by
  have hmono {s : ℂ} (hs : Avoids d 2 s) : Avoids e 2 s :=
    fun ρ hρ h₀ h₁ ht => (div_le_div_of_nonneg_right hed (by positivity)).trans (hs ρ hρ h₀ h₁ ht)
  exact fun t => ⟨hmono (h t).1,hmono (h t).2⟩

private theorem ae_left_accumulation (s : Set ℝ) : ∀ᵐ x : ℝ, x∈s → NeBot (𝓝[s ∩ Iio x] x) := by
  have h := (countable_setOfPred_isolated_left_within (s:=s)).measure_zero (volume : Measure ℝ)
  filter_upwards [compl_mem_ae_iff.mpr h] with x hx hxs
  exact ⟨fun he => hx ⟨hxs,he⟩⟩

theorem ae_approaching_good_walls :
    ∀ᵐ b : ℝ, 0<b → ∃ d : ℝ, 0<d ∧ GoodWall d b ∧ ∃ B : ℕ→ℝ,
      StrictMono B ∧ Tendsto B atTop (𝓝 b) ∧ ∀ n, b/2 ≤ B n ∧ B n<b ∧ GoodWall d (B n) := by
  let c (k : ℕ) : ℝ := 1/((k:ℝ)+1)
  let S (k : ℕ) := {u : ℝ | GoodWall (c k) u}
  have hae := ae_all_iff.mpr (fun k : ℕ => ae_left_accumulation (S k))
  filter_upwards [ae_wall_separation,hae] with b hb hacc hp
  obtain ⟨d,hd,hb⟩ := hb
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hd
  have hbk : b∈S k := goodWall_mono hk.le hb
  let s := S k ∩ Iio b
  have ht : NeBot (𝓝[s] b) := hacc k hbk
  have hcl := mem_closure_iff_nhdsWithin_neBot.mpr ht
  have hne := Set.nonempty_of_mem (show b∈closure s from hcl)
  have lub := isLUB_of_mem_closure (s:=s) (a:=b) (fun x hx => hx.2.le) hcl
  obtain ⟨B,hB,hlt,hlim,hS⟩ := lub.exists_seq_strictMono_tendsto_of_notMem
    (fun h => (lt_irrefl b) h.2) (closure_nonempty_iff.mp hne)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (le_mem_nhds (show b/2<b by linarith)))
  have hm : StrictMono (fun n : ℕ => n+N) := fun i j hij => Nat.add_lt_add_right hij N
  refine ⟨c k,by dsimp [c]; positivity,hbk,fun n => B (n+N),hB.comp hm,?_,?_⟩
  · exact hlim.comp hm.tendsto_atTop
  · exact fun n => ⟨hN _ (Nat.le_add_left ..),hlt _,(hS _).1⟩

end
end MasulloRH.SynthesisStrip
end StandaloneSynthL2Walls


-- Local source: SynthL2UniformDivision
section StandaloneSynthL2UniformDivision
open Set
open scoped SchwartzMap ContDiff
namespace MasulloRH.SynthUniformWall
noncomputable section

private def Q (x : ℝ) := (1+|x|)^2
private def G {α : Type*} (t : α→ℝ) (f : α→ℂ) :=
  ∃ A B : ℝ, 0≤A ∧ 0≤B ∧ ∀ x, ‖f x‖ ≤ B*Real.exp (A*Q (t x))

private theorem gg_bdd {α : Type*} {t : α→ℝ} {f : α→ℂ} {C : ℝ} (hf : ∀ x, ‖f x‖≤C) :
    G t f := ⟨0,|C|,le_rfl,abs_nonneg _,fun x => by simpa using (hf x).trans (le_abs_self _)⟩

private theorem gg_const {α : Type*} {t : α→ℝ} (a : ℂ) : G t (fun _ => a) :=
  gg_bdd (C:=‖a‖) (fun _ => le_rfl)

private theorem gg_add {α : Type*} {t : α→ℝ} {f g : α→ℂ} (hf : G t f) (hg : G t g) :
    G t (fun x => f x+g x) := by
  obtain ⟨A,B,hA,hB,hf⟩ := hf
  obtain ⟨a,b,ha,hb,hg⟩ := hg
  refine ⟨A+a,B+b,by positivity,by positivity,fun x => ?_⟩
  apply (norm_add_le _ _).trans ((add_le_add (hf x) (hg x)).trans ?_)
  rw [add_mul B]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ha) (sq_nonneg _))) hB
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (sq_nonneg _))) hb

private theorem gg_mul {α : Type*} {t : α→ℝ} {f g : α→ℂ} (hf : G t f) (hg : G t g) :
    G t (fun x => f x*g x) := by
  obtain ⟨A,B,hA,hB,hf⟩ := hf
  obtain ⟨a,b,ha,hb,hg⟩ := hg
  refine ⟨A+a,B*b,by positivity,by positivity,fun x => ?_⟩
  rw [norm_mul]
  apply (mul_le_mul (hf x) (hg x) (norm_nonneg _) (by positivity)).trans_eq
  rw [add_mul,Real.exp_add]; ring

private theorem gg_sum {α β : Type*} {t : α→ℝ} (s : Finset β) (f : β→α→ℂ)
    (hf : ∀ j∈s, G t (f j)) : G t (fun x => ∑ j∈s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using gg_const (t:=t) 0
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact gg_add (hf j (by simp)) (ih (fun a ha => hf a (Finset.mem_insert_of_mem ha)))

private theorem rec_growth {ι : Type*} (E : ι→ℝ→ℂ) (hE : ∀ i, ContDiff ℝ ∞ (E i)) (hn : ∀ i x, E i x≠0)
    (he : ∀ j : ℕ, ∃ C : ℝ, ∀ i x, ‖iteratedDeriv j (E i) x‖≤C)
    (hi : G Prod.snd (fun p : ι×ℝ => (E p.1 p.2)⁻¹)) (j : ℕ) :
    G Prod.snd (fun p : ι×ℝ => iteratedDeriv j (fun x => (E p.1 x)⁻¹) p.2) := by
  let g (i : ι) (x : ℝ) := (E i x)⁻¹
  have hg (i : ι) : ContDiff ℝ ∞ (g i) := (hE i).inv (hn i)
  change G Prod.snd (fun p : ι×ℝ => iteratedDeriv j (g p.1) p.2)
  induction j using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|n
    · simpa [g] using hi
    · let d := n+1
      let T (j : ℕ) (p : ι×ℝ) := (d.choose j:ℂ)*iteratedDeriv j (g p.1) p.2*iteratedDeriv (d-j) (E p.1) p.2
      have hf : G Prod.snd (fun p : ι×ℝ => ∑ j∈Finset.range d, T j p) := by
        apply gg_sum
        intro j hj
        obtain ⟨c,hc⟩ := he (d-j)
        exact gg_mul (gg_mul (gg_const _) (ih j (Finset.mem_range.mp hj))) (gg_bdd (fun p => hc p.1 p.2))
      have hfun : (fun p : ι×ℝ => iteratedDeriv d (g p.1) p.2)=
          fun p : ι×ℝ => ((-1:ℂ)*(∑ j∈Finset.range d, T j p))*g p.1 p.2 := by
        funext p
        let i := p.1; let x := p.2
        have hone : g i*E i=fun _ => (1:ℂ) := funext (fun x => inv_mul_cancel₀ (hn i x))
        have hprod := iteratedDeriv_mul (n:=d) (f:=g i) (g:=E i) ((hg i).contDiffAt.of_le (mod_cast le_top))
          ((hE i).contDiffAt.of_le (mod_cast le_top)) (x:=x)
        rw [hone] at hprod
        change iteratedDeriv d (fun _ : ℝ => (1:ℂ)) x = ∑ j∈Finset.range (d+1), T j p at hprod
        simp only [d,iteratedDeriv_const, Nat.succ_ne_zero, ↓reduceIte] at hprod
        change 0 = ∑ j∈Finset.range (d+1), T j p at hprod
        rw [Finset.sum_range_succ] at hprod
        have heq : T d p = iteratedDeriv d (g i) x * E i x := by simp [T,i,x]
        rw [heq] at hprod
        change _ = _ * (E i x)⁻¹
        rw [←div_eq_mul_inv,eq_div_iff (hn i x)]
        linear_combination -hprod
      change G Prod.snd (fun p : ι×ℝ => iteratedDeriv d (g p.1) p.2)
      rw [hfun]
      exact gg_mul (gg_mul (gg_const _) hf) hi

theorem quotient_decay {ι : Type*} (E D : ι→ℝ→ℂ) (hE : ∀ i, ContDiff ℝ ∞ (E i)) (hD : ∀ i, ContDiff ℝ ∞ (D i))
    (hn : ∀ i x, E i x≠0) (he : ∀ j : ℕ, ∃ C : ℝ, ∀ i x, ‖iteratedDeriv j (E i) x‖≤C)
    (A : ℝ) (hA : 0≤A) (hi : ∀ i x, ‖(E i x)⁻¹‖ ≤ Real.exp (A*(1+|x|)^2))
    (hd : ∀ j k : ℕ, ∀ C : ℝ, 0≤C → ∃ B : ℝ, 0≤B ∧ ∀ i x,
      |x|^k*‖iteratedDeriv j (D i) x‖*Real.exp (C*(1+|x|)^2)≤B) (k n : ℕ) :
    ∃ M : ℝ, 0≤M ∧ ∀ i x, |x|^k*‖iteratedDeriv n (fun y => D i y/E i y) x‖≤M := by
  classical
  let g (i : ι) (x : ℝ) := (E i x)⁻¹
  have hg (i : ι) : ContDiff ℝ ∞ (g i) := (hE i).inv (hn i)
  have hgi : G Prod.snd (fun p : ι×ℝ => (E p.1 p.2)⁻¹) := ⟨A,1,hA,by norm_num,fun p => by simpa [Q] using hi p.1 p.2⟩
  let T (j : ℕ) (i : ι) (x : ℝ) := (n.choose j:ℂ)*iteratedDeriv j (D i) x*iteratedDeriv (n-j) (g i) x
  have hT (j : ℕ) : ∃ K : ℝ, 0≤K ∧ ∀ i x, |x|^k*‖T j i x‖≤K := by
    obtain ⟨a,b,ha,hb,h⟩ := rec_growth E hE hn he hgi (n-j)
    obtain ⟨C,hC,hD'⟩ := hd j k a ha
    refine ⟨(n.choose j:ℝ)*b*C,by positivity,fun i x => ?_⟩
    dsimp only [T]
    simp only [norm_mul,Complex.norm_natCast]
    calc
      _ ≤ |x|^k*((n.choose j:ℝ)*‖iteratedDeriv j (D i) x‖*(b*Real.exp (a*Q x))) := by gcongr; exact h (i,x)
      _ = ((n.choose j:ℝ)*b)*(|x|^k*‖iteratedDeriv j (D i) x‖*Real.exp (a*Q x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hD' i x) (by positivity)
  choose K hK hk using hT
  refine ⟨∑j∈Finset.range (n+1),K j,Finset.sum_nonneg (fun j _ => hK j),fun i x => ?_⟩
  rw [show (fun y => D i y/E i y) = D i * g i by funext y; exact div_eq_mul_inv ..]
  rw [iteratedDeriv_mul (n:=n) (f:=D i) (g:=g i)
    ((hD i).contDiffAt.of_le (mod_cast le_top)) ((hg i).contDiffAt.of_le (mod_cast le_top))]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (abs_nonneg _) _)).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => hk j i x)

end
end MasulloRH.SynthUniformWall
end StandaloneSynthL2UniformDivision


-- Local source: SynthL2WallBounds
section StandaloneSynthL2WallBounds
open Set MeasureTheory Filter
open scoped SchwartzMap Topology ContDiff
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall (vertical)

abbrev SelectedWall (b d : ℝ) := {u : ℝ // |u|≤b ∧ ∀ t, Avoids d 2 (vertical u t)}

private theorem factorial_exp (x : ℝ) (hx : 0≤x) (k : ℕ) : x^k≤(k.factorial:ℝ)*Real.exp x := by
  simpa [mul_comm] using (div_le_iff₀ (Nat.cast_pos.mpr k.factorial_pos : 0<(k.factorial:ℝ))).mp (Real.pow_div_factorial_le_exp x hx k)

private theorem polynomial_uniform (P : Polynomial ℂ) (b : ℝ) :
    ∃ M : ℝ, 0≤M ∧ ∀ σ : ℝ, |σ|≤b → ∀ t : ℝ, ‖P.eval (vertical σ t)‖≤M*Real.exp |t| := by
  let A (j : ℕ) := ‖P.coeff j‖*(j.factorial:ℝ)*Real.exp b
  refine ⟨∑j∈Finset.range (P.natDegree+1),A j,Finset.sum_nonneg (fun j _ => by dsimp [A]; positivity),fun σ hσ t => ?_⟩
  rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  apply (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  have hn : ‖vertical σ t‖≤b+|t| := by
    exact (by simpa using Complex.norm_le_abs_re_add_abs_im (vertical σ t) : ‖vertical σ t‖≤|σ|+|t|) |>.trans (by linarith)
  have hp := (factorial_exp _ (norm_nonneg _) j).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hn) (Nat.cast_nonneg _))
  rw [norm_mul,norm_pow]
  apply (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq
  rw [Real.exp_add]; dsimp [A]; ring

private theorem damp_band_rapid (ε b : ℝ) (hε : 0<ε) (j k : ℕ) (A : ℝ) (hA : 0≤A) :
    ∃ B : ℝ, 0≤B ∧ ∀ σ : ℝ, |σ|≤b → ∀ t : ℝ, |t|^k*‖iteratedDeriv j (fun t : ℝ => damp ε (vertical σ t)) t‖*
      Real.exp (A*(1+|t|)^2) ≤ B := by
  obtain ⟨P,hP⟩ := damp_deriv_polynomial ε j
  obtain ⟨M,hM,hp⟩ := polynomial_uniform P b
  obtain ⟨C,hC,hc⟩ := damp_dominates ε b A hε hA
  refine ⟨(k.factorial:ℝ)*M*C,by positivity,fun σ hσ t => ?_⟩
  have h := hc (vertical σ t) (by simpa using hσ)
  rw [SynthWall.vertical_im] at h
  rw [vertical_derivatives _ (damp_entire ε),hP,norm_mul,norm_pow,Complex.norm_I,one_pow,one_mul,norm_mul]
  calc
    _ = (|t|^k*‖P.eval (vertical σ t)‖)*(‖damp ε (vertical σ t)‖*Real.exp (A*(1+|t|)^2)) := by ring
    _ ≤ ((k.factorial:ℝ)*Real.exp |t| *(M*Real.exp |t|))*(C*Real.exp (-2*|t|)) :=
      mul_le_mul (mul_le_mul (factorial_exp _ (abs_nonneg _) _) (hp σ hσ t) (norm_nonneg _) (by positivity)) h
        (by positivity) (by positivity)
    _ = _ := by
      rw [show -2*|t|= -(|t|+|t|) by ring,Real.exp_neg,Real.exp_add]; field_simp

private theorem center_arg (σ t : ℝ) : vertical σ t+1/2=vertical (σ+1/2) t := by
  unfold vertical; push_cast; ring

theorem wall_quotient_decay (b ε d : ℝ) (hb : b<1/2) (hε : 0<ε) (hd : 0<d) (k j : ℕ) :
    ∃ M : ℝ, 0≤M ∧ ∀ u : SelectedWall b d, ∀ t : ℝ, |t|^k *
      ‖iteratedDeriv j (fun y : ℝ => damp ε (vertical u.val y)/centeredE (vertical u.val y)) t‖ ≤ M := by
  let G (u : SelectedWall b d) (y : ℝ) := E (vertical (u.val+1/2) y)
  let D (u : SelectedWall b d) (y : ℝ) := damp ε (vertical u.val y)
  have hcmp (u : SelectedWall b d) (t : ℝ) : centeredE (vertical u.val t)=G u t := by rw [centeredE,center_arg]
  have hsmooth (f : ℂ→ℂ) (hf : Differentiable ℂ f) (a : ℝ) : ContDiff ℝ ∞ (fun t : ℝ => f (vertical a t)) :=
    ((hf.contDiff : ContDiff ℂ ∞ f).restrict_scalars ℝ).comp
      (show ContDiff ℝ ∞ (vertical a) from contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const))
  obtain ⟨C,hC,h⟩ := E_minimum (1/2-b) (1/2+b) (by linarith) (by linarith) d hd 2
  have hi (u : SelectedWall b d) (t : ℝ) : G u t≠0 ∧ ‖(G u t)⁻¹‖≤Real.exp (C*(1+|t|)^2) := by
    obtain ⟨hl,hr⟩ := abs_le.mp u.prop.1
    have hsep := u.prop.2 t
    have hmain := h (vertical (u.val+1/2) t) (by simp; linarith) (by simp; linarith) (by
      simpa only [Avoids,center_arg,SynthWall.vertical_im] using hsep)
    change G u t≠0 ∧ max 0 (-Real.log ‖G u t‖)≤C*(1+|(vertical (u.val+1/2) t).im|)^2 at hmain
    rw [SynthWall.vertical_im] at hmain
    refine ⟨hmain.1,?_⟩
    have hi' := Real.exp_le_exp.mpr ((le_max_right _ _).trans hmain.2)
    rwa [Real.exp_neg,Real.exp_log (norm_pos_iff.mpr hmain.1),←norm_inv] at hi'
  have he (j : ℕ) : ∃ K : ℝ, ∀ u : SelectedWall b d, ∀ t : ℝ, ‖iteratedDeriv j (G u) t‖≤K := by
    obtain ⟨K,_,hk⟩ := E_deriv_band_bound 1 j
    refine ⟨K,fun u t => ?_⟩
    dsimp only [G]
    rw [vertical_derivatives E E_entire,norm_mul,norm_pow,Complex.norm_I,one_pow,one_mul]
    apply hk
    rw [SynthWall.vertical_re]
    exact abs_le.mpr ⟨by linarith [(abs_le.mp u.prop.1).1],by linarith [(abs_le.mp u.prop.1).2]⟩
  have hdf (j k : ℕ) (A : ℝ) (hA : 0≤A) := damp_band_rapid ε b hε j k A hA
  have hD (j k : ℕ) (A : ℝ) (hA : 0≤A) :
      ∃ B : ℝ, 0≤B ∧ ∀ (i : SelectedWall b d) (x : ℝ), |x|^k*‖iteratedDeriv j (D i) x‖*Real.exp (A*(1+|x|)^2)≤B := by
    obtain ⟨B,hB,hB'⟩ := hdf j k A hA
    exact ⟨B,hB,fun u x => hB' _ u.prop.1 x⟩
  obtain ⟨M,hM,hbd⟩ := SynthUniformWall.quotient_decay G D (fun u => hsmooth _ E_entire (u.val+1/2))
    (fun u => hsmooth _ (damp_entire ε) u.val) (fun u x => (hi u x).1) he C hC.le (fun u x => (hi u x).2) hD k j
  refine ⟨M,hM,fun u t => ?_⟩
  simpa only [hcmp] using (hbd u t)

end
end MasulloRH.SynthesisStrip
end StandaloneSynthL2WallBounds


-- Local source: SynthL2WallKernels
section StandaloneSynthL2WallKernels
open Set MeasureTheory Filter Bornology FourierTransform
open scoped SchwartzMap Topology ContDiff FourierTransform
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall (vertical freq freq_ne_zero)

private theorem pow_integral_uniform {ι : Type*} (W : ι→𝓢(ℝ,ℂ)) (hb : IsVonNBounded ℂ (range W)) (k : ℕ) :
    ∃ B : ℝ, 0≤B ∧ ∀ i, (∫x : ℝ, |x|^k*‖W i x‖)≤B := by
  let μ : Measure ℝ := volume
  let A : ℝ := 2^μ.integrablePower * ∫ x : ℝ, (1+‖x‖)^(-(μ.integrablePower:ℝ))
  have hA : 0≤A := by dsimp [A]; positivity
  have h := (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hb
  obtain ⟨B,hB,hb₀⟩ := h (0,0)
  obtain ⟨C,hC,hb₁⟩ := h (k+μ.integrablePower,0)
  refine ⟨A*(B+C),by positivity,fun i => ?_⟩
  have hi := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ μ (W i) k 0
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at hi
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ hA
  exact add_le_add (hb₀ _ ⟨i,rfl⟩).le (hb₁ _ ⟨i,rfl⟩).le

private theorem weighted_integral_uniform {ι : Type*} (W : ι→𝓢(ℝ,ℂ)) (hb : IsVonNBounded ℂ (range W)) :
    ∃ B : ℝ, 0≤B ∧ ∀ i, ∀ p : ℝ, p≤1 →
      Integrable (fun x : ℝ => (1+|x|)^p*‖W i x‖) ∧ (∫x : ℝ, (1+|x|)^p*‖W i x‖)≤B := by
  obtain ⟨B,hB,h₀⟩ := pow_integral_uniform W hb 0
  obtain ⟨C,hC,h₁⟩ := pow_integral_uniform W hb 1
  refine ⟨B+C,by positivity,fun i p hp => ?_⟩
  have hI : Integrable (fun x : ℝ => |x| *‖W i x‖) := by
    simpa only [Real.norm_eq_abs,pow_one] using (W i).integrable_pow_mul volume 1
  have hJ := (W i).integrable.norm.add hI
  have hmono (x : ℝ) : (1+|x|)^p*‖W i x‖ ≤ ‖W i x‖+|x| *‖W i x‖ := by
    apply (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg x] : 1≤1+|x|) hp) (norm_nonneg _)).trans_eq
    rw [Real.rpow_one]; ring
  have hK := hJ.mono' (show Continuous (fun x : ℝ => (1+|x|)^p*‖W i x‖) from
    (Continuous.rpow_const (by fun_prop) (fun _ => Or.inl (by positivity))).mul (W i).continuous.norm).aestronglyMeasurable
    (.of_forall fun x => by rw [Real.norm_of_nonneg (by positivity)]; exact hmono x)
  refine ⟨hK,(integral_mono hK hJ hmono).trans ?_⟩
  change (∫ x : ℝ, ‖W i x‖+|x| * ‖W i x‖)≤B+C
  rw [integral_add (W i).integrable.norm hI]
  simpa using add_le_add (h₀ i) (h₁ i)

theorem wall_multipliers_bounded (b ε d : ℝ) (hb : b<1/2) (hε : 0<ε) (hd : 0<d) :
    ∃ W : SelectedWall b d→𝓢(ℝ,ℂ),
      (∀ u ξ, W u ξ=damp ε (vertical u.val (freq*ξ))/centeredE (vertical u.val (freq*ξ))) ∧
      IsVonNBounded ℂ (range W) := by
  classical
  let scale : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 freq freq_ne_zero)
  let L : 𝓢(ℝ,ℂ)→L[ℂ]𝓢(ℝ,ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scale
  have hex (u : SelectedWall b d) : ∃ V : 𝓢(ℝ,ℂ), ∀ x, V x = damp ε (vertical u.val x)/centeredE (vertical u.val x) := by
    obtain ⟨W,hW⟩ := quotient_wall_multiplier u.val ε (u.prop.1.trans_lt hb) hε d hd 2 u.prop.2
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scale.symm W,fun x => ?_⟩
    change W (scale.symm x)=_
    rw [hW,show freq*scale.symm x=x by exact scale.apply_symm_apply x]
  choose V hV using hex
  have hVb : IsVonNBounded ℂ (range V) := by
    apply (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mpr
    rintro ⟨k,j⟩
    obtain ⟨M,hM,hbd⟩ := wall_quotient_decay b ε d hb hε hd k j
    refine ⟨M+1,by positivity,?_⟩
    rintro _ ⟨u,rfl⟩
    apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound' ℂ k j (V u) hM ?_) (by linarith)
    simpa only [show (V u : ℝ→ℂ) = (fun x => damp ε (vertical u.val x)/centeredE (vertical u.val x)) from funext (hV u)] using (hbd u)
  let W (u : SelectedWall b d) := L (V u)
  refine ⟨W,(fun u ξ => hV u (freq*ξ)),(hVb.image L).subset ?_⟩
  rintro _ ⟨u,rfl⟩
  exact ⟨V u,⟨u,rfl⟩,rfl⟩

theorem uniform_inverse_wall_kernels (b ε d : ℝ) (hb : b<1/2) (hε : 0<ε) (hd : 0<d) :
    ∃ W : SelectedWall b d→𝓢(ℝ,ℂ),
      (∀ u ξ, W u ξ=damp ε (vertical u.val (freq*ξ))/centeredE (vertical u.val (freq*ξ))) ∧
      ∃ M : ℝ, 0≤M ∧ ∀ u, ∀ p : ℝ, p≤1 →
        Integrable (fun x : ℝ => (1+|x|)^p*‖(𝓕⁻ (W u)) x‖) ∧
        (∫ x : ℝ, (1+|x|)^p*‖(𝓕⁻ (W u)) x‖)≤M := by
  obtain ⟨W,hW,hb'⟩ := wall_multipliers_bounded b ε d hb hε hd
  refine ⟨W,hW,?_⟩
  let J : 𝓢(ℝ,ℂ)→L[ℂ]𝓢(ℝ,ℂ) := fourierInvCLM ℂ 𝓢(ℝ,ℂ)
  have hJ : IsVonNBounded ℂ (range (fun u => 𝓕⁻ (W u))) := by
    apply (hb'.image J).subset
    rintro _ ⟨u,rfl⟩
    exact ⟨W u,⟨u,rfl⟩,rfl⟩
  exact weighted_integral_uniform _ hJ

end
end MasulloRH.SynthesisStrip
end StandaloneSynthL2WallKernels


-- Local source: SynthWallShiftEnergy
section StandaloneSynthWallShiftEnergy
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace MasulloRH.SynthWall
noncomputable section

def mass (w : ℝ→ℝ) (f : ℝ→ℂ) := ∫x,(w x*‖f x‖)^2

end
end MasulloRH.SynthWall
end StandaloneSynthWallShiftEnergy


-- Local source: SynthWallApproximateIdentity
section StandaloneSynthWallApproximateIdentity
open Set MeasureTheory Filter
open scoped Topology
namespace MasulloRH.SynthWall
noncomputable section

def dilate (k : ℝ→ℂ) (ε t : ℝ) : ℂ := ((ε⁻¹:ℝ):ℂ)*k (ε⁻¹*t)

end
end MasulloRH.SynthWall
end StandaloneSynthWallApproximateIdentity


-- Local source: SynthDampingKernel
section StandaloneSynthDampingKernel
open Set MeasureTheory Filter FourierTransform
open scoped Topology FourierTransform SchwartzMap ContDiff
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall

private def dampingLine (ε σ : ℝ) (hε : 0<ε) : 𝓢(ℝ,ℂ) where
  toFun t := damp ε (vertical σ t)
  smooth' := (((damp_entire ε).contDiff : ContDiff ℂ ∞ (damp ε)).restrict_scalars ℝ).comp
    (show ContDiff ℝ ∞ (vertical σ) from contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const))
  decay' k j := by
    obtain ⟨B,_,h⟩ := vertical_damp_rapid ε σ hε j k 0 le_rfl
    refine ⟨B,fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs]
    simpa using h x

def dampingProfile (ε σ : ℝ) (hε : 0<ε) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 freq freq_ne_zero)) (dampingLine ε σ hε)

@[simp] theorem dampingProfile_apply (ε σ : ℝ) (hε : 0<ε) (ξ : ℝ) :
    dampingProfile ε σ hε ξ=profile (damp ε) σ ξ := rfl

theorem damping_heights {ε : ℝ} (hε : 0<ε) (b : ℝ) : GoodHeights (damp ε) b := by
  obtain ⟨C,hC,h⟩ := damp_dominates ε b 0 hε le_rfl
  refine ⟨Nat.cast,fun n : ℕ=>C*(Real.exp (-2))^n,tendsto_natCast_atTop_atTop,?_,fun n u hu=>?_⟩
  · simpa using ((summable_geometric_of_lt_one (Real.exp_nonneg _) (Real.exp_lt_one_iff.mpr (by norm_num : (-2:ℝ)<0))).mul_left C).tendsto_atTop_zero
  · have h₁ := h (vertical u n) (by simpa)
    have h₂ := h (vertical u (-n)) (by simpa)
    dsimp only
    rw [←Real.exp_nat_mul]
    simpa [mul_comm (n:ℝ) (-2)] using And.intro h₁ h₂

theorem damping_line_integrable {ε : ℝ} (hε : 0<ε) (σ : ℝ) :
    Integrable (fun t=>damp ε (vertical σ t)) := (dampingLine ε σ hε).integrable

def dampingKernel : 𝓢(ℝ,ℂ) := 𝓕⁻ (dampingProfile 1 0 one_pos)

theorem dampingKernel_untwist (σ x : ℝ) :
    (Real.exp (-σ*x):ℂ)*(𝓕⁻ (profile (damp 1) σ)) x=dampingKernel x := by
  have hh := damping_heights (ε:=1) one_pos |σ|
  have hc : ContinuousOn (damp 1) (closedStrip |σ|) := (damp_entire 1).continuous.continuousOn
  have hd : DifferentiableOn ℂ (damp 1) (openStrip |σ|) := (damp_entire 1).differentiableOn
  have h0 : |(0:ℝ)| ≤ |σ| := by simp
  have he : (Real.exp (-σ*x):ℂ)*(𝓕⁻ (profile (damp 1) σ)) x=
      (Real.exp (-(0:ℝ)*x):ℂ)*(𝓕⁻ (profile (damp 1) 0)) x := by
    rcases le_total σ 0 with hs|hs
    · exact fourierInv_profile_shift _ hs le_rfl h0 hc hd hh (damping_line_integrable one_pos _) (damping_line_integrable one_pos _) x
    · exact (fourierInv_profile_shift _ hs h0 le_rfl hc hd hh (damping_line_integrable one_pos _) (damping_line_integrable one_pos _) x).symm
  unfold dampingKernel
  rw [SchwartzMap.fourierInv_coe,show (dampingProfile 1 0 one_pos : ℝ→ℂ)=profile (damp 1) 0 from funext (dampingProfile_apply 1 0 one_pos)]
  simpa only [neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,one_mul] using he

theorem dampingKernel_tilt (σ : ℝ) :
    tilt σ dampingKernel=(𝓕⁻ (dampingProfile 1 σ one_pos) : 𝓢(ℝ,ℂ)) := by
  rw [SchwartzMap.fourierInv_coe]
  funext x
  change (Real.exp (σ*x):ℂ)*dampingKernel x=(𝓕⁻ (profile (damp 1) σ)) x
  rw [←dampingKernel_untwist σ x]
  simp only [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,neg_mul,add_neg_cancel,Real.exp_zero,Complex.ofReal_one,one_mul]

theorem dampingKernel_fourier (σ : ℝ) : 𝓕 (tilt σ dampingKernel)=profile (damp 1) σ := by
  rw [dampingKernel_tilt,←SchwartzMap.fourier_coe,fourier_fourierInv_eq]
  rfl

theorem integral_dilate {ε : ℝ} (hε : 0<ε) (f : ℝ→ℂ) : (∫t,dilate f ε t)=∫t,f t := by
  unfold dilate
  rw [integral_const_mul,Measure.integral_comp_inv_mul_left f ε,Complex.real_smul,abs_of_pos hε,
    ←mul_assoc,←Complex.ofReal_mul,inv_mul_cancel₀ hε.ne',Complex.ofReal_one,one_mul]

theorem fourier_dilate {ε : ℝ} (hε : 0<ε) (f : ℝ→ℂ) (ξ : ℝ) :
    𝓕 (dilate f ε) ξ=𝓕 f (ε*ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
  let g (t : ℝ) := Complex.exp (↑(-2*Real.pi*t*(ε*ξ))*Complex.I)*f t
  change _=∫t,g t
  rw [←integral_dilate hε g]
  apply integral_congr_ae
  filter_upwards with t
  have h : (-2*Real.pi*(ε⁻¹*t)*(ε*ξ))=(-2*Real.pi*t*ξ) := by field_simp
  change Complex.exp (↑(-2*Real.pi*t*ξ)*Complex.I)*(((ε⁻¹:ℝ):ℂ)*f (ε⁻¹*t))=_
  dsimp only [dilate,g]
  rw [h]
  ring

theorem tilt_dilate {ε : ℝ} (hε : 0<ε) (σ : ℝ) (f : ℝ→ℂ) :
    tilt σ (dilate f ε)=dilate (tilt (ε*σ) f) ε := by
  funext x
  have he : ε*σ*(ε⁻¹*x)=σ*x := by field_simp
  simp only [tilt,dilate,he,mul_left_comm]

theorem dampingKernel_scaled_fourier {ε : ℝ} (hε : 0<ε) (σ : ℝ) :
    𝓕 (tilt σ (dilate dampingKernel ε))=profile (damp ε) σ := by
  funext ξ
  rw [tilt_dilate hε,fourier_dilate hε,dampingKernel_fourier,profile,profile,damp_scale ε]
  congr 1
  unfold vertical
  push_cast
  ring

theorem dampingKernel_scaled_integrable {ε : ℝ} (hε : 0<ε) (σ : ℝ) :
    Integrable (tilt σ (dilate dampingKernel ε)) := by
  rw [tilt_dilate hε,dampingKernel_tilt]
  apply Integrable.const_mul
  exact (𝓕⁻ (dampingProfile 1 (ε*σ) one_pos) : 𝓢(ℝ,ℂ)).integrable.comp_mul_left' (inv_ne_zero hε.ne')

end
end MasulloRH.SynthesisStrip
end StandaloneSynthDampingKernel


-- Local source: SynthWallIdentification
section StandaloneSynthWallIdentification
open MeasureTheory Filter Set FourierTransform
open scoped Topology FourierTransform Convolution
namespace MasulloRH.SynthWall
noncomputable section

theorem tilt_conv (σ : ℝ) (f g : ℝ→ℂ) :
    tilt σ (conv f g)=conv (tilt σ f) (tilt σ g) := by
  funext x
  change (Real.exp (σ*x):ℂ)*(∫t:ℝ,f t*g (x-t))=
    ∫t:ℝ,((Real.exp (σ*t):ℂ)*f t)*((Real.exp (σ*(x-t)):ℂ)*g (x-t))
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [show σ*x=σ*t+σ*(x-t) by ring,Real.exp_add,Complex.ofReal_mul]
  ring

theorem fourier_tilt_conv {σ : ℝ} {f g : ℝ→ℂ} (hf : Integrable (tilt σ f)) (hg : Integrable (tilt σ g))
    (ξ : ℝ) : 𝓕 (tilt σ (conv f g)) ξ=𝓕 (tilt σ f) ξ * 𝓕 (tilt σ g) ξ := by
  rw [tilt_conv]
  exact Real.fourier_mul_convolution_eq hf hg ξ

/-- Equality of integrable Fourier products on one exponential wall identifies both physical convolutions. -/
theorem conv_eq_of_wall_products {σ : ℝ} {k h f g : ℝ→ℂ}
    (hk : Integrable (tilt σ k)) (hf : Integrable (tilt σ f))
    (hh : Integrable (tilt σ h)) (hg : Integrable (tilt σ g))
    (h₁ : Continuous (conv k f)) (h₂ : Continuous (conv h g))
    (hI : Integrable (fun ξ : ℝ=>𝓕 (tilt σ k) ξ * 𝓕 (tilt σ f) ξ))
    (hprod : ∀ ξ,𝓕 (tilt σ k) ξ * 𝓕 (tilt σ f) ξ = 𝓕 (tilt σ h) ξ * 𝓕 (tilt σ g) ξ) :
    conv k f=conv h g := by
  have he : 𝓕 (tilt σ (conv k f))=𝓕 (tilt σ (conv h g)) :=
    funext (fun ξ => (fourier_tilt_conv hk hf ξ).trans ((hprod ξ).trans (fourier_tilt_conv hh hg ξ).symm))
  have h₀ : Integrable (𝓕 (tilt σ (conv k f))) := by
    simpa only [show 𝓕 (tilt σ (conv k f)) = _ from funext (fourier_tilt_conv hk hf)] using hI
  have wt : Continuous (fun x : ℝ => (Real.exp (σ*x):ℂ)) := by fun_prop
  have hcc₁ : Continuous (tilt σ (conv k f)) := wt.mul h₁
  have hcc₂ : Continuous (tilt σ (conv h g)) := wt.mul h₂
  have hJ₁ : Integrable (tilt σ (conv k f)) := by
    rw [tilt_conv]; exact hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  have hJ₂ : Integrable (tilt σ (conv h g)) := by
    rw [tilt_conv]; exact hh.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg
  have hEq := congrArg (fun f : ℝ→ℂ => 𝓕⁻ f) he
  rw [hcc₁.fourierInv_fourier_eq hJ₁ h₀,hcc₂.fourierInv_fourier_eq hJ₂ (he ▸ h₀)] at hEq
  funext x
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos (σ*x)).ne') (congrFun hEq x)

end
end MasulloRH.SynthWall
end StandaloneSynthWallIdentification


-- Local source: SynthPrimal
section StandaloneSynthPrimal
open MeasureTheory Filter Set FourierTransform
open scoped Topology InnerProductSpace FourierTransform
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall
open StripTrace (lap)

theorem lap_bound {b : ℝ} (f : ℝ→ℂ) {s : ℂ} (hs : |s.re|≤b) (x : ℝ) :
    ‖Complex.exp (s*x)*f x‖≤‖f x‖*Real.exp (b*|x|) := by
  simp only [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (norm_nonneg _)
  exact (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right hs (abs_nonneg _)))

theorem lap_regular {b : ℝ} {f : ℝ→ℂ} (hm : AEStronglyMeasurable f)
    (hf : Integrable (fun x=>‖f x‖*Real.exp (b*|x|))) :
    ContinuousOn (lap f) (closedStrip b) ∧ AnalyticOnNhd ℂ (lap f) (openStrip b) ∧
    ∀ s∈closedStrip b, ‖lap f s‖ ≤ ∫ x : ℝ, ‖f x‖*Real.exp (b*|x|) := by
  have hc : ContinuousOn (lap f) (closedStrip b) := by
    apply continuousOn_of_dominated (bound:=fun x=>‖f x‖*Real.exp (b*|x|))
    · exact fun s _ => (show Continuous (fun x : ℝ => Complex.exp (s*x)) by fun_prop).aestronglyMeasurable.mul hm
    · exact fun s hs => .of_forall (lap_bound f hs)
    · exact hf
    · exact .of_forall (fun x => (show Continuous (fun s : ℂ => Complex.exp (s*x)*f x) by fun_prop).continuousOn)
  refine ⟨hc,?_,fun s hs => norm_integral_le_of_norm_le hf (.of_forall (lap_bound f hs))⟩
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const)
  intro s hs
  have h := StripTrace.moment_hasDerivAt hm hf 0 hs
  have he : (fun z => StripPhysical.moment f z 0)=lap f := by
    funext z
    simp only [StripPhysical.moment,lap,pow_zero,mul_one]
    exact integral_congr_ae (.of_forall (fun x => mul_comm _ _))
  exact (he ▸ h).differentiableAt.differentiableWithinAt

theorem exp_tilt_le {b σ : ℝ} (hσ : |σ|≤b) (f : ℝ→ℂ) (x : ℝ) :
    ‖tilt σ f x‖ ≤ Real.exp (b*|x|)*‖f x‖ := by
  rw [tilt_norm]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ((le_abs_self _).trans ((abs_mul _ _).le.trans
    (mul_le_mul_of_nonneg_right hσ (abs_nonneg x))))) (norm_nonneg _)

theorem tilt_int {b σ : ℝ} (hσ : |σ|≤b) {f : ℝ→ℂ} (hm : AEStronglyMeasurable f)
    (hf : Integrable (fun x=>‖f x‖*Real.exp (b*|x|))) : Integrable (tilt σ f) := by
  apply hf.mono' ((show Continuous (fun x : ℝ => (Real.exp (σ*x):ℂ)) by fun_prop).aestronglyMeasurable.mul hm)
  exact .of_forall fun x => (exp_tilt_le hσ f x).trans_eq (mul_comm _ _)

theorem profile_lap (f : ℝ→ℂ) (σ ξ : ℝ) : profile (lap f) σ ξ=𝓕 (tilt σ f) ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [profile,lap,tilt,vertical,freq,smul_eq_mul,Complex.ofReal_exp,←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring

end
end MasulloRH.SynthesisStrip
end StandaloneSynthPrimal


-- Local source: SynthDampingHilbert
section StandaloneSynthDampingHilbert
open Set MeasureTheory Filter FourierTransform
open scoped Topology FourierTransform SchwartzMap
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall

theorem damping_convolution_identify {ε σ : ℝ} (hε : 0<ε) {f q : ℝ→ℂ}
    (hf : Integrable f) (hfσ : Integrable (tilt σ f))
    (hq : Integrable q) (hqσ : Integrable (tilt σ q))
    (hprod : ∀ ξ,profile (damp ε) σ ξ * 𝓕 (tilt σ f) ξ =
      𝓕 (tilt σ seed) ξ * 𝓕 (tilt σ q) ξ) :
    conv (dilate dampingKernel ε) f=conv seed q := by
  have hdC : Continuous (dilate dampingKernel ε) :=
    continuous_const.mul (dampingKernel.continuous.comp (continuous_const.mul continuous_id))
  have hdB : BddAbove (Set.range fun x=>‖dilate dampingKernel ε x‖) := by
    refine ⟨‖((ε⁻¹:ℝ):ℂ)‖ * SchwartzMap.seminorm ℝ 0 0 dampingKernel,?_⟩
    rintro _ ⟨x,rfl⟩
    exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ _ _)
      (norm_nonneg _))
  obtain ⟨C,_,hC⟩ := seed_decay 0
  have hsB : BddAbove (Set.range fun x=>‖seed x‖) := ⟨C,by
    rintro _ ⟨x,rfl⟩
    simpa using hC x⟩
  have hseed := tilt_int (show |σ|≤|σ| from le_rfl) seed_cont.aestronglyMeasurable
    (seed_weighted |σ|)
  have hd := dampingKernel_scaled_fourier hε σ
  have hP : (dampingProfile ε σ hε:ℝ→ℂ)=profile (damp ε) σ := funext (dampingProfile_apply ε σ hε)
  refine conv_eq_of_wall_products (dampingKernel_scaled_integrable hε σ) hfσ hseed hqσ
    (hdB.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul ℂ ℂ) hdC hf)
    (hsB.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul ℂ ℂ) seed_cont hq) ?_ ?_
  · rw [hd,←hP]
    have hc : Continuous (𝓕 (tilt σ f)) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hfσ
    apply ((dampingProfile ε σ hε).integrable.norm.mul_const (∫ x,‖tilt σ f x‖)).mono'
      ((dampingProfile ε σ hε).continuous.mul hc).aestronglyMeasurable
    filter_upwards with ξ
    rw [Pi.mul_apply,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [Real.fourier_eq]
    exact (norm_integral_le_integral_norm _).trans_eq (by simp only [Circle.norm_smul])
  · simpa only [hd] using hprod

end
end MasulloRH.SynthesisStrip
end StandaloneSynthDampingHilbert


-- Local source: SynthQuotientReconstruct
section StandaloneSynthQuotientReconstruct
open Set Filter MeasureTheory FourierTransform
open scoped Topology SchwartzMap FourierTransform ContDiff
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall

/-- On either separated wall, the actual analytic seed transform is nonzero. -/
theorem wall_nonzero_of_separation (b : ℝ) (hb : b<1/2) (d : ℝ) (hd : 0<d)
    (hsep : ∀ t, Avoids d 2 (vertical b t) ∧ Avoids d 2 (vertical (-b) t))
    (s : ℂ) (hs : |s.re|=b) : E (s+1/2)≠0 := by
  have hb0 : 0≤b := hs ▸ abs_nonneg _
  have hzre := abs_le.mp hs.le
  have hr : (s+1/2).re=s.re+1/2 := by simp
  have h0 : 0<(s+1/2).re := by rw [hr]; linarith
  have h1 : (s+1/2).re<1 := by rw [hr]; linarith
  have heq : vertical s.re s.im=s := Complex.ext (by simp) (by simp)
  have hsep' : Avoids d 2 s := by
    rw [←heq]
    rcases (abs_eq hb0).mp hs with ho | ho
    · rw [ho]; exact (hsep _).1
    · rw [ho]; exact (hsep _).2
  intro h
  have bad := hsep' (s+1/2) ((E_strip _ h0 h1).2.1.mp h) h0 h1 (by simp)
  rw [sub_self,norm_zero] at bad
  exact (not_lt_of_ge bad) (by positivity)

end
end MasulloRH.SynthesisStrip
end StandaloneSynthQuotientReconstruct


-- Local source: SynthPowerWeight
section StandaloneSynthPowerWeight
open MeasureTheory Set Filter
open scoped Topology SchwartzMap
namespace MasulloRH.SynthPower
noncomputable section

def physicalWeight (b p x : ℝ) := (1+|x|)^p*Real.exp (b*|x|)

theorem power_cont (p : ℝ) : Continuous (fun x : ℝ=>(1+|x|)^p) :=
  (show Continuous (fun x : ℝ=>1+|x|) by fun_prop).rpow_const (fun x=>Or.inl (by dsimp; positivity))

theorem physicalWeight_cont (b p : ℝ) : Continuous (physicalWeight b p) := by
  exact (power_cont p).mul (by fun_prop)
theorem physicalWeight_pos (b p x : ℝ) : 0<physicalWeight b p x := by unfold physicalWeight; positivity

theorem power_sub (p : ℝ) (hp : 0≤p) (x y : ℝ) :
    (1+|x|)^p ≤ (1+|y|)^p*(1+|x-y|)^p := by
  rw [←Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity) (SynthWall.one_abs_submultiplicative x y) hp

theorem inverse_power_memLp (p : ℝ) (hp : 1/2<p) : MemLp (fun x : ℝ=>(1+|x|)^(-p)) 2 volume := by
  apply (memLp_two_iff_integrable_sq (power_cont (-p)).aestronglyMeasurable).mpr
  apply (integrable_one_add_norm (μ:=volume) (E:=ℝ) (r:=p*2) (by simp; linarith)).congr
  filter_upwards with x
  rw [Real.norm_eq_abs,←Real.rpow_mul_natCast (by positivity)]
  congr 1
  push_cast; ring

theorem integrable_exp_of_weighted_memLp {b p : ℝ} (hp : 1/2<p) {f : ℝ→ℂ}
    (hF : MemLp (fun x=>physicalWeight b p x*‖f x‖) 2 volume) :
    Integrable (fun x=>Real.exp (b*|x|)*‖f x‖) := by
  apply (hF.integrable_mul (inverse_power_memLp p hp)).congr
  filter_upwards with x
  change (physicalWeight b p x*‖f x‖)*(1+|x|)^(-p)=_
  rw [physicalWeight,Real.rpow_neg (by positivity)]
  field_simp

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

end
end MasulloRH.SynthPower
end StandaloneSynthPowerWeight


-- Local source: SynthL2Glue
section StandaloneSynthL2Glue
open MeasureTheory Filter Set FourierTransform
open scoped Topology FourierTransform
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall

theorem fourier_injective_cont {f g : ℝ→ℂ} (hc : Continuous f) (hd : Continuous g)
    (hf : Integrable f) (hg : Integrable g) (h : 𝓕 f=𝓕 g) : f=g := by
  let k := f-g
  have hz : 𝓕 k=(0:ℝ→ℂ) := by
    funext ξ
    have hh := congrFun h ξ
    rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul] at hh
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [k,Pi.sub_apply,smul_sub,Pi.zero_apply]
    rw [integral_sub]
    · exact sub_eq_zero.mpr hh
    all_goals
      let a (x : ℝ) := Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I)
      first | apply hf.norm.mono' ((show Continuous a by dsimp [a]; fun_prop).smul hc).aestronglyMeasurable
            | apply hg.norm.mono' ((show Continuous a by dsimp [a]; fun_prop).smul hd).aestronglyMeasurable
      filter_upwards with x
      simp [a,norm_smul,Complex.norm_exp]
  have he := (hc.sub hd).fourierInv_fourier_eq (hf.sub hg) (hz ▸ integrable_zero ..)
  rw [hz] at he
  have hzero : 𝓕⁻ (0:ℝ→ℂ)=(0:ℝ→ℂ) := by funext x; simp [Real.fourierInv_eq']
  rw [hzero] at he
  exact sub_eq_zero.mp he.symm

/-- A zero-free shared Fourier wall identifies kernels found by division in two different strips. -/
theorem seed_kernel_unique (σ : ℝ) (hE : ∀ ξ : ℝ,E (vertical σ (freq*ξ)+1/2)≠0)
    (q q' : ℝ→ℂ) (hc : Continuous q) (hc' : Continuous q')
    (hI : Integrable (tilt σ q)) (hI' : Integrable (tilt σ q'))
    (heq : conv seed q=conv seed q') : q=q' := by
  have hseed := tilt_int (show |σ|≤|σ| from le_rfl) seed_cont.aestronglyMeasurable (seed_weighted |σ|)
  have htilt : tilt σ q=tilt σ q' := by
    apply fourier_injective_cont ((show Continuous (fun x : ℝ => (Real.exp (σ*x):ℂ)) by fun_prop).mul hc)
      ((show Continuous (fun x : ℝ => (Real.exp (σ*x):ℂ)) by fun_prop).mul hc') hI hI'
    funext ξ
    have h := congrArg (fun f : ℝ→ℂ => 𝓕 (tilt σ f) ξ) heq
    change 𝓕 (tilt σ (conv seed q)) ξ=𝓕 (tilt σ (conv seed q')) ξ at h
    rw [fourier_tilt_conv hseed hI,fourier_tilt_conv hseed hI'] at h
    apply mul_left_cancel₀ _ h
    rw [←profile_lap seed σ ξ]
    simpa only [profile,E,add_sub_cancel_right] using hE ξ
  funext x
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') (congrFun htilt x)

end
end MasulloRH.SynthesisStrip
end StandaloneSynthL2Glue


-- Local source: SynthPowerPrimal
section StandaloneSynthPowerPrimal
open Set Filter MeasureTheory FourierTransform
open scoped Topology InnerProductSpace FourierTransform
namespace MasulloRH.SynthPower
noncomputable section
open SynthWall SynthesisStrip
open StripTrace (lap)

theorem weighted_memLp_exp_inner {b p : ℝ} (hp : 0≤p) {f : ℝ→ℂ} (hm : AEStronglyMeasurable f)
    (hw : MemLp (fun x=>physicalWeight b p x*‖f x‖) 2 volume) (c : ℝ) (hc : c<b) :
    Integrable (fun x : ℝ=>‖f x‖*Real.exp (c*|x|)) := by
  let δ := b-c
  have hδ : 0<δ := sub_pos.mpr hc
  have hI : Integrable (fun x : ℝ=>Real.exp (-(2*δ)*|x|)) := by
    have hd : 0<2*δ := by positivity
    have h := (integrable_comp_mul_left_iff (fun x : ℝ=>Real.exp (-|x|)) hd.ne').mpr int_exp
    simpa only [Function.comp_def,abs_mul,abs_of_pos hd,neg_mul] using h
  have hL : MemLp (fun x : ℝ=>Real.exp (-δ*|x|)) 2 volume := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    apply hI.congr
    exact .of_forall fun x => by dsimp only; rw [←Real.exp_nat_mul]; congr 1; push_cast; ring
  apply (hw.integrable_mul hL).mono' (hm.norm.mul (by fun_prop))
  filter_upwards with x
  have h1 : 1≤(1+|x|)^p := Real.one_le_rpow (by linarith [abs_nonneg x]) hp
  change ‖‖f x‖*Real.exp (c*|x|)‖≤(physicalWeight b p x*‖f x‖)*Real.exp (-δ*|x|)
  rw [Real.norm_of_nonneg (by positivity),physicalWeight]
  calc
    _ = 1*(Real.exp (b*|x|)*‖f x‖*Real.exp (-δ*|x|)) := by
      rw [one_mul,mul_comm (Real.exp _),mul_assoc,←Real.exp_add]; congr 2; dsimp only [δ]; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right h1 (by positivity)).trans_eq (by ring)

theorem tilt_envelope {b p σ : ℝ} (hσ : |σ|≤b) {f : ℝ→ℂ} (hm : AEStronglyMeasurable f)
    (hf : MemLp (fun x=>physicalWeight b p x*‖f x‖) 2 volume) :
    MemLp (fun x : ℝ=>(1+|x|)^p*‖tilt σ f x‖) 2 volume := by
  have ht : AEStronglyMeasurable (tilt σ f) :=
    (show Continuous (fun x : ℝ => (Real.exp (σ*x):ℂ)) by fun_prop).aestronglyMeasurable.mul hm
  apply hf.mono' ((power_cont p).aestronglyMeasurable.mul ht.norm)
  filter_upwards with x
  change ‖(1+|x|)^p*‖tilt σ f x‖‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (exp_tilt_le hσ f x) (by positivity : 0≤(1+|x|)^p)).trans_eq (mul_assoc _ _ _).symm

end
end MasulloRH.SynthPower
end StandaloneSynthPowerPrimal


-- Local source: SynthL2Energy
section StandaloneSynthL2Energy
open MeasureTheory Filter Set FourierTransform
open scoped Topology FourierTransform SchwartzMap Convolution
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall
open StripTrace (lap)

theorem inverse_wall_kernel (σ ε : ℝ) (hε : 0<ε) (f q : ℝ→ℂ)
    (hf : Integrable (tilt σ f)) (hq : Continuous q) (hI : Integrable (tilt σ q))
    (he : conv (dilate dampingKernel ε) f=conv seed q)
    (m : 𝓢(ℝ,ℂ)) (hm : ∀ξ,m ξ=damp ε (vertical σ (freq*ξ))/centeredE (vertical σ (freq*ξ)))
    (hn : ∀ξ,centeredE (vertical σ (freq*ξ))≠0) :
    tilt σ q=conv (𝓕⁻ m : 𝓢(ℝ,ℂ)) (tilt σ f) := by
  let k : 𝓢(ℝ,ℂ) := 𝓕⁻ m
  have hs := tilt_int (show |σ|≤|σ| from le_rfl) seed_cont.aestronglyMeasurable (seed_weighted |σ|)
  have heF (ξ : ℝ) := congrArg (fun g : ℝ→ℂ => 𝓕 (tilt σ g) ξ) he
  have hbdd : BddAbove (Set.range fun x => ‖k x‖) := ⟨SchwartzMap.seminorm ℝ 0 0 k,by
    rintro _ ⟨x,rfl⟩; exact SchwartzMap.norm_le_seminorm ℝ k x⟩
  apply fourier_injective_cont ((show Continuous (fun x : ℝ => (Real.exp (σ*x):ℂ)) by fun_prop).mul hq)
    (hbdd.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul ℂ ℂ) k.continuous hf)
    hI (k.integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf)
  funext ξ
  have H := heF ξ
  change 𝓕 (tilt σ (conv (dilate dampingKernel ε) f)) ξ=𝓕 (tilt σ (conv seed q)) ξ at H
  rw [fourier_tilt_conv (dampingKernel_scaled_integrable hε σ) hf,fourier_tilt_conv hs hI,
    dampingKernel_scaled_fourier hε,←profile_lap seed σ ξ] at H
  change 𝓕 (tilt σ q) ξ=𝓕 ((k:ℝ→ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] tilt σ f) ξ
  rw [Real.fourier_mul_convolution_eq k.integrable hf,←SchwartzMap.fourier_coe,show 𝓕 k=m from fourier_fourierInv_eq m,hm]
  let z := vertical σ (freq*ξ)
  have hz : centeredE z=lap seed z := by simp [centeredE,E]
  change damp ε z * 𝓕 (tilt σ f) ξ = lap seed z * 𝓕 (tilt σ q) ξ at H
  change 𝓕 (tilt σ q) ξ = damp ε z/centeredE z * 𝓕 (tilt σ f) ξ
  rw [←hz] at H
  rw [div_mul_eq_mul_div,eq_div_iff (hn ξ),mul_comm]
  exact H.symm

theorem wall_energy (b p σ ε : ℝ) (hp : 0≤p) (hσ : |σ|≤b) (hε : 0<ε)
    (f q : ℝ→ℂ) (hmf : Measurable f) (hf : Integrable (tilt σ f))
    (hF : MemLp (fun x=>SynthPower.physicalWeight b p x*‖f x‖) 2 volume)
    (hq : Continuous q) (hI : Integrable (tilt σ q))
    (he : conv (dilate dampingKernel ε) f=conv seed q)
    (m : 𝓢(ℝ,ℂ)) (hm : ∀ξ,m ξ=damp ε (vertical σ (freq*ξ))/centeredE (vertical σ (freq*ξ)))
    (hn : ∀ξ,centeredE (vertical σ (freq*ξ))≠0)
    (C : ℝ) (hC : (∫x : ℝ,(1+|x|)^p*‖(𝓕⁻ m : 𝓢(ℝ,ℂ)) x‖)≤C) :
    mass (fun x : ℝ=>(1+|x|)^p) (tilt σ q) ≤ C^2*mass (SynthPower.physicalWeight b p) f := by
  let w := fun x : ℝ => (1+|x|)^p
  let k : 𝓢(ℝ,ℂ) := 𝓕⁻ m
  have ht := SynthPower.tilt_envelope hσ hmf.aestronglyMeasurable hF
  have h := (weighted_young (SynthPower.power_cont p) (fun t=>by positivity) (SynthPower.power_sub p hp)
    k.integrable hf (SynthPower.one_abs_rpow_schwartz p k) ht).2
  rw [inverse_wall_kernel σ ε hε f q hf hq hI he m hm hn]
  apply h.trans (mul_le_mul (pow_le_pow_left₀ (integral_nonneg (fun x => by positivity)) hC 2) _ (integral_nonneg (fun x=>sq_nonneg _)) (sq_nonneg C))
  apply integral_mono ((memLp_two_iff_integrable_sq ht.1).mp ht) ((memLp_two_iff_integrable_sq hF.1).mp hF)
  intro x
  apply pow_le_pow_left₀ (by positivity)
  rw [SynthPower.physicalWeight,mul_assoc]
  exact mul_le_mul_of_nonneg_left (exp_tilt_le hσ f x) (by positivity)

theorem full_mass_of_walls (a p : ℝ) (q : ℝ→ℂ) (hq : Measurable q)
    (hP : MemLp (fun x=>SynthPower.physicalWeight a p x*‖q x‖) 2 volume) (ha : 0≤a) (M : ℝ)
    (hw : ∀ σ : ℝ, |σ|=a → mass (fun x : ℝ=>(1+|x|)^p) (tilt σ q)≤M) :
    mass (SynthPower.physicalWeight a p) q≤2*M := by
  let w (x : ℝ) := (1+|x|)^p
  let m (σ x : ℝ) := (w x*‖tilt σ q x‖)^2
  have hI (σ : ℝ) (h : |σ|=a) : Integrable (m σ) := by
    have ht := SynthPower.tilt_envelope h.le hq.aestronglyMeasurable hP
    exact (memLp_two_iff_integrable_sq ht.1).mp ht
  have hpos : |a|=a := abs_of_nonneg ha
  have hneg : |(-a)|=a := (abs_neg _).trans hpos
  have hpt (x : ℝ) : (SynthPower.physicalWeight a p x*‖q x‖)^2 ≤ m a x + m (-a) x := by
    rcases le_total 0 x with hx|hx
    · apply le_add_of_le_of_nonneg (le_of_eq _) (sq_nonneg _)
      simp [m,w,SynthPower.physicalWeight,tilt_norm,abs_of_nonneg hx,mul_assoc]
    · apply le_add_of_nonneg_of_le (sq_nonneg _) (le_of_eq _)
      dsimp only [m,w]
      rw [tilt_norm,SynthPower.physicalWeight,abs_of_nonpos hx,mul_neg,neg_mul,mul_assoc]
  have hi := integral_mono ((memLp_two_iff_integrable_sq hP.1).mp hP) ((hI a hpos).add (hI (-a) hneg)) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_add (hI a hpos) (hI (-a) hneg)] at hi
  exact hi.trans (by change mass w (tilt a q) + mass w (tilt (-a) q)≤2*M; linarith [hw a hpos,hw (-a) hneg])

end
end MasulloRH.SynthesisStrip
end StandaloneSynthL2Energy


-- Local source: SynthL2Fatou
section StandaloneSynthL2Fatou
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace MasulloRH.SynthPower
noncomputable section

/-- Uniform energy on approaching widths gives the same energy bound at the limit,
even for widths that approach through a nonmonotone sequence. -/
theorem weighted_memLp_of_tendsto_widths (b p : ℝ) (B : ℕ→ℝ)
    (hB : Tendsto B atTop (𝓝 b)) (q : ℝ→ℂ) (hq : Continuous q) (M : ℝ)
    (hw : ∀ n, MemLp (fun x=>physicalWeight (B n) p x*‖q x‖) 2 volume)
    (hmass : ∀ n, SynthWall.mass (physicalWeight (B n) p) q ≤ M) :
    MemLp (fun x=>physicalWeight b p x*‖q x‖) 2 volume ∧
      SynthWall.mass (physicalWeight b p) q ≤ M := by
  let F (a x : ℝ) := (physicalWeight a p x*‖q x‖)^2
  have hF (a : ℝ) : Continuous (F a) := ((physicalWeight_cont a p).mul hq.norm).pow 2
  have hN (a x : ℝ) : 0≤F a x := sq_nonneg _
  have hI (n : ℕ) : Integrable (F (B n)) :=
    (memLp_two_iff_integrable_sq (hw n).1).mp (hw n)
  have hlim (x : ℝ) : Tendsto (fun n=>ENNReal.ofReal (F (B n) x)) atTop (𝓝 (ENNReal.ofReal (F b x))) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    exact (show Continuous (fun a=>F a x) by dsimp [F,physicalWeight]; fun_prop).continuousAt.tendsto.comp hB
  have hle : (∫⁻ x : ℝ, ENNReal.ofReal (F b x))≤ENNReal.ofReal M := by
    calc
      _ = ∫⁻ x : ℝ, atTop.liminf (fun n=>ENNReal.ofReal (F (B n) x)) := by
        exact lintegral_congr (fun x=>(hlim x).liminf_eq.symm)
      _ ≤ atTop.liminf (fun n=>∫⁻ x : ℝ, ENNReal.ofReal (F (B n) x)) :=
        lintegral_liminf_le (fun n=>ENNReal.measurable_ofReal.comp (hF _).measurable)
      _ ≤ _ := by
        apply liminf_le_of_frequently_le' (.of_forall _)
        intro n
        rw [←ofReal_integral_eq_lintegral_ofReal (hI n) (.of_forall (hN _))]
        exact ENNReal.ofReal_le_ofReal (hmass n)
  have hint : Integrable (F b) :=
    ⟨(hF b).aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal (.of_forall (hN b))).mpr
      (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨(memLp_two_iff_integrable_sq ((physicalWeight_cont b p).mul hq.norm).aestronglyMeasurable).mpr hint,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hint (.of_forall (hN _))] at hle
  have hM : 0≤M := (integral_nonneg (hN (B 0))).trans (hmass 0)
  exact (ENNReal.ofReal_le_ofReal_iff hM).mp hle

end
end MasulloRH.SynthPower
end StandaloneSynthL2Fatou


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

theorem reconstruct (p : ℝ) (hp : 0≤p) {Q : ℂ→ℂ} {b : ℝ} (hb : 0≤b)
    (hC : ContinuousOn Q (closedStrip b)) (hD : DifferentiableOn ℂ Q (openStrip b))
    (hh : GoodHeights Q b) (hwa : WallFactor p Q (-b)) (hwb : WallFactor p Q b) :
    ∃ q : ℝ→ℂ, Continuous q ∧ Integrable (fun x => Real.exp (b*|x|)*‖q x‖) ∧
      MemLp (fun x => (1+|x|)^p*(Real.exp (b*|x|)*‖q x‖)) 2 volume ∧
      ∀ σ : ℝ, |σ|=b → tilt σ q=𝓕⁻ (profile Q σ) ∧ 𝓕 (tilt σ q)=profile Q σ := by
  apply MasulloRH.bilateral_fourier_reconstruction_from_schwartz_walls b p hb hp Q hC hD hh
  intro σ hσ
  rcases (abs_eq hb).mp hσ with rfl | rfl
  · exact hwb
  · exact hwa

end
end MasulloRH.SynthPower
end StandaloneSynthPowerReconstruction


-- Local source: SynthPowerQuotient
section StandaloneSynthPowerQuotient
open Set Filter MeasureTheory FourierTransform
open scoped Topology SchwartzMap FourierTransform ContDiff
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall

/-- Regularized division reconstructs a finite-energy physical kernel on every
pair of sufficiently separated walls. Its two tilted Fourier transforms agree
with the regularized analytic quotient on the entire boundary. -/
theorem reconstruct_quotient_of_separation_p (b p ε : ℝ) (hb0 : 0≤b) (hb : b<1/2) (hp : 0≤p) (hε : 0<ε)
    (d : ℝ) (hd : 0<d)
    (hsep : ∀ t, Avoids d 2 (vertical b t) ∧ Avoids d 2 (vertical (-b) t))
    (F : ℂ→ℂ) (hC : ContinuousOn F (closedStrip b)) (ha : AnalyticOnNhd ℂ F (openStrip b))
    (ho : ∀ s ∈ openStrip b, E (s+1/2)=0 → analyticOrderAt E (s+1/2)≤analyticOrderAt F s)
    (M : ℝ) (hM : 0≤M) (hF : ∀ s∈closedStrip b, ‖F s‖≤M)
    (hw : ∀ σ : ℝ, |σ|=b → ∃ f : ℝ→ℂ, Integrable f ∧
      MemLp (fun x : ℝ=>(1+|x|)^p*‖f x‖) 2 volume ∧ ∀ ξ, profile F σ ξ=(𝓕 f) ξ) :
    ∃ q : ℝ→ℂ, Continuous q ∧ Integrable (fun x => Real.exp (b*|x|)*‖q x‖) ∧
      MemLp (fun x => (1+|x|)^p*(Real.exp (b*|x|)*‖q x‖)) 2 volume ∧
      ∀ σ : ℝ, |σ|=b → tilt σ q=𝓕⁻ (profile (dividedTransform ε F) σ) ∧
        𝓕 (tilt σ q)=profile (dividedTransform ε F) σ := by
  obtain ⟨hQ,haQ⟩ := dividedTransform_regular b ε F hC ha ho (wall_nonzero_of_separation b hb d hd hsep)
  obtain ⟨r,hr,T,_,hT,hsepT⟩ := exists_horizontal_separation
  have hgood := quotient_good_heights b ε hb hε F M hM hF r hr 2 T hT (fun n u _ => hsepT n u)
  have fac (σ : ℝ) (hσ : |σ|=b) (h : ∀ t, Avoids d 2 (vertical σ t)) :
      SynthPower.WallFactor p (dividedTransform ε F) σ := by
    obtain ⟨f,hf,hw,hFour⟩ := hw σ hσ
    obtain ⟨v,hv⟩ := quotient_wall_multiplier σ ε (hσ.trans_lt hb) hε d hd 2 h
    refine ⟨f,v,hf,hw,?_⟩
    intro ξ
    have hn := wall_nonzero_of_separation b hb d hd hsep (vertical σ (freq*ξ)) (by simpa only [vertical_re] using hσ)
    rw [hv,←hFour,profile,profile,dividedTransform_eq _ _ _ hn]
    unfold centeredE
    ring
  exact SynthPower.reconstruct p hp hb0 hQ haQ hgood
    (fac (-b) (by simp [abs_of_nonneg hb0]) (fun t => (hsep t).2))
    (fac b (abs_of_nonneg hb0) (fun t => (hsep t).1))
end
end MasulloRH.SynthesisStrip
end StandaloneSynthPowerQuotient


-- Local source: SynthPowerFactorization
section StandaloneSynthPowerFactorization
open MeasureTheory Filter Set FourierTransform
open scoped Topology FourierTransform
namespace MasulloRH.SynthPower
noncomputable section
open SynthWall SynthesisStrip
open StripTrace (lap)

/-- Division by the actual dyadic Gaussian theta generator. The quotient solves
a physical convolution equation in the two-sided weighted space. -/
theorem seed_factorization_of_exp (b p ε : ℝ) (hb0 : 0≤b) (hb : b<1/2) (hp : 0≤p) (hε : 0<ε)
    (d : ℝ) (hd : 0<d) (hsep : ∀t, Avoids d 2 (vertical b t) ∧ Avoids d 2 (vertical (-b) t))
    (f : ℝ→ℂ) (hm : Measurable f)
    (hi : Integrable (fun x : ℝ => ‖f x‖*Real.exp (b*|x|)))
    (hw : MemLp (fun x=>physicalWeight b p x*‖f x‖) 2 volume)
    (ho : ∀s∈openStrip b,E (s+1/2)=0 → analyticOrderAt E (s+1/2)≤analyticOrderAt (lap f) s) :
    ∃ q : ℝ→ℂ, Continuous q ∧ Integrable (fun x=>Real.exp (b*|x|)*‖q x‖) ∧
      MemLp (fun x=>physicalWeight b p x*‖q x‖) 2 volume ∧
      conv (dilate dampingKernel ε) f=conv seed q := by
  obtain ⟨hC,hA,hB⟩ := lap_regular hm.aestronglyMeasurable hi
  let F := lap f
  let M := ∫x : ℝ, ‖f x‖*Real.exp (b*|x|)
  have hM : 0≤M := integral_nonneg (fun x => by positivity)
  obtain ⟨q,hq,hqI,hqW,hqF⟩ := reconstruct_quotient_of_separation_p b p ε hb0 hb hp hε d hd hsep F hC hA ho M hM hB
    (fun σ hσ => ⟨tilt σ f,tilt_int hσ.le hm.aestronglyMeasurable hi,tilt_envelope hσ.le hm.aestronglyMeasurable hw,profile_lap f σ⟩)
  have hqs : Integrable (fun x => ‖q x‖*Real.exp (b*|x|)) := by simpa only [mul_comm] using hqI
  have hin {g : ℝ→ℂ} (hg : AEStronglyMeasurable g)
      (h : Integrable (fun x => ‖g x‖*Real.exp (b*|x|))) : Integrable g :=
    h.mono' hg (.of_forall (fun x => le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg hb0 (abs_nonneg _)))))
  have hb' : |b|=b := abs_of_nonneg hb0
  refine ⟨q,hq,hqI,(by simpa only [physicalWeight,mul_assoc] using hqW),?_⟩
  apply damping_convolution_identify (σ:=b) hε (hin hm.aestronglyMeasurable hi) (tilt_int hb'.le hm.aestronglyMeasurable hi)
    (hin hq.aestronglyMeasurable hqs) (tilt_int hb'.le hq.aestronglyMeasurable hqs)
  intro ξ
  let s := vertical b (freq*ξ)
  have hs : |s.re|=b := by simpa [s] using hb'
  have hn : E (s+1/2)≠0 := wall_nonzero_of_separation b hb d hd hsep s hs
  have hsE : lap seed s=E (s+1/2) := by simp [E]
  rw [←profile_lap f b ξ,←profile_lap seed b ξ,(hqF b hb').2]
  change damp ε s*lap f s=lap seed s*dividedTransform ε F s
  rw [hsE,dividedTransform_eq _ _ _ hn]
  dsimp only [F]
  exact (mul_div_cancel₀ _ hn).symm

end
end MasulloRH.SynthPower
end StandaloneSynthPowerFactorization


-- Local source: SynthL2Factor
section StandaloneSynthL2Factor
open MeasureTheory Filter Set FourierTransform
open scoped Topology FourierTransform SchwartzMap
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall
open StripTrace (lap)

theorem seed_factorization_by_limit (b p ε : ℝ) (hb : 0<b) (hB : b<1/2) (hp : 0≤p) (hP : p≤1)
    (hε : 0<ε) (d : ℝ) (hd : 0<d) (B : ℕ→ℝ) (hmono : Monotone B) (hlim : Tendsto B atTop (𝓝 b))
    (hseq : ∀ n, b/2≤B n ∧ B n<b ∧ GoodWall d (B n)) (f : ℝ→ℂ) (hmf : Measurable f)
    (hw : MemLp (fun x=>SynthPower.physicalWeight b p x*‖f x‖) 2 volume)
    (ho : ∀s∈openStrip b,E (s+1/2)=0 → analyticOrderAt E (s+1/2)≤analyticOrderAt (lap f) s) :
    ∃ q : ℝ→ℂ, Continuous q ∧ Integrable q ∧
      MemLp (fun x=>SynthPower.physicalWeight b p x*‖q x‖) 2 volume ∧
      conv (dilate dampingKernel ε) f=conv seed q := by
  classical
  have h0 (n) : 0≤B n := (by positivity : 0≤b/2).trans (hseq n).1
  have hi (n) := SynthPower.weighted_memLp_exp_inner hp hmf.aestronglyMeasurable hw (B n) (hseq n).2.1
  have hF (n : ℕ) : MemLp (fun x=>SynthPower.physicalWeight (B n) p x*‖f x‖) 2 volume := by
    apply hw.mono' ((SynthPower.physicalWeight_cont _ _).aestronglyMeasurable.mul hmf.aestronglyMeasurable.norm)
    filter_upwards with x
    change ‖SynthPower.physicalWeight (B n) p x*‖f x‖‖≤_
    rw [Real.norm_of_nonneg (mul_nonneg (SynthPower.physicalWeight_pos _ _ _).le (norm_nonneg _))]
    unfold SynthPower.physicalWeight
    gcongr
    exact (hseq n).2.1.le
  have hex (n : ℕ) := SynthPower.seed_factorization_of_exp (B n) p ε (h0 n) ((hseq n).2.1.trans hB)
    hp hε d hd (hseq n).2.2 f hmf (hi n) (hF n)
    (fun s hs => ho s ((show |s.re|<B n from hs).trans (hseq n).2.1))
  choose q hc hqI hqW he using hex
  have hqe (n) : Integrable (fun x => ‖q n x‖*Real.exp (B n*|x|)) := by simpa only [mul_comm] using hqI n
  have hmin (n) : B 0≤B n := hmono (Nat.zero_le _)
  have hfixed (n : ℕ) : q 0 = q n := by
    apply seed_kernel_unique (B 0) (fun ξ => wall_nonzero_of_separation (B 0) ((hseq 0).2.1.trans hB) d hd
      (hseq 0).2.2 _ (by simp [abs_of_nonneg (h0 0)])) _ _ (hc 0) (hc n)
      (tilt_int (show |B 0|≤B 0 by rw [abs_of_nonneg (h0 0)]) (hc 0).aestronglyMeasurable (hqe 0))
      (tilt_int (show |B 0|≤B n by rw [abs_of_nonneg (h0 0)]; exact hmin n) (hc n).aestronglyMeasurable (hqe n))
    exact (he 0).symm.trans (he n)
  obtain ⟨W,hW,C,hC,hK⟩ := uniform_inverse_wall_kernels b ε d hB hε hd
  let M := C^2*mass (SynthPower.physicalWeight b p) f
  have hbound (n : ℕ) (σ : ℝ) (hσ : |σ|=B n) :
      mass (fun x : ℝ=>(1+|x|)^p) (tilt σ (q n))≤M := by
    have ht (t : ℝ) : Avoids d 2 (vertical σ t) := by
      rcases (abs_eq (h0 n)).mp hσ with rfl|rfl
      · exact ((hseq n).2.2 t).1
      · exact ((hseq n).2.2 t).2
    let u : SelectedWall b d := ⟨σ,hσ.le.trans (hseq n).2.1.le,ht⟩
    have hn (ξ : ℝ) : centeredE (vertical σ (freq*ξ))≠0 :=
      wall_nonzero_of_separation (B n) ((hseq n).2.1.trans hB) d hd (hseq n).2.2 _ (by simpa)
    exact wall_energy b p σ ε hp u.prop.1 hε f (q n) hmf (tilt_int hσ.le hmf.aestronglyMeasurable (hi n)) hw (hc n)
      (tilt_int hσ.le (hc n).aestronglyMeasurable (hqe n)) (he n) (W u) (hW u) hn C (hK u p hP).2
  have hfull (n : ℕ) : mass (SynthPower.physicalWeight (B n) p) (q 0)≤2*M := by
    rw [hfixed n]
    exact full_mass_of_walls (B n) p _ (hc n).measurable (hqW n) (h0 n) M (hbound n)
  have hfinal := SynthPower.weighted_memLp_of_tendsto_widths b p B hlim (q 0) (hc 0) (2*M)
    (fun n => by rw [hfixed n]; exact hqW n) hfull
  have hInt : Integrable (q 0) := (hqe 0).mono' (hc 0).aestronglyMeasurable (.of_forall fun x =>
    le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg (h0 0) (abs_nonneg _))))
  exact ⟨q 0,hc 0,hInt,hfinal.1,he 0⟩

end
end MasulloRH.SynthesisStrip
end StandaloneSynthL2Factor


-- Local source: SynthPublicCoordinates
section StandaloneSynthPublicCoordinates
open Set Filter MeasureTheory FourierTransform
open scoped FourierTransform
namespace MasulloRH.SynthesisStrip
noncomputable section
open SynthWall

theorem rationalDyadicThetaSeed_eq : rationalDyadicThetaSeed=seed := by
  funext x
  unfold rationalDyadicThetaSeed seed StripTheta.logTheta
  congr 1
  apply tsum_congr
  intro n
  exact ((Classical.choose_spec dyadic_gaussian_theta_mellin).1 _).symm

theorem rationalQuarticKernel_eq (ε : ℝ) : rationalQuarticKernel ε=dilate dampingKernel ε := by
  have h (ξ : ℝ) : dampingProfile 1 0 one_pos ξ =
      (Real.exp (-((-2*Real.pi*ξ)^4)):ℂ) := by
    rw [dampingProfile_apply,profile,damp,vertical]
    simp [freq,Complex.ofReal_exp]
    congr 2
    rw [←neg_mul _ Complex.I,mul_pow,Complex.I_pow_four,mul_one]
  funext x
  unfold rationalQuarticKernel dilate dampingKernel
  rw [SchwartzMap.fourierInv_coe,show (dampingProfile 1 0 one_pos:ℝ→ℂ)=_ from funext h]

end
end MasulloRH.SynthesisStrip
end StandaloneSynthPublicCoordinates


-- Local source: SynthPublicMoments
section StandaloneSynthPublicMoments
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
namespace MasulloRH.SynthPower
noncomputable section
open SynthWall SynthesisStrip
open StripTrace (lap)

theorem divisor_order_of_moments (b p : ℝ) (hB : b<1/2) (hp : 0≤p)
    (f : ℝ→ℂ) (hm : Measurable f) (hw : MemLp (fun x=>physicalWeight b p x*‖f x‖) 2 volume)
    (hD : RationalStripDivisorMoments b f) (s : ℂ) (hs : s∈openStrip b) (hE : E (s+1/2)=0) :
    analyticOrderAt E (s+1/2)≤analyticOrderAt (lap f) s := by
  obtain ⟨c,hsc,hcb⟩ := exists_between (show |s.re|<b from hs)
  have hi := weighted_memLp_exp_inner hp hm.aestronglyMeasurable hw c hcb
  have hsr : (s+1/2).re=s.re+1/2 := by simp
  obtain ⟨hl,hr⟩ := abs_lt.mp (show |s.re|<b from hs)
  have h0 : 0<(s+1/2).re := by rw [hsr]; linarith
  have h1 : (s+1/2).re<1 := by rw [hsr]; linarith
  obtain ⟨_,hz,ho⟩ := E_strip _ h0 h1
  have hfin : analyticOrderAt E (s+1/2)≠⊤ := by
    intro h
    have hall := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero _ E_entire.analyticAt).mp h
    obtain ⟨C,_,hc⟩ := E_anchor
    have hbad := hc 2 (by norm_num)
    simp [hall] at hbad
    norm_num at hbad
  rw [←ENat.natCast_toNat hfin,ho]
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((lap_regular hm.aestronglyMeasurable hi).2.1 s hsc)).mpr
  intro r hr
  rw [StripTrace.lap_iteratedDeriv hm.aestronglyMeasurable hi r hsc]
  have h := hD (s+1/2) (hz.mp hE) h0 h1 (by simpa [hsr] using (show |s.re|<b from hs)) r hr
  simpa only [StripPhysical.moment,add_sub_cancel_right] using h

end
end MasulloRH.SynthPower
end StandaloneSynthPublicMoments


-- Local source: SynthPublicDivision
section StandaloneSynthPublicDivision
open MeasureTheory Filter
open scoped Topology Convolution

open MasulloRH

/-- On almost every positive strip of half-width less than one half, quartic
smoothing is divisible by the centered arithmetic theta seed whenever the
Laplace moments of the input vanish on the full interior zeta divisor. -/
theorem solution :
    ∀ᵐ b : ℝ, 0<b → b<1/2 → ∀ p : ℝ, 0≤p → ∀ f : ℝ→ℂ, Measurable f →
      MemLp (fun x : ℝ => ((1+|x|)^p*Real.exp (b*|x|))*‖f x‖) 2 volume →
      MasulloRH.RationalStripDivisorMoments b f → ∀ ε : ℝ, 0<ε →
      ∃ q : ℝ→ℂ, Continuous q ∧ Integrable q ∧
        MemLp (fun x : ℝ => ((1+|x|)^p*Real.exp (b*|x|))*‖q x‖) 2 volume ∧
        (MasulloRH.rationalQuarticKernel ε ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
          (MasulloRH.rationalDyadicThetaSeed ⋆[ContinuousLinearMap.mul ℂ ℂ] q) := by
  filter_upwards [SynthesisStrip.ae_approaching_good_walls] with b hbdy hb hB p hp f hm hw hD ε hε
  obtain ⟨d,hd,hsep,B,hmono,hlim,hseq⟩ := hbdy hb
  have hdiv := SynthPower.divisor_order_of_moments b p hB hp f hm hw hD
  simp only [SynthesisStrip.rationalQuarticKernel_eq,SynthesisStrip.rationalDyadicThetaSeed_eq]
  by_cases hP : 1/2<p
  · have hi : Integrable (fun x : ℝ=>‖f x‖*Real.exp (b*|x|)) := by
      simpa only [mul_comm] using SynthPower.integrable_exp_of_weighted_memLp (b:=b) (f:=f) hP hw
    obtain ⟨q,hq,hqI,hqW,he⟩ := SynthPower.seed_factorization_of_exp b p ε hb.le hB hp hε d hd hsep f hm hi hw hdiv
    refine ⟨q,hq,?_,hqW,he⟩
    exact hqI.mono' hq.aestronglyMeasurable (.of_forall fun x =>
      le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg hb.le (abs_nonneg x))))
  · exact SynthesisStrip.seed_factorization_by_limit b p ε hb hB hp (by linarith) hε d hd B hmono.monotone
      hlim hseq f hm hw hdiv
end StandaloneSynthPublicDivision

