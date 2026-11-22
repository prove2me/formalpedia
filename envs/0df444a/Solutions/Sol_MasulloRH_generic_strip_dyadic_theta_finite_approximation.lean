-- Prove2me | solution 1 for MasulloRH.generic_strip_dyadic_theta_finite_approximation
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T21:43:41.221403+00:00
-- url     : https://prove2.me/submissions/5ce30093-2bd2-4291-b7e0-eb5994cd8fde

import Mathlib
import Definitions.Def_MasulloRH_GaussianThetaDivision
import Theorems.Thm_MasulloRH_generic_strip_dyadic_theta_division
import Theorems.Thm_MasulloRH_dyadic_gaussian_theta_mellin

-- Local component: ThetaSynthesisWeightedYoung
/-!
Weighted Young inequality used by the actual-theta synthesis bridge.
The proof below is a minimal extraction from the accepted public proof
0ab415f7-6816-4b40-b9ec-50067de21560 by marozols, of theorem
24df0c86-b075-4107-9103-8fc580dde151 (generic_strip_dyadic_theta_division).
Only the namespace and enclosing section are renamed. The source helpers are
included explicitly: importing the public division theorem does not export them.
-/

-- Local source: SynthWallYoung
section ThetaSynthesisYoungExtraction
open Set MeasureTheory Filter
open scoped Topology Convolution SchwartzMap
namespace MasulloRH.ThetaSynthesisYoung
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
end MasulloRH.ThetaSynthesisYoung
end ThetaSynthesisYoungExtraction


-- Local component: ThetaSynthesisWeightFacts
/-!
Elementary facts about the literal weight used by the registered theta division
theorem. The submultiplicative polynomial estimate is the same one explicitly
proved in `ThetaSynthesisWeightedYoung` (an attributed source extraction).
-/

open MeasureTheory Set Filter
open scoped Topology

namespace MasulloRH.ThetaSynthesisWeight
noncomputable section

def weight (b p x : ℝ) : ℝ := (1 + |x|) ^ p * Real.exp (b * |x|)

theorem weight_continuous (b p : ℝ) : Continuous (weight b p) := by
  apply Continuous.mul
  · exact (show Continuous (fun x : ℝ => 1 + |x|) by fun_prop).rpow_const
      (fun x => Or.inl (by dsimp; positivity))
  · fun_prop

theorem weight_pos (b p x : ℝ) : 0 < weight b p x := by
  unfold weight
  positivity

theorem weight_nonneg (b p x : ℝ) : 0 ≤ weight b p x := (weight_pos b p x).le

theorem weight_one_le (b p : ℝ) (hb : 0 ≤ b) (hp : 0 ≤ p) (x : ℝ) :
    1 ≤ weight b p x := by
  apply one_le_mul_of_one_le_of_one_le
  · exact Real.one_le_rpow (by linarith [abs_nonneg x]) hp
  · exact Real.one_le_exp (mul_nonneg hb (abs_nonneg x))

@[simp] theorem weight_zero (b p : ℝ) : weight b p 0 = 1 := by simp [weight]

@[simp] theorem weight_neg (b p x : ℝ) : weight b p (-x) = weight b p x := by
  simp [weight]

theorem weight_submultiplicative (b p : ℝ) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (x t : ℝ) : weight b p x ≤ weight b p t * weight b p (x-t) := by
  have hpoly : (1+|x|)^p ≤ (1+|t|)^p * (1+|x-t|)^p := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity)
      (ThetaSynthesisYoung.one_abs_submultiplicative x t) hp
  have hexp : Real.exp (b*|x|) ≤ Real.exp (b*|t|) * Real.exp (b*|x-t|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := abs_add_le t (x-t)
    rw [add_sub_cancel] at h
    nlinarith
  apply (mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)).trans_eq
  dsimp [weight]
  ring

theorem weight_dilate (b p : ℝ) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) :
    weight b p (ε*t) ≤ weight b p t := by
  have ht : |ε*t| ≤ |t| := by
    rw [abs_mul, abs_of_pos hε]
    exact mul_le_of_le_one_left (abs_nonneg t) hε1
  apply mul_le_mul
  · exact Real.rpow_le_rpow (by positivity) (by linarith) hp
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hb)
  · exact (Real.exp_pos _).le
  · positivity

theorem weight_sq (b p x : ℝ) : (weight b p x)^2 = weight (2*b) (2*p) x := by
  dsimp [weight]
  rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), ← Real.exp_nat_mul]
  congr 1 <;> congr 1 <;> push_cast <;> ring

end
end MasulloRH.ThetaSynthesisWeight


-- Local component: ThetaSynthesisFiniteTranslates
/-!
Finite-translate approximation in weighted L², for the actual theta synthesis
corollary. No zero-location assertion is used in this functional-analysis layer.
-/

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ComplexConjugate

namespace MasulloRH.ThetaSynthesisFinite
noncomputable section

abbrev H := Lp ℂ 2 (volume : Measure ℝ)

def weighted (w : ℝ → ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := (w x : ℂ) * f x

theorem norm_weighted (w : ℝ → ℝ) (hw : ∀ x, 0 ≤ w x) (f : ℝ → ℂ) (x : ℝ) :
    ‖weighted w f x‖ = w x * ‖f x‖ := by
  simp [weighted, norm_mul, Complex.norm_real, abs_of_nonneg (hw x)]

theorem weighted_memLp {w : ℝ → ℝ} (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hF : MemLp (fun x => w x * ‖f x‖) 2 volume) :
    MemLp (weighted w f) 2 volume := by
  apply hF.congr_norm ((Complex.continuous_ofReal.comp hw).aestronglyMeasurable.mul hf)
  filter_upwards with x
  change ‖w x * ‖f x‖‖ = ‖weighted w f x‖
  rw [norm_weighted w hw0 f x, Real.norm_of_nonneg (mul_nonneg (hw0 x) (norm_nonneg _))]

theorem H_norm_sq (f : H) : ‖f‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
  simp only [inner_self_eq_norm_sq_to_K]
  apply integral_congr_ae
  filter_upwards with x
  norm_cast

theorem weighted_toLp_norm_sq {w : ℝ → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    {f : ℝ → ℂ} (hf : MemLp (weighted w f) 2 volume) :
    ‖hf.toLp (weighted w f)‖ ^ 2 = ∫ x : ℝ, (w x * ‖f x‖) ^ 2 := by
  rw [H_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, norm_weighted w hw0 f x]

theorem weighted_toLp_dist_sq {w : ℝ → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    {f g : ℝ → ℂ} (hf : MemLp (weighted w f) 2 volume)
    (hg : MemLp (weighted w g) 2 volume) :
    dist (hf.toLp (weighted w f)) (hg.toLp (weighted w g)) ^ 2 =
      ∫ x : ℝ, (w x * ‖g x - f x‖) ^ 2 := by
  rw [dist_eq_norm, H_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp (weighted w f)) (hg.toLp (weighted w g)),
    hf.coeFn_toLp, hg.coeFn_toLp] with x hx hfx hgx
  simp only [hx, Pi.sub_apply, hfx, hgx, weighted, ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (hw0 x), norm_sub_rev (f x) (g x)]

theorem exists_finite_sum_of_mem_closure_span
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (v : ι → E) (f : E)
    (hf : f ∈ (Submodule.span ℂ (range v)).topologicalClosure)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset ι) (a : ι → ℂ), ‖f - ∑ i ∈ s, a i • v i‖ < ε := by
  classical
  have hc : f ∈ closure (↑(Submodule.span ℂ (range v)) : Set E) := hf
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hc ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
  refine ⟨c.support, c, ?_⟩
  rw [← hc] at hfg
  simpa only [Finsupp.sum, dist_eq_norm] using hfg

open ThetaSynthesisYoung (conv)

theorem conv_comm (f g : ℝ → ℂ) : conv f g = conv g f := by
  funext x
  change (∫ t : ℝ, f t * g (x-t)) = ∫ t : ℝ, g t * f (x-t)
  rw [← integral_sub_left_eq_self (fun t : ℝ => f t * g (x-t)) volume x]
  simp only [sub_sub_cancel]
  apply integral_congr_ae
  filter_upwards with t
  exact mul_comm _ _

def absConv (f g : ℝ → ℂ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, ‖f t‖ * ‖g (x-t)‖

theorem absConv_nonneg (f g : ℝ → ℂ) (x : ℝ) : 0 ≤ absConv f g x :=
  integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem absConv_comm (f g : ℝ → ℂ) : absConv f g = absConv g f := by
  funext x
  unfold absConv
  rw [← integral_sub_left_eq_self (fun t : ℝ => ‖f t‖ * ‖g (x-t)‖) volume x]
  simp only [sub_sub_cancel]
  apply integral_congr_ae
  filter_upwards with t
  exact mul_comm _ _

theorem weighted_absConv_memLp {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hwsub : ∀ x t, w x ≤ w t * w (x-t))
    {k q : ℝ → ℂ} (hk : Integrable k) (hq : Integrable q)
    (hK : Integrable (fun x => w x * ‖k x‖))
    (hQ : MemLp (fun x => w x * ‖q x‖) 2 volume) :
    MemLp (fun x => w x * absConv k q x) 2 volume := by
  let K : ℝ → ℂ := fun x => (‖k x‖ : ℂ)
  let Q : ℝ → ℂ := fun x => (‖q x‖ : ℂ)
  have hki : Integrable K := hk.norm.ofReal
  have hqi : Integrable Q := hq.norm.ofReal
  have hKW : Integrable (fun x => w x * ‖K x‖) := by simpa [K] using hK
  have hQW : MemLp (fun x => w x * ‖Q x‖) 2 volume := by simpa [Q] using hQ
  have h := (ThetaSynthesisYoung.weighted_young hw hw0 hwsub hki hqi hKW hQW).1
  have he (x : ℝ) : conv K Q x = (absConv k q x : ℂ) := by
    change (∫ t : ℝ, (‖k t‖ : ℂ) * (‖q (x-t)‖ : ℂ)) = _
    simp only [← Complex.ofReal_mul]
    exact integral_complex_ofReal
  simpa only [he, Complex.norm_real, Real.norm_of_nonneg (absConv_nonneg k q _)] using h

theorem translate_weighted_memLp {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hwsub : ∀ x t, w x ≤ w t * w (x-t))
    {k : ℝ → ℂ} (hk : Continuous k)
    (hK : MemLp (fun x => w x * ‖k x‖) 2 volume) (y : ℝ) :
    MemLp (weighted w (fun x => k (x-y))) 2 volume := by
  have ht := (hK.comp_measurePreserving (measurePreserving_sub_right volume y)).const_mul (w y)
  apply weighted_memLp hw hw0 (hk.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  apply ht.mono' (hw.mul (hk.comp (continuous_id.sub continuous_const)).norm).aestronglyMeasurable
  filter_upwards with x
  change ‖w x * ‖k (x-y)‖‖ ≤ w y * (w (x-y) * ‖k (x-y)‖)
  rw [Real.norm_of_nonneg (mul_nonneg (hw0 _) (norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_right (hwsub x y) (norm_nonneg _)).trans_eq (by ring)

/-- A weighted L² convolution can be tested against a vector by Fubini even
when the quotient has no same-weight L¹ bound. The absolute convolution and
weighted Young supply the product-integrability estimate. -/
theorem convolution_pairing_zero {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hwsub : ∀ x t, w x ≤ w t * w (x-t))
    {k q : ℝ → ℂ} (hkc : Continuous k) (hk : Integrable k) (hq : Integrable q)
    (C : ℝ) (hkb : ∀ x, ‖k x‖ ≤ C)
    (hK : Integrable (fun x => w x * ‖k x‖))
    (hQ : MemLp (fun x => w x * ‖q x‖) 2 volume)
    (u : H)
    (hzero : ∀ y : ℝ, (∫ x : ℝ, star (u x) * (w x : ℂ) * k (x-y)) = 0) :
    (∫ x : ℝ, star (u x) * (w x : ℂ) * conv k q x) = 0 := by
  let F : ℝ × ℝ → ℂ := fun z =>
    (star (u z.1) * (w z.1 : ℂ)) * (q z.2 * k (z.1-z.2))
  have hFm : AEStronglyMeasurable F (volume.prod volume) := by
    exact ((Lp.aestronglyMeasurable u).star.comp_fst.mul
      ((Complex.continuous_ofReal.comp hw).comp continuous_fst).aestronglyMeasurable).mul
      (hq.aestronglyMeasurable.comp_snd.mul
        (hkc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)
  have hFx (x : ℝ) : Integrable (fun y => F (x,y)) := by
    have hi : Integrable (fun y : ℝ => q y * k (x-y)) := by
      apply (hq.norm.mul_const C).mono'
        (hq.aestronglyMeasurable.mul (hkc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      filter_upwards with y
      change ‖q y * k (x-y)‖ ≤ ‖q y‖ * C
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hkb (x-y)) (norm_nonneg _)
    exact hi.const_mul (star (u x) * (w x : ℂ))
  have hAbs := weighted_absConv_memLp hw hw0 hwsub hk hq hK hQ
  have hI : Integrable (fun x : ℝ => ‖u x‖ * (w x * absConv k q x)) :=
    (Lp.memLp u).norm.integrable_mul hAbs
  have hpoint (x : ℝ) : (∫ y : ℝ, ‖F (x,y)‖) = ‖u x‖ * (w x * absConv k q x) := by
    simp only [F, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (hw0 x)]
    rw [integral_const_mul]
    change (‖u x‖ * w x) * absConv q k x = _
    rw [absConv_comm q k]
    ring
  have hFi : Integrable F (volume.prod volume) :=
    (integrable_prod_iff hFm).mpr ⟨.of_forall hFx,
      hI.congr (.of_forall fun x => (hpoint x).symm)⟩
  have hswap := integral_integral_swap (f := fun x y => F (x,y)) hFi
  calc
    (∫ x : ℝ, star (u x) * (w x : ℂ) * conv k q x)
        = ∫ x : ℝ, ∫ y : ℝ, F (x,y) := by
          rw [conv_comm k q]
          apply integral_congr_ae
          filter_upwards with x
          exact (integral_const_mul (star (u x) * (w x : ℂ)) _).symm
    _ = ∫ y : ℝ, ∫ x : ℝ, F (x,y) := hswap
    _ = 0 := by
      have hy (y : ℝ) : (∫ x : ℝ, F (x,y)) = 0 := by
        calc
          _ = q y * (∫ x : ℝ, star (u x) * (w x : ℂ) * k (x-y)) := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with x
            dsimp [F]
            ring
          _ = 0 := by rw [hzero y, mul_zero]
      simp only [hy, integral_zero]

/-- The weighted pairing with an actual function agrees with the Hilbert-space
inner product of its `Lp` class. -/
theorem inner_weighted_toLp (w : ℝ → ℝ) (f : ℝ → ℂ)
    (hf : MemLp (weighted w f) 2 volume) (u : H) :
    inner ℂ u (hf.toLp (weighted w f)) =
      ∫ x : ℝ, star (u x) * (w x : ℂ) * f x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
  change weighted w f x * star (u x) = _
  dsimp [weighted]
  ring

/-- Fubini and Hilbert-space duality put the weighted convolution in the
closed span of the weighted translates. No weighted L¹ assumption on `q`
is needed. -/
theorem convolution_mem_closed_translate_span {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hwsub : ∀ x t, w x ≤ w t * w (x-t))
    {k q : ℝ → ℂ} (hkc : Continuous k) (hk : Integrable k) (hq : Integrable q)
    (C : ℝ) (hkb : ∀ x, ‖k x‖ ≤ C)
    (hK : Integrable (fun x => w x * ‖k x‖))
    (hK2 : MemLp (fun x => w x * ‖k x‖) 2 volume)
    (hQ : MemLp (fun x => w x * ‖q x‖) 2 volume)
    (hconv : MemLp (weighted w (conv k q)) 2 volume) :
    hconv.toLp (weighted w (conv k q)) ∈
      (Submodule.span ℂ (range fun y : ℝ =>
        (translate_weighted_memLp hw hw0 hwsub hkc hK2 y).toLp
          (weighted w (fun x => k (x-y))))).topologicalClosure := by
  let v (y : ℝ) : H := (translate_weighted_memLp hw hw0 hwsub hkc hK2 y).toLp
    (weighted w (fun x => k (x-y)))
  let S : Submodule ℂ H := Submodule.span ℂ (range v)
  change hconv.toLp (weighted w (conv k q)) ∈ S.topologicalClosure
  rw [← S.orthogonal_orthogonal_eq_closure]
  apply (S.orthogonal.mem_orthogonal _).mpr
  intro u hu
  rw [inner_weighted_toLp]
  apply convolution_pairing_zero hw hw0 hwsub hkc hk hq C hkb hK hQ u
  intro y
  have hv : v y ∈ S := Submodule.subset_span (mem_range_self y)
  have h := Submodule.inner_left_of_mem_orthogonal hv hu
  change inner ℂ u ((translate_weighted_memLp hw hw0 hwsub hkc hK2 y).toLp
    (weighted w (fun x => k (x-y)))) = 0 at h
  simpa only [inner_weighted_toLp] using h

theorem exists_fin_sum_of_mem_closure_span
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (v : ι → E) (f : E)
    (hf : f ∈ (Submodule.span ℂ (range v)).topologicalClosure)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (a : Fin m → ℂ) (y : Fin m → ι),
      ‖f - ∑ i : Fin m, a i • v (y i)‖ < ε := by
  classical
  obtain ⟨s, a, ha⟩ := exists_finite_sum_of_mem_closure_span v f hf ε hε
  let e := s.equivFin.symm
  refine ⟨s.card, fun i => a (e i), fun i => (e i : ι), ?_⟩
  have he : (∑ i : Fin s.card, a (e i) • v (e i)) = ∑ j ∈ s, a j • v j := by
    calc
      _ = ∑ j : s, a j • v j := e.sum_comp (fun j : s => a j • v j)
      _ = ∑ j ∈ s, a j • v j := Finset.sum_coe_sort s (fun j => a j • v j)
  rw [he]
  exact ha

theorem finite_weighted_sum_ae (w : ℝ → ℝ) (k : ℝ → ℂ) (v : ℝ → H)
    (hv : ∀ y : ℝ, v y =ᵐ[volume] weighted w (fun x => k (x-y)))
    {m : ℕ} (a : Fin m → ℂ) (y : Fin m → ℝ) :
    ⇑(∑ i : Fin m, a i • v (y i) : H) =ᵐ[volume]
      weighted w (fun x => ∑ i : Fin m, a i * k (x-y i)) := by
  have he : ∀ᵐ x : ℝ, ∀ i : Fin m,
      (a i • v (y i)) x = a i * weighted w (fun t => k (t-y i)) x := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (a i) (v (y i)), hv (y i)] with x hx hy
    simp only [hx, hy, Pi.smul_apply, smul_eq_mul]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • v (y i)), he]
    with x hx hi
  rw [hx]
  simp only [hi, weighted, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Closed-span membership yields an actual finite sum and a finite weighted
squared-error integral. The cardinality may be zero. -/
theorem finite_approximation_of_mem_closed_span (w : ℝ → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (k f : ℝ → ℂ) (hf : MemLp (weighted w f) 2 volume) (v : ℝ → H)
    (hv : ∀ y : ℝ, v y =ᵐ[volume] weighted w (fun x => k (x-y)))
    (hspan : hf.toLp (weighted w f) ∈
      (Submodule.span ℂ (range v)).topologicalClosure)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (a : Fin m → ℂ) (y : Fin m → ℝ),
      MemLp (fun x => w x * ‖f x - ∑ i : Fin m, a i * k (x-y i)‖) 2 volume ∧
      (∫ x : ℝ, (w x * ‖f x - ∑ i : Fin m, a i * k (x-y i)‖) ^ 2) < δ := by
  obtain ⟨m, a, y, ha⟩ := exists_fin_sum_of_mem_closure_span v
    (hf.toLp (weighted w f)) hspan (Real.sqrt δ) (Real.sqrt_pos.mpr hδ)
  let g : H := ∑ i : Fin m, a i • v (y i)
  let r : ℝ → ℂ := fun x => f x - ∑ i : Fin m, a i * k (x-y i)
  have hgae : g =ᵐ[volume] weighted w (fun x => ∑ i : Fin m, a i * k (x-y i)) :=
    finite_weighted_sum_ae w k v hv a y
  have hrae : (hf.toLp (weighted w f) - g) =ᵐ[volume] weighted w r := by
    filter_upwards [Lp.coeFn_sub (hf.toLp (weighted w f)) g, hf.coeFn_toLp, hgae]
      with x hx hfx hgx
    simp only [hx, hfx, hgx, Pi.sub_apply, weighted, r, mul_sub]
  have hr : MemLp (weighted w r) 2 volume :=
    MemLp.ae_eq hrae (Lp.memLp (hf.toLp (weighted w f) - g))
  have hrR : MemLp (fun x => w x * ‖r x‖) 2 volume := by
    simpa only [norm_weighted w hw0 r] using hr.norm
  refine ⟨m, a, y, hrR, ?_⟩
  have henergy : ‖hf.toLp (weighted w f) - g‖ ^ 2 =
      ∫ x : ℝ, (w x * ‖r x‖) ^ 2 := by
    rw [H_norm_sq]
    apply integral_congr_ae
    filter_upwards [hrae] with x hx
    rw [hx, norm_weighted w hw0 r x]
  change (∫ x : ℝ, (w x * ‖r x‖) ^ 2) < δ
  rw [← henergy]
  have hs := Real.sq_sqrt hδ.le
  have hn := norm_nonneg (hf.toLp (weighted w f) - g)
  have hp := Real.sqrt_nonneg δ
  change ‖hf.toLp (weighted w f) - g‖ < Real.sqrt δ at ha
  nlinarith

theorem convolution_finite_approximation {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hwsub : ∀ x t, w x ≤ w t * w (x-t))
    {k q : ℝ → ℂ} (hkc : Continuous k) (hk : Integrable k) (hq : Integrable q)
    (C : ℝ) (hkb : ∀ x, ‖k x‖ ≤ C)
    (hK : Integrable (fun x => w x * ‖k x‖))
    (hK2 : MemLp (fun x => w x * ‖k x‖) 2 volume)
    (hQ : MemLp (fun x => w x * ‖q x‖) 2 volume)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (a : Fin m → ℂ) (y : Fin m → ℝ),
      MemLp (fun x => w x * ‖conv k q x - ∑ i : Fin m, a i * k (x-y i)‖) 2 volume ∧
      (∫ x : ℝ, (w x * ‖conv k q x - ∑ i : Fin m, a i * k (x-y i)‖) ^ 2) < δ := by
  have hconvR := (ThetaSynthesisYoung.weighted_young hw hw0 hwsub hk hq hK hQ).1
  have hconv := weighted_memLp hw hw0
    (hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hq).aestronglyMeasurable hconvR
  have hspan := convolution_mem_closed_translate_span hw hw0 hwsub hkc hk hq C hkb hK hK2 hQ hconv
  apply finite_approximation_of_mem_closed_span w hw0 k (conv k q) hconv _ _ hspan δ hδ
  intro y
  exact MemLp.coeFn_toLp _

end
end MasulloRH.ThetaSynthesisFinite


-- Local component: ThetaSynthesisAssembly
/-!
The functional-analysis assembly step for theta synthesis: a strong limit of
weighted L² convolutions by a fixed generator lies in its closed translate span.
The conclusion is stated using actual finite sums and a finite error integral.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace MasulloRH.ThetaSynthesisAssembly
noncomputable section
open ThetaSynthesisFinite
open ThetaSynthesisYoung (conv)

theorem finite_approximation_of_convolution_limits {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : ∀ x, 0 ≤ w x) (hwsub : ∀ x t, w x ≤ w t * w (x-t))
    {k : ℝ → ℂ} (hkc : Continuous k) (hk : Integrable k)
    (C : ℝ) (hkb : ∀ x, ‖k x‖ ≤ C)
    (hK : Integrable (fun x => w x * ‖k x‖))
    (hK2 : MemLp (fun x => w x * ‖k x‖) 2 volume)
    (f : ℝ → ℂ) (hfm : AEStronglyMeasurable f volume)
    (hF : MemLp (fun x => w x * ‖f x‖) 2 volume)
    (P : ℝ → ℝ → ℂ)
    (hlimit : Tendsto (fun ε : ℝ => ∫ x : ℝ, (w x * ‖P ε x - f x‖)^2)
      (𝓝[>] 0) (𝓝 0))
    (hfactor : ∀ ε : ℝ, 0 < ε → ∃ q : ℝ → ℂ, Integrable q ∧
      MemLp (fun x => w x * ‖q x‖) 2 volume ∧ P ε = conv k q)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (a : Fin m → ℂ) (y : Fin m → ℝ),
      MemLp (fun x => w x * ‖f x - ∑ i : Fin m, a i * k (x-y i)‖) 2 volume ∧
      (∫ x : ℝ, (w x * ‖f x - ∑ i : Fin m, a i * k (x-y i)‖)^2) < δ := by
  have hf := weighted_memLp hw hw0 hfm hF
  let F : H := hf.toLp (weighted w f)
  let v (y : ℝ) : H := (translate_weighted_memLp hw hw0 hwsub hkc hK2 y).toLp
    (weighted w (fun x => k (x-y)))
  let S : Submodule ℂ H := (Submodule.span ℂ (range v)).topologicalClosure
  have hclosed : IsClosed (S : Set H) :=
    (Submodule.span ℂ (range v)).isClosed_topologicalClosure
  have hspan : F ∈ S := by
    have hcl : F ∈ closure (S : Set H) := by
      apply Metric.mem_closure_iff.mpr
      intro η hη
      have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
          (∫ x : ℝ, (w x * ‖P ε x-f x‖)^2) < η^2 :=
        hlimit.eventually (eventually_lt_nhds (sq_pos_of_pos hη))
      have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
      obtain ⟨ε, he, hε⟩ := (hsmall.and hpos).exists
      obtain ⟨q, hq, hQ, hP⟩ := hfactor ε hε
      have hgR := (ThetaSynthesisYoung.weighted_young hw hw0 hwsub hk hq hK hQ).1
      have hg := weighted_memLp hw hw0
        (hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hq).aestronglyMeasurable hgR
      let G : H := hg.toLp (weighted w (conv k q))
      have hGS : G ∈ S :=
        convolution_mem_closed_translate_span hw hw0 hwsub hkc hk hq C hkb hK hK2 hQ hg
      refine ⟨G, hGS, ?_⟩
      have hd : dist F G ^ 2 = ∫ x : ℝ, (w x * ‖conv k q x-f x‖)^2 :=
        weighted_toLp_dist_sq hw0 hf hg
      rw [hP] at he
      rw [← hd] at he
      have hn := dist_nonneg (x := F) (y := G)
      nlinarith
    change F ∈ (S : Set H)
    simpa only [hclosed.closure_eq] using hcl
  apply finite_approximation_of_mem_closed_span w hw0 k f hf v _ hspan δ hδ
  intro y
  exact MemLp.coeFn_toLp _

end
end MasulloRH.ThetaSynthesisAssembly


-- Local component: ThetaSynthesisApproxIdentity
open MeasureTheory Filter Set
open scoped Topology Convolution

namespace MasulloRH.ThetaSynthesisAI

noncomputable section

def energy (w : ℝ → ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, (w x * ‖f x‖)^2

def translate (f : ℝ → ℂ) (t : ℝ) : ℝ → ℂ := fun x => f (x-t)

def dilate (k : ℝ → ℂ) (ε : ℝ) : ℝ → ℂ :=
  fun x => ((ε⁻¹ : ℝ) : ℂ) * k (ε⁻¹*x)

private theorem norm_sq_L2 (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖g‖^2 = ∫ x : ℝ, ‖g x‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner g g)]
  apply integral_congr_ae
  exact .of_forall fun x => by simp [← Complex.ofReal_pow]

theorem integral_sq_norm_eq_toLp (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    (∫ x : ℝ, ‖f x‖^2) = ‖hf.toLp f‖^2 := by
  rw [norm_sq_L2]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

private def shiftMap (t : ℝ) : C(ℝ, ℝ) := ⟨fun x => x-t, by fun_prop⟩

private theorem shiftMap_preserving (t : ℝ) :
    MeasurePreserving (shiftMap t) (volume : Measure ℝ) volume := by
  simpa only [shiftMap, ContinuousMap.coe_mk, sub_eq_add_neg] using
    measurePreserving_add_right (volume : Measure ℝ) (-t)

private theorem shiftMap_continuous : Continuous shiftMap := by
  exact (ContinuousMap.mk (fun z : ℝ × ℝ => z.2-z.1) (by fun_prop)).curry.continuous

private def lpShift (g : Lp ℂ 2 (volume : Measure ℝ)) (t : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (shiftMap t) (shiftMap_preserving t) g

private theorem lpShift_continuous (g : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous (lpShift g) := by
  exact continuous_const.compMeasurePreservingLp shiftMap_continuous shiftMap_preserving
    (by norm_num)

private theorem lpShift_zero (g : Lp ℂ 2 (volume : Measure ℝ)) : lpShift g 0 = g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving g (shiftMap_preserving 0)] with x hx
  simpa [lpShift, shiftMap] using hx

theorem translation_energy_unweighted_tendsto (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, ‖f (x-t)-f x‖^2) (𝓝 0) (𝓝 0) := by
  let g := hf.toLp f
  have he (t : ℝ) : (∫ x : ℝ, ‖f (x-t)-f x‖^2) = ‖lpShift g t-g‖^2 := by
    rw [norm_sq_L2]
    apply integral_congr_ae
    have hcomp := (shiftMap_preserving t).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp
    filter_upwards [Lp.coeFn_sub (lpShift g t) g,
      Lp.coeFn_compMeasurePreserving g (shiftMap_preserving t), hf.coeFn_toLp,
      hcomp] with x hsub hshift hf₀ hf₁
    dsimp [g, shiftMap, lpShift] at *
    rw [hsub, hshift, hf₀, hf₁]
  simp_rw [he]
  have hc : Continuous (fun t : ℝ => ‖lpShift g t-g‖^2) :=
    ((lpShift_continuous g).sub (continuous_const : Continuous (fun _ : ℝ => g))).norm.pow 2
  simpa [lpShift_zero] using hc.tendsto 0

theorem weighted_translate_memLp (w : ℝ → ℝ) (hw : Continuous w)
    (hw1 : ∀ x, 1 ≤ w x) (hwsub : ∀ x t, w x ≤ w t*w (x-t))
    (f : ℝ → ℂ) (hm : Measurable f)
    (hf : MemLp (fun x => w x*‖f x‖) 2 volume) (t : ℝ) :
    MemLp (fun x => w x*‖f (x-t)‖) 2 volume := by
  have hn x : 0 ≤ w x := (by norm_num : (0:ℝ) ≤ 1).trans (hw1 x)
  have htr := (hf.comp_measurePreserving (shiftMap_preserving t)).const_mul (w t)
  apply htr.mono' ((hw.measurable.mul ((hm.comp (by fun_prop :
    Measurable fun x : ℝ => x-t)).norm)).aestronglyMeasurable)
  filter_upwards with x
  change ‖w x*‖f (x-t)‖‖ ≤ w t*(w (x-t)*‖f (x-t)‖)
  rw [Real.norm_of_nonneg (mul_nonneg (hn _) (norm_nonneg _))]
  nlinarith only [mul_le_mul_of_nonneg_right (hwsub x t) (norm_nonneg (f (x-t)))]

theorem weighted_translate_sub_memLp (w : ℝ → ℝ) (hw : Continuous w)
    (hw1 : ∀ x, 1 ≤ w x) (hwsub : ∀ x t, w x ≤ w t*w (x-t))
    (f : ℝ → ℂ) (hm : Measurable f)
    (hf : MemLp (fun x => w x*‖f x‖) 2 volume) (t : ℝ) :
    MemLp (fun x => w x*‖f (x-t)-f x‖) 2 volume := by
  have hn x : 0 ≤ w x := (by norm_num : (0:ℝ) ≤ 1).trans (hw1 x)
  have htr := weighted_translate_memLp w hw hw1 hwsub f hm hf t
  apply (htr.add hf).mono' ((hw.measurable.mul
    (((hm.comp (by fun_prop : Measurable fun x : ℝ => x-t)).sub hm).norm)).aestronglyMeasurable)
  filter_upwards with x
  change ‖w x*‖f (x-t)-f x‖‖ ≤ w x*‖f (x-t)‖+w x*‖f x‖
  rw [Real.norm_of_nonneg (mul_nonneg (hn _) (norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (hn _)).trans_eq (by ring)

theorem weight_difference_bound (w : ℝ → ℝ) (hw1 : ∀ x, 1 ≤ w x)
    (hwneg : ∀ x, w (-x)=w x) (hwsub : ∀ x t, w x ≤ w t*w (x-t)) (x t : ℝ) :
    |w x-w (x-t)| ≤ (w t-1)*w (x-t) := by
  have ha : 0 < w x := lt_of_lt_of_le zero_lt_one (hw1 x)
  have hb : 0 < w (x-t) := lt_of_lt_of_le zero_lt_one (hw1 (x-t))
  have hc : 0 < w t := lt_of_lt_of_le zero_lt_one (hw1 t)
  have hupper : w x/w (x-t) ≤ w t := (div_le_iff₀ hb).mpr (by simpa [mul_comm] using hwsub x t)
  have hback : w (x-t) ≤ w t*w x := by
    simpa [hwneg, sub_neg_eq_add] using hwsub (x-t) (-t)
  have hlower : (w t)⁻¹ ≤ w x/w (x-t) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hc hb]
    nlinarith only [hback]
  have hrec : 2-w t ≤ (w t)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hc]
    nlinarith [sq_nonneg (w t-1)]
  have hr : |w x/w (x-t)-1| ≤ w t-1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : w x-w (x-t) = (w x/w (x-t)-1)*w (x-t) := by field_simp
  rw [he, abs_mul, abs_of_pos hb]
  exact mul_le_mul_of_nonneg_right hr hb.le


theorem weighted_translation_energy_bound (w : ℝ → ℝ) (hw : Continuous w)
    (hw1 : ∀ x, 1 ≤ w x) (hwsub : ∀ x t, w x ≤ w t*w (x-t))
    (f : ℝ → ℂ) (hm : Measurable f)
    (hf : MemLp (fun x => w x*‖f x‖) 2 volume) (t : ℝ) :
    energy w (fun x => f (x-t)-f x) ≤ 2*((w t)^2+1)*energy w f := by
  have hn x : 0 ≤ w x := (by norm_num : (0:ℝ) ≤ 1).trans (hw1 x)
  have hsq : Integrable (fun x => (w x*‖f x‖)^2) :=
    (memLp_two_iff_integrable_sq hf.1).mp hf
  have hsub := weighted_translate_sub_memLp w hw hw1 hwsub f hm hf t
  have hsubsq := (memLp_two_iff_integrable_sq hsub.1).mp hsub
  have hmajor : Integrable (fun x => 2*((w t)^2*(w (x-t)*‖f (x-t)‖)^2+(w x*‖f x‖)^2)) :=
    (((hsq.comp_sub_right t).const_mul ((w t)^2)).add hsq).const_mul 2
  calc
    _ ≤ ∫ x : ℝ, 2*((w t)^2*(w (x-t)*‖f (x-t)‖)^2+(w x*‖f x‖)^2) := by
      apply integral_mono hsubsq hmajor
      intro x
      have htri := mul_le_mul_of_nonneg_left (norm_sub_le (f (x-t)) (f x)) (hn x)
      have hweight := mul_le_mul_of_nonneg_right (hwsub x t) (norm_nonneg (f (x-t)))
      have hnon : 0 ≤ w x*‖f (x-t)-f x‖ := mul_nonneg (hn _) (norm_nonneg _)
      have hsum : 0 ≤ w t*(w (x-t)*‖f (x-t)‖)+w x*‖f x‖ :=
        add_nonneg (mul_nonneg (hn _) (mul_nonneg (hn _) (norm_nonneg _)))
          (mul_nonneg (hn _) (norm_nonneg _))
      have hle : w x*‖f (x-t)-f x‖ ≤ w t*(w (x-t)*‖f (x-t)‖)+w x*‖f x‖ := by nlinarith
      have hs := (sq_le_sq₀ hnon hsum).mpr hle
      nlinarith [sq_nonneg (w t*(w (x-t)*‖f (x-t)‖)-w x*‖f x‖)]
    _ = _ := by
      rw [integral_const_mul, integral_add ((hsq.comp_sub_right t).const_mul ((w t)^2)) hsq,
        integral_const_mul, integral_sub_right_eq_self (fun x : ℝ => (w x*‖f x‖)^2) t]
      unfold energy
      ring

theorem weighted_translation_energy_tendsto (w : ℝ → ℝ) (hw : Continuous w)
    (hw1 : ∀ x, 1 ≤ w x) (hwzero : w 0=1)
    (hwneg : ∀ x, w (-x)=w x) (hwsub : ∀ x t, w x ≤ w t*w (x-t))
    (f : ℝ → ℂ) (hm : Measurable f)
    (hf : MemLp (fun x => w x*‖f x‖) 2 volume) :
    Tendsto (fun t : ℝ => energy w (fun x => f (x-t)-f x)) (𝓝 0) (𝓝 0) := by
  have hn x : 0 ≤ w x := (by norm_num : (0:ℝ) ≤ 1).trans (hw1 x)
  let F : ℝ → ℂ := fun x => (w x : ℂ)*f x
  have hFm : Measurable F := by dsimp [F]; fun_prop
  have hFn x : ‖F x‖=w x*‖f x‖ := by simp [F,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hn x)]
  have hF : MemLp F 2 volume := hf.congr_norm hFm.aestronglyMeasurable
    (.of_forall fun x => by rw [hFn,Real.norm_of_nonneg (mul_nonneg (hn _) (norm_nonneg _))])
  have hFsq : Integrable (fun x => ‖F x‖^2) :=
    (memLp_two_iff_integrable_sq_norm hF.1).mp hF
  have hupper (t : ℝ) : energy w (fun x => f (x-t)-f x) ≤
      2*(∫ x : ℝ, ‖F (x-t)-F x‖^2)+2*(w t-1)^2*(∫ x : ℝ, ‖F x‖^2) := by
    have hsub := weighted_translate_sub_memLp w hw hw1 hwsub f hm hf t
    have hsubsq := (memLp_two_iff_integrable_sq hsub.1).mp hsub
    have hFd : MemLp (fun x => F (x-t)-F x) 2 volume :=
      (hF.comp_measurePreserving (shiftMap_preserving t)).sub hF
    have hFdsq := (memLp_two_iff_integrable_sq_norm hFd.1).mp hFd
    have hmajor : Integrable (fun x => 2*‖F (x-t)-F x‖^2+2*(w t-1)^2*‖F (x-t)‖^2) :=
      (hFdsq.const_mul 2).add ((hFsq.comp_sub_right t).const_mul (2*(w t-1)^2))
    calc
      _ ≤ ∫ x : ℝ, 2*‖F (x-t)-F x‖^2+2*(w t-1)^2*‖F (x-t)‖^2 := by
        apply integral_mono hsubsq hmajor
        intro x
        have hid : (w x : ℂ)*(f (x-t)-f x) =
            (F (x-t)-F x)+((w x-w (x-t) : ℝ) : ℂ)*f (x-t) := by dsimp [F]; push_cast; ring
        have hnorm := norm_add_le (F (x-t)-F x) (((w x-w (x-t) : ℝ) : ℂ)*f (x-t))
        rw [← hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hn x), norm_mul,
          Complex.norm_real, Real.norm_eq_abs] at hnorm
        have hwbd := mul_le_mul_of_nonneg_right (weight_difference_bound w hw1 hwneg hwsub x t)
          (norm_nonneg (f (x-t)))
        have ht : 0 ≤ w t-1 := sub_nonneg.mpr (hw1 t)
        have hle : w x*‖f (x-t)-f x‖ ≤ ‖F (x-t)-F x‖+(w t-1)*‖F (x-t)‖ := by
          rw [hFn]
          nlinarith only [hnorm,hwbd]
        have hs := (sq_le_sq₀ (mul_nonneg (hn _) (norm_nonneg _))
          (add_nonneg (norm_nonneg _) (mul_nonneg ht (norm_nonneg _)))).mpr hle
        nlinarith [sq_nonneg (‖F (x-t)-F x‖-(w t-1)*‖F (x-t)‖)]
      _ = _ := by
        rw [integral_add (hFdsq.const_mul 2) ((hFsq.comp_sub_right t).const_mul (2*(w t-1)^2)),
          integral_const_mul, integral_const_mul, integral_sub_right_eq_self (fun x : ℝ => ‖F x‖^2) t]
  have hlimit : Tendsto (fun t : ℝ => 2*(∫ x : ℝ, ‖F (x-t)-F x‖^2)+
      2*(w t-1)^2*(∫ x : ℝ, ‖F x‖^2)) (𝓝 0) (𝓝 0) := by
    have ht := (translation_energy_unweighted_tendsto F hF).const_mul 2
    have hwlim := (((hw.tendsto 0).sub_const 1).pow 2).const_mul 2
    convert ht.add (hwlim.mul_const (∫ x : ℝ, ‖F x‖^2)) using 1 <;> simp [hwzero]
  exact squeeze_zero (fun t => integral_nonneg (fun x => sq_nonneg _)) hupper hlimit


theorem translation_energy_measurable (w : ℝ → ℝ) (hw : Continuous w)
    (f : ℝ → ℂ) (hm : Measurable f) :
    Measurable (fun t : ℝ => energy w (fun x => f (x-t)-f x)) := by
  have hj : StronglyMeasurable (fun z : ℝ × ℝ => (w z.2*‖f (z.2-z.1)-f z.2‖)^2) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  exact hj.integral_prod_right'.measurable

theorem scaled_translation_energy_bound (w : ℝ → ℝ) (hw : Continuous w)
    (hw1 : ∀ x, 1 ≤ w x) (hwsub : ∀ x t, w x ≤ w t*w (x-t))
    (f : ℝ → ℂ) (hm : Measurable f)
    (hf : MemLp (fun x => w x*‖f x‖) 2 volume)
    (ε t : ℝ) (hscale : w (ε*t) ≤ w t) :
    energy w (fun x => f (x-ε*t)-f x) ≤ 4*(w t)^2*energy w f := by
  have hn x : 0 ≤ w x := (by norm_num : (0:ℝ) ≤ 1).trans (hw1 x)
  have hE : 0 ≤ energy w f := integral_nonneg (fun x => sq_nonneg _)
  have hs : (w (ε*t))^2 ≤ (w t)^2 := (sq_le_sq₀ (hn _) (hn _)).mpr hscale
  have ho : 1 ≤ (w t)^2 := by nlinarith [hw1 t]
  exact (weighted_translation_energy_bound w hw hw1 hwsub f hm hf (ε*t)).trans
    (mul_le_mul_of_nonneg_right (by nlinarith only [hs,ho]) hE)

private def differenceSquare (w : ℝ → ℝ) (f : ℝ → ℂ) (ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  (w z.2*‖f (z.2-ε*z.1)-f z.2‖)^2

private theorem weighted_difference_joint_integrable (w : ℝ → ℝ) (hw : Continuous w)
    (hw1 : ∀ x, 1 ≤ w x) (hwsub : ∀ x t, w x ≤ w t*w (x-t))
    (k f : ℝ → ℂ) (hkm : Measurable k) (hm : Measurable f)
    (hf : MemLp (fun x => w x*‖f x‖) 2 volume)
    (hK : Integrable (fun t => (w t)^2*‖k t‖))
    (ε : ℝ) (hscale : ∀ t, w (ε*t) ≤ w t) :
    Integrable (fun z : ℝ × ℝ => ‖k z.1‖*differenceSquare w f ε z) (volume.prod volume) := by
  have hJm : StronglyMeasurable (fun z : ℝ × ℝ => ‖k z.1‖*differenceSquare w f ε z) := by
    apply Measurable.stronglyMeasurable
    unfold differenceSquare
    fun_prop
  have hJn z : 0 ≤ ‖k z.1‖*differenceSquare w f ε z := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hE : 0 ≤ energy w f := integral_nonneg (fun x => sq_nonneg _)
  have houter : Integrable (fun t : ℝ => ‖k t‖*energy w (fun x => f (x-ε*t)-f x)) := by
    apply (hK.const_mul (4*energy w f)).mono'
      ((hkm.norm.mul ((translation_energy_measurable w hw f hm).comp (by fun_prop :
        Measurable (fun t : ℝ => ε*t)))).aestronglyMeasurable)
    filter_upwards with t
    change ‖‖k t‖*energy w (fun x => f (x-ε*t)-f x)‖ ≤ 4*energy w f*((w t)^2*‖k t‖)
    have hnon : 0 ≤ energy w (fun x => f (x-ε*t)-f x) := integral_nonneg (fun x => sq_nonneg _)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hnon)]
    exact (mul_le_mul_of_nonneg_left
      (scaled_translation_energy_bound w hw hw1 hwsub f hm hf ε t (hscale t)) (norm_nonneg _)).trans_eq (by ring)
  apply (integrable_prod_iff hJm.aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun t => ?_), ?_⟩
  · have hsub := weighted_translate_sub_memLp w hw hw1 hwsub f hm hf (ε*t)
    exact ((memLp_two_iff_integrable_sq hsub.1).mp hsub).const_mul ‖k t‖
  · apply houter.congr
    filter_upwards with t
    change ‖k t‖*(∫ x : ℝ, (w x*‖f (x-ε*t)-f x‖)^2) =
      (∫ x : ℝ, ‖‖k t‖*(w x*‖f (x-ε*t)-f x‖)^2‖)
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun x => (Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))).symm

private def averagedDifference (k f : ℝ → ℂ) (ε x : ℝ) : ℂ :=
  ∫ t : ℝ, k t*(f (x-ε*t)-f x)

private theorem averaged_difference_measurable (k f : ℝ → ℂ)
    (hkm : Measurable k) (hm : Measurable f) (ε : ℝ) :
    Measurable (averagedDifference k f ε) := by
  have hj : StronglyMeasurable (fun z : ℝ × ℝ => k z.2*(f (z.1-ε*z.2)-f z.1)) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  exact hj.integral_prod_right'.measurable

private theorem averaged_difference_energy_bound (w : ℝ → ℝ) (hw : Continuous w)
    (hw1 : ∀ x, 1 ≤ w x) (hwsub : ∀ x t, w x ≤ w t*w (x-t))
    (k f : ℝ → ℂ) (hkm : Measurable k) (hk : Integrable k) (hm : Measurable f)
    (hf : MemLp (fun x => w x*‖f x‖) 2 volume)
    (hK : Integrable (fun t => (w t)^2*‖k t‖))
    (ε : ℝ) (hscale : ∀ t, w (ε*t) ≤ w t) :
    (∀ᵐ x : ℝ, Integrable (fun t : ℝ => k t*(f (x-ε*t)-f x))) ∧
    MemLp (fun x => w x*‖averagedDifference k f ε x‖) 2 volume ∧
    energy w (averagedDifference k f ε) ≤
      (∫ t : ℝ, ‖k t‖)*(∫ t : ℝ, ‖k t‖*energy w (fun x => f (x-ε*t)-f x)) := by
  have hn x : 0 ≤ w x := (by norm_num : (0:ℝ) ≤ 1).trans (hw1 x)
  let J : ℝ × ℝ → ℝ := fun z => ‖k z.1‖*differenceSquare w f ε z
  have hJ : Integrable J (volume.prod volume) :=
    weighted_difference_joint_integrable w hw hw1 hwsub k f hkm hm hf hK ε hscale
  let A := ∫ t : ℝ, ‖k t‖
  let B : ℝ → ℝ := fun x => ∫ t : ℝ, J (t,x)
  have hB : Integrable B := hJ.integral_prod_right
  have hmain : ∀ᵐ x : ℝ, Integrable (fun t : ℝ => k t*(f (x-ε*t)-f x)) ∧
      (w x*‖averagedDifference k f ε x‖)^2 ≤ A*B x := by
    filter_upwards [hJ.prod_left_ae] with x hx
    have hmV : AEStronglyMeasurable (fun t : ℝ => w x*‖f (x-ε*t)-f x‖) := by
      apply Measurable.aestronglyMeasurable
      fun_prop
    obtain ⟨hI,hC⟩ := ThetaSynthesisYoung.weighted_cauchy (fun t => ‖k t‖)
      (fun t => w x*‖f (x-ε*t)-f x‖) (fun t => norm_nonneg _)
      (fun t => mul_nonneg (hn _) (norm_nonneg _)) hk.norm hmV hx
    have hdiff : Integrable (fun t : ℝ => k t*(f (x-ε*t)-f x)) := by
      apply hI.mono'
        ((hkm.mul ((hm.comp (by fun_prop : Measurable (fun t : ℝ => x-ε*t))).sub measurable_const)).aestronglyMeasurable)
      filter_upwards with t
      change ‖k t*(f (x-ε*t)-f x)‖ ≤ ‖k t‖*(w x*‖f (x-ε*t)-f x‖)
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (norm_nonneg _) (hw1 x)) (norm_nonneg _))
    refine ⟨hdiff, ?_⟩
    have hb : w x*‖averagedDifference k f ε x‖ ≤ ∫ t : ℝ, ‖k t‖*(w x*‖f (x-ε*t)-f x‖) := by
      calc
        _ ≤ w x*(∫ t : ℝ, ‖k t*(f (x-ε*t)-f x)‖) :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (hn _)
        _ = _ := by rw [← integral_const_mul]; congr 1; ext t; rw [norm_mul]; ring
    exact ((sq_le_sq₀ (mul_nonneg (hn _) (norm_nonneg _))
      (integral_nonneg (fun t => mul_nonneg (norm_nonneg _) (mul_nonneg (hn _) (norm_nonneg _))))).mpr hb).trans hC
  have hGm : AEStronglyMeasurable (fun x => w x*‖averagedDifference k f ε x‖) :=
    (hw.measurable.mul (averaged_difference_measurable k f hkm hm ε).norm).aestronglyMeasurable
  have hGs : Integrable (fun x => (w x*‖averagedDifference k f ε x‖)^2) := by
    apply (hB.const_mul A).mono' (hGm.pow 2)
    filter_upwards [hmain] with x hx
    change ‖(w x*‖averagedDifference k f ε x‖)^2‖ ≤ A*B x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hx.2
  refine ⟨hmain.mono (fun x hx => hx.1), (memLp_two_iff_integrable_sq hGm).mpr hGs,
    (integral_mono_ae hGs (hB.const_mul A) (hmain.mono (fun x hx => hx.2))).trans_eq ?_⟩
  rw [integral_const_mul]
  congr 1
  change (∫ x : ℝ, ∫ t : ℝ, J (t,x)) = _
  rw [← integral_integral_swap hJ]
  apply integral_congr_ae
  filter_upwards with t
  change (∫ x : ℝ, ‖k t‖*(w x*‖f (x-ε*t)-f x‖)^2) =
    ‖k t‖*(∫ x : ℝ, (w x*‖f (x-ε*t)-f x‖)^2)
  exact integral_const_mul _ _


private theorem integral_dilate (k : ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t : ℝ, dilate k ε t) = ∫ t : ℝ, k t := by
  unfold dilate
  rw [integral_const_mul, Measure.integral_comp_inv_mul_left k ε, Complex.real_smul, abs_of_pos hε,
    ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hε.ne', Complex.ofReal_one, one_mul]

theorem dilated_convolution_eq (k f : ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (dilate k ε ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x =
      ∫ t : ℝ, k t*f (x-ε*t) := by
  rw [← integral_dilate (fun t => k t*f (x-ε*t)) hε]
  apply integral_congr_ae
  filter_upwards with t
  change ((ε⁻¹ : ℝ) : ℂ)*k (ε⁻¹*t)*f (x-t) =
    ((ε⁻¹ : ℝ) : ℂ)*(k (ε⁻¹*t)*f (x-ε*(ε⁻¹*t)))
  have hh : ε*(ε⁻¹*t)=t := by field_simp
  rw [hh,mul_assoc]

private theorem averaged_difference_eq_convolution_sub (k f : ℝ → ℂ)
    (hk : Integrable k) (hunit : (∫ t : ℝ, k t)=1)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ)
    (hdiff : Integrable (fun t : ℝ => k t*(f (x-ε*t)-f x))) :
    averagedDifference k f ε x = (dilate k ε ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x-f x := by
  have hconst : Integrable (fun t : ℝ => k t*f x) := hk.mul_const _
  have hfirst : Integrable (fun t : ℝ => k t*f (x-ε*t)) := by
    apply (hdiff.add hconst).congr
    filter_upwards with t
    change k t*(f (x-ε*t)-f x)+k t*f x = k t*f (x-ε*t)
    ring
  rw [dilated_convolution_eq k f hε x]
  calc
    _ = ∫ t : ℝ, k t*f (x-ε*t)-k t*f x := by
      apply integral_congr_ae
      exact .of_forall fun t => by ring
    _ = (∫ t : ℝ, k t*f (x-ε*t))-(∫ t : ℝ, k t*f x) := integral_sub hfirst hconst
    _ = _ := by rw [integral_mul_const,hunit,one_mul]

/-- Weighted square-integrability is preserved by sufficiently small positive kernel dilations. -/
theorem weighted_approximate_identity_memLp (w : ℝ → ℝ) (hw : Continuous w)
    (hw1 : ∀ x, 1 ≤ w x) (hwsub : ∀ x t, w x ≤ w t*w (x-t))
    (k f : ℝ → ℂ) (hkm : Measurable k) (hk : Integrable k)
    (hunit : (∫ t : ℝ, k t)=1) (hm : Measurable f)
    (hf : MemLp (fun x => w x*‖f x‖) 2 volume)
    (hK : Integrable (fun t => (w t)^2*‖k t‖))
    (ε : ℝ) (hε : 0 < ε) (hscale : ∀ t, w (ε*t) ≤ w t) :
    MemLp (fun x => w x*‖(dilate k ε ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x-f x‖) 2 volume := by
  obtain ⟨hae,hmem,hbound⟩ :=
    averaged_difference_energy_bound w hw hw1 hwsub k f hkm hk hm hf hK ε hscale
  refine (memLp_congr_ae ?_).mp hmem
  filter_upwards [hae] with x hx
  rw [averaged_difference_eq_convolution_sub k f hk hunit hε x hx]

/-- A normalized kernel with an absolute squared-weight moment is a strong approximate
identity in the weighted L² norm. The kernel may be complex and need not be positive. -/
theorem weighted_approximate_identity_tendsto (w : ℝ → ℝ) (hw : Continuous w)
    (hw1 : ∀ x, 1 ≤ w x) (hwzero : w 0=1)
    (hwneg : ∀ x, w (-x)=w x) (hwsub : ∀ x t, w x ≤ w t*w (x-t))
    (hwdilate : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, w (ε*t) ≤ w t)
    (k f : ℝ → ℂ) (hkm : Measurable k) (hk : Integrable k)
    (hunit : (∫ t : ℝ, k t)=1) (hm : Measurable f)
    (hf : MemLp (fun x => w x*‖f x‖) 2 volume)
    (hK : Integrable (fun t => (w t)^2*‖k t‖)) :
    Tendsto (fun ε : ℝ => energy w (fun x =>
      (dilate k ε ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x-f x)) (𝓝[>] 0) (𝓝 0) := by
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε ∧ ε ≤ 1 :=
    hpos.and ((eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds)
  have hscalar : Tendsto (fun ε : ℝ => ∫ t : ℝ, ‖k t‖*energy w (fun x => f (x-ε*t)-f x))
      (𝓝[>] 0) (𝓝 0) := by
    have hmE := translation_energy_measurable w hw f hm
    have hmAll (ε : ℝ) : AEStronglyMeasurable
        (fun t : ℝ => ‖k t‖*energy w (fun x => f (x-ε*t)-f x)) :=
      (hkm.norm.mul (hmE.comp (by fun_prop : Measurable (fun t : ℝ => ε*t)))).aestronglyMeasurable
    have hdom : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), ∀ᵐ t : ℝ,
        ‖‖k t‖*energy w (fun x => f (x-ε*t)-f x)‖ ≤ 4*energy w f*((w t)^2*‖k t‖) := by
      filter_upwards [heps] with ε hε
      filter_upwards with t
      have hnon : 0 ≤ energy w (fun x => f (x-ε*t)-f x) := integral_nonneg (fun x => sq_nonneg _)
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hnon)]
      exact (mul_le_mul_of_nonneg_left
        (scaled_translation_energy_bound w hw hw1 hwsub f hm hf ε t (hwdilate ε hε.1 hε.2 t))
        (norm_nonneg _)).trans_eq (by ring)
    have hpoint : ∀ᵐ t : ℝ, Tendsto (fun ε : ℝ => ‖k t‖*energy w (fun x => f (x-ε*t)-f x))
        (𝓝[>] (0:ℝ)) (𝓝 ((fun _ : ℝ => (0:ℝ)) t)) := by
      filter_upwards with t
      have ht : Tendsto (fun ε : ℝ => ε*t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        simpa using ((continuous_id.mul_const t).tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using ((weighted_translation_energy_tendsto w hw hw1 hwzero hwneg hwsub f hm hf).comp ht).const_mul ‖k t‖
    simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => 4*energy w f*((w t)^2*‖k t‖)) (.of_forall hmAll) hdom
      (hK.const_mul (4*energy w f)) hpoint
  have hupper : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      energy w (fun x => (dilate k ε ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x-f x) ≤
        (∫ t : ℝ, ‖k t‖)*(∫ t : ℝ, ‖k t‖*energy w (fun x => f (x-ε*t)-f x)) := by
    filter_upwards [heps] with ε hε
    obtain ⟨hae,hmem,hbound⟩ := averaged_difference_energy_bound w hw hw1 hwsub k f
      hkm hk hm hf hK ε (hwdilate ε hε.1 hε.2)
    convert hbound using 1
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [averaged_difference_eq_convolution_sub k f hk hunit hε.1 x hx]
  exact squeeze_zero' (.of_forall fun ε => integral_nonneg (fun x => sq_nonneg _)) hupper
    (by simpa using hscalar.const_mul (∫ t : ℝ, ‖k t‖))


end
end MasulloRH.ThetaSynthesisAI


-- Local component: ThetaSynthesisKernelFacts
/-!
# Analytic facts for the literal dyadic theta seed and quartic kernel

The internal theta/Poisson/contour/damping proofs below are a minimal extraction
from the accepted proof of `MasulloRH.generic_strip_dyadic_theta_division`,
theorem 24df0c86-b075-4107-9103-8fc580dde151, accepted solution
0ab415f7-6816-4b40-b9ec-50067de21560 (2026-11-21).
Original source SHA256:
71deb2ba3c7fdbac922b6c487bc59de725e4af350ae6e4beee34acda7064f834.

Only the registered statement of `dyadic_gaussian_theta_mellin` is used from
outside Mathlib.  No proof-helper export from its full-proof mirror is used.
The public corollaries retain the literal registered seed/kernel definitions.
This file proves analytic inputs to a subcritical synthesis argument, not RH.
-/

set_option maxHeartbeats 4000000

section StandaloneThetaGeneralBounds
open Set Filter MeasureTheory Asymptotics
open scoped Topology SchwartzMap FourierTransform
namespace MasulloRH.ThetaSynthesisFacts.Internal
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
end MasulloRH.ThetaSynthesisFacts.Internal
end StandaloneThetaGeneralBounds

section StandaloneThetaPoisson
open MeasureTheory Filter Set FourierTransform
open scoped SchwartzMap FourierTransform Topology
set_option autoImplicit false
namespace MasulloRH.ThetaSynthesisFacts.Internal
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
end MasulloRH.ThetaSynthesisFacts.Internal
end StandaloneThetaPoisson

section StandaloneStripThetaRows
open MeasureTheory Filter Set FourierTransform
open scoped Topology FourierTransform SchwartzMap
namespace MasulloRH.ThetaSynthesisFacts.Internal
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
  simp only [logTheta,theta_poisson_scaled g (Real.exp_pos x),Real.exp_neg,
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
end MasulloRH.ThetaSynthesisFacts.Internal
end StandaloneStripThetaRows

section ExtractedSeedFacts
open Set Filter MeasureTheory
open scoped SchwartzMap FourierTransform
namespace MasulloRH.ThetaSynthesisFacts.Internal
noncomputable section

def generatorTest : 𝓢(ℝ,ℂ) := Classical.choose dyadic_gaussian_theta_mellin
theorem generatorTest_zero : generatorTest 0=0 := (Classical.choose_spec dyadic_gaussian_theta_mellin).2.1
theorem generatorTest_int : (∫x : ℝ,generatorTest x)=0 := (Classical.choose_spec dyadic_gaussian_theta_mellin).2.2.1

def seed : ℝ→ℂ := logTheta generatorTest
theorem seed_cont : Continuous seed := logTheta_continuous _ generatorTest_zero
theorem seed_decay (a : ℝ) : ∃ C : ℝ, 0≤C ∧ ∀ x, ‖seed x‖≤C*Real.exp (-a*|x|) :=
  logTheta_exp_decay _ generatorTest_zero generatorTest_int a

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

end
end MasulloRH.ThetaSynthesisFacts.Internal
end ExtractedSeedFacts

section StandaloneSynthDamping
open Set MeasureTheory Filter
open scoped Topology
namespace MasulloRH.ThetaSynthesisFacts.Internal
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
end MasulloRH.ThetaSynthesisFacts.Internal
end StandaloneSynthDamping

section StandaloneSynthWallContour
open Set MeasureTheory Filter
open scoped Topology Interval
namespace MasulloRH.ThetaSynthesisFacts.Internal
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
end MasulloRH.ThetaSynthesisFacts.Internal
end StandaloneSynthWallContour

section StandaloneSynthDampingDeriv
open Set Filter
open scoped Topology
namespace MasulloRH.ThetaSynthesisFacts.Internal
noncomputable section

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
  rw [vertical_im] at h
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
end MasulloRH.ThetaSynthesisFacts.Internal
end StandaloneSynthDampingDeriv

section StandaloneSynthWallReconstruction
open Set MeasureTheory Filter FourierTransform
open scoped Topology FourierTransform SchwartzMap Convolution
namespace MasulloRH.ThetaSynthesisFacts.Internal
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
end MasulloRH.ThetaSynthesisFacts.Internal
end StandaloneSynthWallReconstruction

section StandaloneSynthWallApproximateIdentity
open Set MeasureTheory Filter
open scoped Topology
namespace MasulloRH.ThetaSynthesisFacts.Internal
noncomputable section

def dilate (k : ℝ→ℂ) (ε t : ℝ) : ℂ := ((ε⁻¹:ℝ):ℂ)*k (ε⁻¹*t)

end
end MasulloRH.ThetaSynthesisFacts.Internal
end StandaloneSynthWallApproximateIdentity

section StandaloneSynthDampingKernel
open Set MeasureTheory Filter FourierTransform
open scoped Topology FourierTransform SchwartzMap ContDiff
namespace MasulloRH.ThetaSynthesisFacts.Internal
noncomputable section

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

end
end MasulloRH.ThetaSynthesisFacts.Internal
end StandaloneSynthDampingKernel

section StandaloneSynthPublicCoordinates
open Set Filter MeasureTheory FourierTransform
open scoped FourierTransform
namespace MasulloRH.ThetaSynthesisFacts.Internal
noncomputable section

theorem rationalDyadicThetaSeed_eq : rationalDyadicThetaSeed=seed := by
  funext x
  unfold rationalDyadicThetaSeed seed logTheta
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
end MasulloRH.ThetaSynthesisFacts.Internal
end StandaloneSynthPublicCoordinates

/-! Literal-coordinate corollaries for the finite-translate synthesis proof. -/
open Set MeasureTheory FourierTransform
open scoped Topology SchwartzMap FourierTransform
namespace MasulloRH.ThetaSynthesisFacts
noncomputable section

theorem seed_continuous : Continuous rationalDyadicThetaSeed := by
  rw [Internal.rationalDyadicThetaSeed_eq]
  exact Internal.seed_cont

theorem seed_exp_decay (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖rationalDyadicThetaSeed x‖ ≤ C * Real.exp (-A * |x|) := by
  rw [Internal.rationalDyadicThetaSeed_eq]
  exact Internal.seed_decay A

theorem weight_continuous (b p : ℝ) (hp : 0 ≤ p) :
    Continuous (fun x : ℝ => (1 + |x|)^p * Real.exp (b * |x|)) := by
  exact ((continuous_const.add continuous_abs).rpow_const (fun _ => Or.inr hp)).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs))

theorem weight_nonneg (b p x : ℝ) : 0 ≤ (1 + |x|)^p * Real.exp (b * |x|) := by
  positivity

theorem weight_le_exp (b p : ℝ) (hp : 0 ≤ p) (x : ℝ) :
    (1 + |x|)^p * Real.exp (b * |x|) ≤ Real.exp ((p+b) * |x|) := by
  have hx : 0 < 1 + |x| := by positivity
  have hlog : Real.log (1+|x|) ≤ |x| := by
    simpa using Real.log_le_sub_one_of_pos hx
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add, Real.exp_le_exp]
  nlinarith only [mul_le_mul_of_nonneg_right hlog hp]

/-- Polynomial weights can be absorbed in the seed's arbitrary exponential decay. -/
theorem seed_weighted_exp_decay (b p A : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ((1 + |x|)^p * Real.exp (b * |x|)) * ‖rationalDyadicThetaSeed x‖ ≤
        C * Real.exp (-A * |x|) := by
  obtain ⟨C,hC,h⟩ := seed_exp_decay (p+b+A)
  refine ⟨C,hC,fun x => ?_⟩
  calc
    _ ≤ Real.exp ((p+b)*|x|) * (C * Real.exp (-(p+b+A)*|x|)) :=
      mul_le_mul (weight_le_exp b p hp x) (h x) (norm_nonneg _) (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring

theorem seed_weighted_integrable (b p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun x =>
      ((1+|x|)^p * Real.exp (b*|x|)) * ‖rationalDyadicThetaSeed x‖) := by
  obtain ⟨C,hC,h⟩ := seed_weighted_exp_decay b p 1 hp
  apply (Internal.int_exp.const_mul C).mono'
    ((weight_continuous b p hp).mul seed_continuous.norm).aestronglyMeasurable
  filter_upwards with x
  change ‖((1+|x|)^p * Real.exp (b*|x|)) * ‖rationalDyadicThetaSeed x‖‖ ≤
    C * Real.exp (-|x|)
  rw [Real.norm_of_nonneg (mul_nonneg (weight_nonneg b p x) (norm_nonneg _))]
  simpa using h x

theorem seed_weighted_memLp (b p : ℝ) (hp : 0 ≤ p) :
    MemLp (fun x =>
      ((1+|x|)^p * Real.exp (b*|x|)) * ‖rationalDyadicThetaSeed x‖) 2 volume := by
  have hc := (weight_continuous b p hp).mul seed_continuous.norm
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2
  obtain ⟨C,hC,h⟩ := seed_weighted_exp_decay b p 1 hp
  apply (Internal.int_exp.const_mul (C^2)).mono' (hc.pow 2).aestronglyMeasurable
  filter_upwards with x
  change ‖(((1+|x|)^p * Real.exp (b*|x|)) * ‖rationalDyadicThetaSeed x‖)^2‖ ≤
    C^2 * Real.exp (-|x|)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have he0 := Real.exp_nonneg (-|x|)
  have he1 : Real.exp (-|x|) ≤ 1 := Real.exp_le_one_iff.mpr (by simp)
  have he2 : (Real.exp (-|x|))^2 ≤ Real.exp (-|x|) := by
    nlinarith only [mul_le_mul_of_nonneg_left he1 he0]
  calc
    _ ≤ (C * Real.exp (-|x|))^2 :=
      pow_le_pow_left₀ (mul_nonneg (weight_nonneg b p x) (norm_nonneg _)) (by simpa using h x) 2
    _ ≤ C^2 * Real.exp (-|x|) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left he2 (sq_nonneg C)

theorem seed_integrable : Integrable rationalDyadicThetaSeed := by
  have h := seed_weighted_integrable 0 0 le_rfl
  have hn : Integrable (fun x => ‖rationalDyadicThetaSeed x‖) := by simpa using h
  exact (integrable_norm_iff seed_continuous.aestronglyMeasurable).mp hn

theorem quarticKernel_one_eq :
    rationalQuarticKernel 1 = (Internal.dampingKernel : ℝ → ℂ) := by
  rw [Internal.rationalQuarticKernel_eq]
  funext x
  simp [Internal.dilate]

theorem quarticKernel_one_continuous : Continuous (rationalQuarticKernel 1) := by
  rw [quarticKernel_one_eq]
  exact Internal.dampingKernel.continuous

theorem quarticKernel_one_integrable : Integrable (rationalQuarticKernel 1) := by
  rw [quarticKernel_one_eq]
  exact Internal.dampingKernel.integrable

theorem quarticKernel_one_integral : (∫ x, rationalQuarticKernel 1 x) = 1 := by
  rw [quarticKernel_one_eq]
  have h := congrFun (Internal.dampingKernel_fourier 0) 0
  have ht : Internal.tilt 0 Internal.dampingKernel = (Internal.dampingKernel : ℝ → ℂ) := by
    funext x
    simp [Internal.tilt]
  rw [ht] at h
  simpa [Real.fourier_real_eq_integral_exp_smul, Internal.profile,
    Internal.damp, Internal.vertical] using h

/-- Every real exponential tilt of the literal unit quartic kernel is Schwartz. -/
theorem quarticKernel_one_tilt_schwartz (σ : ℝ) :
    ∃ g : 𝓢(ℝ,ℂ), (g : ℝ → ℂ) =
      fun x => (Real.exp (σ*x) : ℂ) * rationalQuarticKernel 1 x := by
  refine ⟨𝓕⁻ (Internal.dampingProfile 1 σ one_pos), ?_⟩
  rw [quarticKernel_one_eq]
  exact (Internal.dampingKernel_tilt σ).symm

theorem quarticKernel_one_tilt_integrable (σ : ℝ) :
    Integrable (fun x => (Real.exp (σ*x) : ℂ) * rationalQuarticKernel 1 x) := by
  obtain ⟨g,hg⟩ := quarticKernel_one_tilt_schwartz σ
  rw [← hg]
  exact g.integrable

theorem quarticKernel_one_exp_abs_integrable (A : ℝ) :
    Integrable (fun x => Real.exp (A*|x|) * ‖rationalQuarticKernel 1 x‖) := by
  have hp : Integrable (fun x => Real.exp (A*x) * ‖rationalQuarticKernel 1 x‖) := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
      using (quarticKernel_one_tilt_integrable A).norm
  have hm : Integrable (fun x => Real.exp (-A*x) * ‖rationalQuarticKernel 1 x‖) := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
      using (quarticKernel_one_tilt_integrable (-A)).norm
  apply (hp.add hm).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      quarticKernel_one_continuous.norm).aestronglyMeasurable
  filter_upwards with x
  change ‖Real.exp (A*|x|) * ‖rationalQuarticKernel 1 x‖‖ ≤
    Real.exp (A*x) * ‖rationalQuarticKernel 1 x‖ +
      Real.exp (-A*x) * ‖rationalQuarticKernel 1 x‖
  rw [Real.norm_of_nonneg (by positivity)]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (by positivity)
  · rw [abs_of_nonpos hx]
    have he : A*(-x) = -A*x := by ring
    rw [he]
    exact le_add_of_nonneg_left (by positivity)

theorem quarticKernel_one_weighted_integrable (b p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun x =>
      ((1+|x|)^p * Real.exp (b*|x|)) * ‖rationalQuarticKernel 1 x‖) := by
  apply (quarticKernel_one_exp_abs_integrable (p+b)).mono'
    ((weight_continuous b p hp).mul quarticKernel_one_continuous.norm).aestronglyMeasurable
  filter_upwards with x
  change ‖((1+|x|)^p * Real.exp (b*|x|)) * ‖rationalQuarticKernel 1 x‖‖ ≤
    Real.exp ((p+b)*|x|) * ‖rationalQuarticKernel 1 x‖
  rw [Real.norm_of_nonneg (mul_nonneg (weight_nonneg b p x) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (weight_le_exp b p hp x) (norm_nonneg _)

theorem quarticKernel_scale (ε : ℝ) :
    rationalQuarticKernel ε =
      fun x => ((ε⁻¹ : ℝ) : ℂ) * rationalQuarticKernel 1 (ε⁻¹*x) := by
  funext x
  simp [rationalQuarticKernel]

end
end MasulloRH.ThetaSynthesisFacts


-- Local component: ThetaSynthesisQuarticApprox
open MeasureTheory Filter Set
open scoped Topology Convolution

namespace MasulloRH.ThetaSynthesisFacts
noncomputable section

/-- The literal quartic kernel is a strong approximate identity for each nonnegative
polynomial-exponential weight. No positivity assumption on the kernel is used. -/
theorem quartic_approx_identity_tendsto (b p : ℝ) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (f : ℝ → ℂ) (hm : Measurable f)
    (hf : MemLp (fun x => ((1+|x|)^p*Real.exp (b*|x|))*‖f x‖) 2 volume) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ,
      (((1+|x|)^p*Real.exp (b*|x|))*
        ‖(rationalQuarticKernel ε ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x-f x‖)^2)
      (𝓝[>] 0) (𝓝 0) := by
  have hK : Integrable (fun t => (ThetaSynthesisWeight.weight b p t)^2*
      ‖rationalQuarticKernel 1 t‖) := by
    simp_rw [ThetaSynthesisWeight.weight_sq]
    exact quarticKernel_one_weighted_integrable (2*b) (2*p) (mul_nonneg (by norm_num) hp)
  have h := ThetaSynthesisAI.weighted_approximate_identity_tendsto
    (ThetaSynthesisWeight.weight b p) (ThetaSynthesisWeight.weight_continuous b p)
    (ThetaSynthesisWeight.weight_one_le b p hb hp) (ThetaSynthesisWeight.weight_zero b p)
    (ThetaSynthesisWeight.weight_neg b p) (ThetaSynthesisWeight.weight_submultiplicative b p hb hp)
    (ThetaSynthesisWeight.weight_dilate b p hb hp)
    (rationalQuarticKernel 1) f quarticKernel_one_continuous.measurable
    quarticKernel_one_integrable quarticKernel_one_integral hm hf hK
  have hscale (ε : ℝ) : ThetaSynthesisAI.dilate (rationalQuarticKernel 1) ε = rationalQuarticKernel ε :=
    (quarticKernel_scale ε).symm
  simpa only [ThetaSynthesisAI.energy, ThetaSynthesisWeight.weight, hscale] using h

/-- Small positive dilations give a genuine weighted L² error, so the preceding
real integral convergence is convergence in the weighted L² norm. -/
theorem quartic_approx_identity_memLp (b p : ℝ) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (f : ℝ → ℂ) (hm : Measurable f)
    (hf : MemLp (fun x => ((1+|x|)^p*Real.exp (b*|x|))*‖f x‖) 2 volume)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    MemLp (fun x => ((1+|x|)^p*Real.exp (b*|x|))*
      ‖(rationalQuarticKernel ε ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x-f x‖) 2 volume := by
  have hK : Integrable (fun t => (ThetaSynthesisWeight.weight b p t)^2*
      ‖rationalQuarticKernel 1 t‖) := by
    simp_rw [ThetaSynthesisWeight.weight_sq]
    exact quarticKernel_one_weighted_integrable (2*b) (2*p) (mul_nonneg (by norm_num) hp)
  have h := ThetaSynthesisAI.weighted_approximate_identity_memLp
    (ThetaSynthesisWeight.weight b p) (ThetaSynthesisWeight.weight_continuous b p)
    (ThetaSynthesisWeight.weight_one_le b p hb hp) (ThetaSynthesisWeight.weight_submultiplicative b p hb hp)
    (rationalQuarticKernel 1) f quarticKernel_one_continuous.measurable
    quarticKernel_one_integrable quarticKernel_one_integral hm hf hK ε hε
    (ThetaSynthesisWeight.weight_dilate b p hb hp ε hε hε1)
  have hscale : ThetaSynthesisAI.dilate (rationalQuarticKernel 1) ε = rationalQuarticKernel ε :=
    (quarticKernel_scale ε).symm
  simpa only [ThetaSynthesisWeight.weight, hscale] using h

end
end MasulloRH.ThetaSynthesisFacts


-- Local component: GenericStripThetaSynthesis
/-!
Forward subcritical theta synthesis. This is a corollary of the registered
generic-strip division theorem, with the weighted closure/approximate-identity
steps proved explicitly. It makes no assertion at the critical strip boundary.
-/

open MeasureTheory Filter Set
open scoped Topology Convolution

theorem solution :
    ∀ᵐ b : ℝ, 0 < b → b < 1/2 → ∀ p : ℝ, 0 ≤ p → ∀ f : ℝ → ℂ,
      Measurable f →
      MemLp (fun x : ℝ => ((1+|x|)^p * Real.exp (b*|x|)) * ‖f x‖) 2 volume →
      _root_.MasulloRH.RationalStripDivisorMoments b f → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (a : Fin m → ℂ) (y : Fin m → ℝ),
        MemLp (fun x : ℝ => ((1+|x|)^p * Real.exp (b*|x|)) *
          ‖f x - ∑ i : Fin m, a i * _root_.MasulloRH.rationalDyadicThetaSeed (x-y i)‖)
          2 volume ∧
        (∫ x : ℝ, (((1+|x|)^p * Real.exp (b*|x|)) *
          ‖f x - ∑ i : Fin m, a i * _root_.MasulloRH.rationalDyadicThetaSeed (x-y i)‖)^2) < δ := by
  filter_upwards [_root_.MasulloRH.generic_strip_dyadic_theta_division]
    with b hdiv hb hhalf p hp f hfm hF hMom δ hδ
  obtain ⟨C, hC, hbound⟩ := _root_.MasulloRH.ThetaSynthesisFacts.seed_exp_decay 0
  have hkb : ∀ x : ℝ, ‖_root_.MasulloRH.rationalDyadicThetaSeed x‖ ≤ C := by
    intro x
    simpa using hbound x
  apply _root_.MasulloRH.ThetaSynthesisAssembly.finite_approximation_of_convolution_limits
    (_root_.MasulloRH.ThetaSynthesisWeight.weight_continuous b p)
    (_root_.MasulloRH.ThetaSynthesisWeight.weight_nonneg b p)
    (_root_.MasulloRH.ThetaSynthesisWeight.weight_submultiplicative b p hb.le hp)
    _root_.MasulloRH.ThetaSynthesisFacts.seed_continuous
    _root_.MasulloRH.ThetaSynthesisFacts.seed_integrable C hkb
    (_root_.MasulloRH.ThetaSynthesisFacts.seed_weighted_integrable b p hp)
    (_root_.MasulloRH.ThetaSynthesisFacts.seed_weighted_memLp b p hp)
    f hfm.aestronglyMeasurable hF
    (fun ε => _root_.MasulloRH.rationalQuarticKernel ε ⋆[ContinuousLinearMap.mul ℂ ℂ] f)
    (_root_.MasulloRH.ThetaSynthesisFacts.quartic_approx_identity_tendsto b p hb.le hp f hfm hF)
    ?_ δ hδ
  intro ε hε
  obtain ⟨q, hqc, hqi, hQ, hEq⟩ := hdiv hb hhalf p hp f hfm hF hMom ε hε
  exact ⟨q, hqi, hQ, hEq⟩
