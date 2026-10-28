-- Prove2me | solution 1 for OAI.CubicTorus.delaunay_chamber_monotone_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T16:50:37.200537+00:00
-- url     : https://prove2.me/submissions/8f162500-290f-45b4-bd93-c8472581038b

import Mathlib
import Definitions.Def_OAIQ079A000

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_DelaunayPeriodicMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
namespace CubicTorus

lemma delaunay_energy {a b r p : ℝ} (ha : 0<a) (hab : a<b) (_hr : 0 < r)
    (hf : r/Real.sqrt (1+p^2)=(1/(a+b))*(r^2+a*b)) :
    p^2*(r^2+a*b)^2=(b^2-r^2)*(r^2-a^2) := by
  have hs : 0<Real.sqrt (1+p^2) := Real.sqrt_pos.mpr (by positivity)
  have hab0 : a+b≠0 := (show 0<a+b by linarith).ne'
  have he : r*(a+b)=(r^2+a*b)*Real.sqrt (1+p^2) := by
    field_simp at hf
    nlinarith only [hf]
  have he2 := congrArg (fun x : ℝ => x^2) he
  rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤1+p^2)] at he2
  nlinarith only [he2]

lemma delaunay_z_bounds {a b r : ℝ} (ha : 0<a) (hab : a<b) (hr : r∈Ioo a b) :
    (2*r^2-(a^2+b^2))/(b^2-a^2)∈Ioo (-1 : ℝ) 1 := by
  have hb : 0<b := ha.trans hab
  have hr0 : 0 < r := ha.trans hr.1
  have hΔ : 0<b^2-a^2 := by nlinarith only [ha,hab]
  constructor
  · apply (lt_div_iff₀ hΔ).2
    nlinarith only [ha,hr.1]
  · apply (div_lt_iff₀ hΔ).2
    nlinarith only [hr0,hr.2]

lemma delaunaySquare_amplitude {a b r : ℝ} (ha : 0<a) (hab : a<b) (hr : r∈Icc a b) :
    delaunaySquare a b (delaunayAmplitude a b r)=r^2 := by
  have hΔ : 0<b^2-a^2 := by nlinarith only [ha,hab]
  have hr0 : 0 < r := ha.trans_le hr.1
  have hz₁ : -1≤(2*r^2-(a^2+b^2))/(b^2-a^2) := by
    apply (le_div_iff₀ hΔ).2
    nlinarith only [ha,hr.1]
  have hz₂ : (2*r^2-(a^2+b^2))/(b^2-a^2)≤1 := by
    apply (div_le_iff₀ hΔ).2
    nlinarith only [hr0,hr.2]
  unfold delaunaySquare delaunayAmplitude
  rw [show 2*(Real.arccos ((2*r^2-(a^2+b^2))/(b^2-a^2))/2)=
    Real.arccos ((2*r^2-(a^2+b^2))/(b^2-a^2)) by ring,Real.cos_arccos hz₁ hz₂]
  field_simp
  ring

lemma hasDerivAt_delaunayAmplitude {a b t : ℝ} {r p : ℝ → ℝ}
    (ha : 0<a) (hab : a<b) (hr : HasDerivAt r (p t) t)
    (hbnd : r t∈Ioo a b) (hp : p t<0)
    (hf : r t/Real.sqrt (1+p t^2)=(1/(a+b))*(r t^2+a*b)) :
    HasDerivAt (fun s => delaunayAmplitude a b (r s))
      (r t/(r t^2+a*b)) t := by
  let z := (2*r t^2-(a^2+b^2))/(b^2-a^2)
  let Δ := b^2-a^2
  let A := r t^2+a*b
  have hb : 0<b := ha.trans hab
  have hr0 : 0 < r t := ha.trans hbnd.1
  have hΔ : 0<Δ := by dsimp [Δ]; nlinarith only [ha,hab]
  have hA : 0<A := add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos ha hb)
  have hz : z∈Ioo (-1 : ℝ) 1 := delaunay_z_bounds ha hab hbnd
  have hzpos : 0<1-z^2 := by nlinarith only [hz.1,hz.2]
  have hw : 0<Real.sqrt (1-z^2) := Real.sqrt_pos.mpr hzpos
  have hw2 := Real.sq_sqrt hzpos.le
  have henergy := delaunay_energy ha hab hr0 hf
  have hid : Δ^2*(1-z^2)=4*((b^2-r t^2)*(r t^2-a^2)) := by
    dsimp [z,Δ]
    field_simp [show b^2-a^2≠0 from hΔ.ne']
    ring
  have hsq : (Δ*Real.sqrt (1-z^2))^2=(-2*p t*A)^2 := by
    rw [mul_pow,hw2,hid,← henergy]
    dsimp only [A]
    ring
  have he : Δ*Real.sqrt (1-z^2)= -2*p t*A :=
    (sq_eq_sq₀ (mul_pos hΔ hw).le (mul_nonneg (by linarith only [hp] : 0≤ -2*p t) hA.le)).mp hsq
  have hzder := (((hr.pow 2).const_mul 2).sub_const (a^2+b^2)).div_const (b^2-a^2)
  have hd := ((Real.hasDerivAt_arccos hz.1.ne' hz.2.ne).comp t hzder).div_const 2
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Nat.reduceSub,Nat.cast_ofNat,pow_one]
  change r t/A=(-(1/Real.sqrt (1-z^2))*(2*(2*r t*p t)/Δ))/2
  field_simp [hA.ne',hΔ.ne',hw.ne']
  nlinarith only [he]

end CubicTorus

end
end

section

noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus

lemma delaunay_weight_pair_nonneg {a b y : ℝ} (ha : 0<a) (hab : a≤b)
    (hy : y∈Icc (a^2) (b^2)) :
    0≤(y-(a^2+b^2)/2)*
      ((Real.sqrt y+a*b/Real.sqrt y)-
        (Real.sqrt (a^2+b^2-y)+a*b/Real.sqrt (a^2+b^2-y))) := by
  let z := a^2+b^2-y
  let u := Real.sqrt y
  let v := Real.sqrt z
  have hb : 0<b := ha.trans_le hab
  have hy0 : 0<y := (sq_pos_of_pos ha).trans_le hy.1
  have hz0 : 0<z := by dsimp [z]; nlinarith only [hy.2,sq_pos_of_pos ha]
  have hu : 0<u := Real.sqrt_pos.mpr hy0
  have hv : 0<v := Real.sqrt_pos.mpr hz0
  have hu2 : u^2=y := Real.sq_sqrt hy0.le
  have hv2 : v^2=z := Real.sq_sqrt hz0.le
  have hyz : (a*b)^2≤y*z := by
    have h := mul_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hy.2)
    dsimp [z]
    nlinarith only [h]
  have huv : a*b≤u*v := by
    have hsq : (a*b)^2≤(u*v)^2 := by nlinarith only [hyz,hu2,hv2]
    exact (sq_le_sq₀ (mul_pos ha hb).le (mul_pos hu hv).le).mp hsq
  have hp : 0≤(y-(a^2+b^2)/2)*(u-v) := by
    have h : (y-(a^2+b^2)/2)*(u-v)=(u-v)^2*(u+v)/2 := by
      dsimp [z] at hv2
      have hS : a^2+b^2=u^2+v^2 := by linarith only [hu2,hv2]
      rw [hS,← hu2]
      ring
    rw [h]
    positivity
  have hq : 0≤1-a*b/(u*v) := by
    apply sub_nonneg.mpr
    exact (div_le_one (mul_pos hu hv)).2 huv
  have he : (u+a*b/u)-(v+a*b/v)=(u-v)*(1-a*b/(u*v)) := by
    field_simp
    ring
  change 0≤(y-(a^2+b^2)/2)*((u+a*b/u)-(v+a*b/v))
  rw [he,← mul_assoc]
  exact mul_nonneg hp hq

theorem delaunay_weighted_mean_bound {a b T : ℝ} (ha : 0<a) (hab : a≤b)
    (hT : 0≤T) {y : ℝ → ℝ} (hy : ContinuousOn y (Icc 0 T))
    (hbnd : ∀ t∈Icc 0 T,y t∈Icc (a^2) (b^2))
    (hsym : ∀ t∈Icc 0 T,y (T-t)=a^2+b^2-y t) :
    (a^2+b^2)/2 * (∫ t in (0 : ℝ)..T,Real.sqrt (y t)+a*b/Real.sqrt (y t)) ≤
      ∫ t in (0 : ℝ)..T,y t*(Real.sqrt (y t)+a*b/Real.sqrt (y t)) := by
  let c := (a^2+b^2)/2
  let w := fun t => Real.sqrt (y t)+a*b/Real.sqrt (y t)
  let f := fun t => (y t-c)*w t
  have hy0 (t) (ht : t∈Icc 0 T) : 0<y t := (sq_pos_of_pos ha).trans_le (hbnd t ht).1
  have hw : ContinuousOn w (Icc 0 T) :=
    (Real.continuous_sqrt.comp_continuousOn hy).add
      (continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn hy)
        (fun t ht => (Real.sqrt_pos.mpr (hy0 t ht)).ne'))
  have hf : ContinuousOn f (Icc 0 T) := (hy.sub continuousOn_const).mul hw
  have hfI : IntervalIntegrable f volume 0 T := hf.intervalIntegrable_of_Icc hT
  have hwr : ContinuousOn (fun t => f (T-t)) (Icc 0 T) :=
    hf.comp (continuousOn_const.sub continuousOn_id) (fun t ht => by constructor <;> linarith [ht.1,ht.2])
  have hfrI : IntervalIntegrable (fun t => f (T-t)) volume 0 T := hwr.intervalIntegrable_of_Icc hT
  have hnon : 0≤∫ t in (0 : ℝ)..T,f t+f (T-t) := by
    apply intervalIntegral.integral_nonneg hT
    intro t ht
    have h := delaunay_weight_pair_nonneg ha hab (hbnd t ht)
    rw [show f t+f (T-t)=(y t-c)*(w t-w (T-t)) by
      dsimp only [f]; rw [hsym t ht]; dsimp only [c]; ring]
    simpa only [w,hsym t ht,c] using h
  have hsymI : (∫ t in (0 : ℝ)..T,f (T-t))=∫ t in (0 : ℝ)..T,f t := by
    simpa only [sub_self,sub_zero] using intervalIntegral.integral_comp_sub_left f T (a := 0) (b := T)
  rw [intervalIntegral.integral_add hfI hfrI,hsymI] at hnon
  have hfi : (∫ t in (0 : ℝ)..T,f t) =
      (∫ t in (0 : ℝ)..T,y t*w t)-c*(∫ t in (0 : ℝ)..T,w t) := by
    simp only [f,sub_mul]
    have hi₁ : IntervalIntegrable (fun t => y t*w t) volume 0 T :=
      (hy.mul hw).intervalIntegrable_of_Icc hT
    have hi₂ : IntervalIntegrable (fun t => c*w t) volume 0 T :=
      (continuousOn_const.mul hw).intervalIntegrable_of_Icc hT
    rw [intervalIntegral.integral_sub hi₁ hi₂,intervalIntegral.integral_const_mul]
  rw [hfi] at hnon
  change c*(∫ t in (0 : ℝ)..T,w t)≤∫ t in (0 : ℝ)..T,y t*w t
  linarith

end CubicTorus

end
end

section

noncomputable section
open Set MeasureTheory Filter
namespace CubicTorus

lemma delaunaySquare_continuous (a b : ℝ) : Continuous (delaunaySquare a b) := by
  unfold delaunaySquare
  fun_prop

lemma delaunaySquare_bounds {a b : ℝ} (ha : 0<a) (hab : a<b) (θ : ℝ) :
    delaunaySquare a b θ∈Icc (a^2) (b^2) := by
  have hΔ : 0≤b^2-a^2 := by nlinarith only [ha,hab]
  have h₁ := mul_nonneg hΔ (show 0≤1+Real.cos (2*θ) by linarith [Real.neg_one_le_cos (2*θ)])
  have h₂ := mul_nonneg hΔ (show 0≤1-Real.cos (2*θ) by linarith [Real.cos_le_one (2*θ)])
  constructor <;> dsimp [delaunaySquare] <;> nlinarith only [h₁,h₂]

lemma delaunaySquare_reflect (a b θ : ℝ) :
    delaunaySquare a b (Real.pi/2-θ)=a^2+b^2-delaunaySquare a b θ := by
  unfold delaunaySquare
  rw [show 2*(Real.pi/2-θ)=Real.pi-2*θ by ring,Real.cos_pi_sub]
  ring

theorem delaunay_half_mean_bound {r p : ℝ → ℝ} {L U a b : ℝ}
    (hLU : L<U) (ha : 0<a) (hab : a<b)
    (hr : ∀ t,HasDerivAt r (p t) t)
    (hL : r L=b) (hU : r U=a)
    (hbnd : ∀ t∈Ioo L U,r t∈Ioo a b)
    (hp : ∀ t∈Ioo L U,p t<0)
    (hf : ∀ t∈Ioo L U,r t/Real.sqrt (1+p t^2)=(1/(a+b))*(r t^2+a*b)) :
    (a^2+b^2)/2*(U-L)≤∫ t in L..U,r t^2 := by
  let c := (a^2+b^2)/2
  let y := delaunaySquare a b
  let w := fun θ => Real.sqrt (y θ)+a*b/Real.sqrt (y θ)
  let f := fun θ => (y θ-c)*w θ
  let F := fun θ => ∫ s in (0 : ℝ)..θ,f s
  let A := fun t => delaunayAmplitude a b (r t)
  have hy : Continuous y := delaunaySquare_continuous a b
  have hypos (θ) : 0<y θ := (sq_pos_of_pos ha).trans_le (delaunaySquare_bounds ha hab θ).1
  have hw : Continuous w := hy.sqrt.add (continuous_const.div hy.sqrt (fun θ => (Real.sqrt_pos.mpr (hypos θ)).ne'))
  have hc : Continuous f := (hy.sub continuous_const).mul hw
  have hF (θ) : HasDerivAt F (f θ) θ := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable _ _) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun θ => (hF θ).continuousAt
  have hrc : Continuous r := continuous_iff_continuousAt.mpr fun t => (hr t).continuousAt
  have hAc : Continuous A := by
    dsimp [A,delaunayAmplitude]
    exact (Real.continuous_arccos.comp (((continuous_const.mul (hrc.pow 2)).sub continuous_const).div_const _)).div_const _
  have hde (t) (ht : t∈Ioo L U) : HasDerivAt (fun t => F (A t)) (r t^2-c) t := by
    have hA := hasDerivAt_delaunayAmplitude ha hab (hr t) (hbnd t ht) (hp t ht) (hf t ht)
    have hyA : y (A t)=r t^2 := delaunaySquare_amplitude ha hab ⟨(hbnd t ht).1.le,(hbnd t ht).2.le⟩
    have hr0 : 0 < r t := ha.trans (hbnd t ht).1
    have hd := (hF (A t)).comp t hA
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [f,w]
    rw [hyA,Real.sqrt_sq hr0.le]
    have hh : r t^2+a*b≠0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos ha (ha.trans hab))).ne'
    field_simp
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hLU.le
    (hFc.comp hAc).continuousOn hde ((hrc.pow 2).sub continuous_const |>.intervalIntegrable L U)
  have hAL : A L=0 := by dsimp only [A]; rw [hL,delaunayAmplitude_b ha hab]
  have hAU : A U=Real.pi/2 := by dsimp only [A]; rw [hU,delaunayAmplitude_a ha hab]
  simp only [Function.comp_apply,hAL,hAU] at hInt
  have hmean := delaunay_weighted_mean_bound ha hab.le (by positivity : 0≤Real.pi/2)
    hy.continuousOn (fun θ _ => delaunaySquare_bounds ha hab θ) (fun θ _ => delaunaySquare_reflect a b θ)
  have hnon : 0≤F (Real.pi/2) := by
    have he : F (Real.pi/2)=(∫ θ in (0 : ℝ)..(Real.pi/2),y θ*w θ)-c*(∫ θ in (0 : ℝ)..(Real.pi/2),w θ) := by
      dsimp only [F,f]
      simp only [sub_mul]
      have hi₁ : IntervalIntegrable (fun θ => y θ*w θ) volume 0 (Real.pi/2) := (hy.mul hw).intervalIntegrable _ _
      have hi₂ : IntervalIntegrable (fun θ => c*w θ) volume 0 (Real.pi/2) := (continuous_const.mul hw).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hi₁ hi₂, intervalIntegral.integral_const_mul]
    rw [he]
    exact sub_nonneg.mpr hmean
  have hF0 : F 0=0 := by simp [F]
  rw [hF0,sub_zero] at hInt
  have hi : IntervalIntegrable (fun t => r t^2) volume L U := (hrc.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi (intervalIntegrable_const),
    intervalIntegral.integral_const] at hInt
  change c*(U-L)≤∫ t in L..U,r t^2
  simp only [smul_eq_mul] at hInt
  linarith only [hInt,hnon]

end CubicTorus

end
end

section

noncomputable section
open Set MeasureTheory
namespace CubicTorus

lemma even_periodic_reflect_one {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (he : ∀ t,f (-t)=f t) (t : ℝ) : f (1-t)=f t := by
  rw [show 1-t= -t+1 by ring,hp,he]

lemma even_periodic_deriv_endpoints {r p : ℝ → ℝ}
    (hr : ∀ t,HasDerivAt r (p t) t) (hp : Function.Periodic r 1)
    (he : ∀ t,r (-t)=r t) : p 0=0 ∧ p (1/2)=0 := by
  have hfun : (fun t => r (-t))=r := funext he
  have hfun' : (fun t => r (1-t))=r := funext (even_periodic_reflect_one hp he)
  have hd₀ := (hr (-(0 : ℝ))).comp 0 (hasDerivAt_id (0 : ℝ)).neg
  simp only [neg_zero,mul_neg_one] at hd₀
  change HasDerivAt (fun t => r (-t)) (-p 0) 0 at hd₀
  rw [hfun] at hd₀
  have hz₀ := (hr 0).unique hd₀
  have hd₁ := (hr (1-(1/2 : ℝ))).comp (1/2)
    ((hasDerivAt_const (1/2 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (1/2 : ℝ)))
  norm_num at hd₁
  change HasDerivAt (fun t => r (1-t)) (-p (1/2)) (1/2) at hd₁
  rw [hfun'] at hd₁
  have hz₁ := (hr (1/2)).unique hd₁
  constructor <;> linarith only [hz₀,hz₁]

lemma even_periodic_integral_half {f : ℝ → ℝ} (hc : Continuous f)
    (hp : Function.Periodic f 1) (he : ∀ t,f (-t)=f t) :
    (∫ t in (0 : ℝ)..1,f t)=2*(∫ t in (0 : ℝ)..(1/2),f t) := by
  have hright : (∫ t in (1/2 : ℝ)..1,f t)=∫ t in (0 : ℝ)..(1/2),f t := by
    calc
      (∫ t in (1/2 : ℝ)..1,f t) = ∫ t in (1/2 : ℝ)..1,f (1-t) := by
        apply intervalIntegral.integral_congr
        intro t _
        exact (even_periodic_reflect_one hp he t).symm
      _ = ∫ t in (0 : ℝ)..(1/2),f t := by
        have hh := intervalIntegral.integral_comp_sub_left f 1 (a := (1/2 : ℝ)) (b := 1)
        norm_num at hh ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (1/2))
    (hc.intervalIntegrable (1/2) 1),hright]
  ring

end CubicTorus

end
end

section

noncomputable section
open Set MeasureTheory Filter
namespace CubicTorus

lemma delaunay_radius_at_zero_slope {a b r p : ℝ} (ha : 0<a) (hab : a<b)
    (hf : r/Real.sqrt (1+p^2)=(1/(a+b))*(r^2+a*b)) (hp : p=0) :
    r=a ∨ r=b := by
  have hs : a+b≠0 := (add_pos ha (ha.trans hab)).ne'
  simp only [hp,zero_pow (by decide : 2≠0),add_zero,Real.sqrt_one,div_one] at hf
  have he : (r-a)*(r-b)=0 := by
    field_simp at hf
    nlinarith only [hf]
  exact (mul_eq_zero.mp he).imp sub_eq_zero.mp sub_eq_zero.mp

theorem delaunay_even_monotone_mean {r p : ℝ → ℝ} {a b : ℝ}
    (ha : 0<a) (hab : a<b) (hr : ∀ t,HasDerivAt r (p t) t)
    (hrp : Function.Periodic r 1) (he : ∀ t,r (-t)=r t)
    (hneg : ∀ t∈Ioo (0 : ℝ) (1/2),p t<0)
    (hf : ∀ t,r t/Real.sqrt (1+p t^2)=(1/(a+b))*(r t^2+a*b)) :
    (a^2+b^2)/2≤∫ t in (0 : ℝ)..1,r t^2 := by
  have hc : Continuous r := continuous_iff_continuousAt.mpr fun t => (hr t).continuousAt
  have hanti : StrictAntiOn r (Icc (0 : ℝ) (1/2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc.continuousOn
    intro t ht
    rw [(hr t).deriv]
    exact hneg t (by simpa only [interior_Icc] using ht)
  have h01 : r (1/2) < r 0 := hanti (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hp0,hp1⟩ := even_periodic_deriv_endpoints hr hrp he
  have ha0 := delaunay_radius_at_zero_slope ha hab (hf 0) hp0
  have ha1 := delaunay_radius_at_zero_slope ha hab (hf (1/2)) hp1
  have hL : r 0=b := by
    rcases ha0 with h|h
    · rcases ha1 with h'|h' <;> linarith
    · exact h
  have hU : r (1/2)=a := by
    rcases ha1 with h|h
    · exact h
    · linarith
  have hbnd (t) (ht : t∈Ioo (0 : ℝ) (1/2)) : r t∈Ioo a b := by
    constructor
    · rw [← hU]
      exact hanti ⟨ht.1.le,ht.2.le⟩ (by norm_num) ht.2
    · rw [← hL]
      exact hanti (by norm_num) ⟨ht.1.le,ht.2.le⟩ ht.1
  have hm := delaunay_half_mean_bound (by norm_num : (0 : ℝ)<1/2) ha hab hr hL hU hbnd hneg
    (fun t _ => hf t)
  have hp2 : Function.Periodic (fun t => r t^2) 1 := fun t => by dsimp only; rw [hrp t]
  rw [even_periodic_integral_half (f := fun t => r t^2) (hc.pow 2) hp2 (fun t => by rw [he t])]
  linarith only [hm]

theorem delaunay_chamber_monotone_mean_oai {r p : ℝ → ℝ} {a b c : ℝ}
    (ha : 0<a) (hab : a<b) (hc : c=0 ∨ c=1/2)
    (hr : ∀ t,HasDerivAt r (p t) t)
    (hrp : Function.Periodic r 1) (he : ∀ t,r (-t)=r t)
    (hneg : ∀ t∈Ioo c (c+1/2),p t<0)
    (hf : ∀ t,r t/Real.sqrt (1+p t^2)=(1/(a+b))*(r t^2+a*b)) :
    (a^2+b^2)/2≤∫ t in (0 : ℝ)..1,r t^2 := by
  let s := fun t => r (t+c)
  let q := fun t => p (t+c)
  have hs (t) : HasDerivAt s (q t) t := by
    have hh := (hr (t+c)).comp t ((hasDerivAt_id t).add_const c)
    convert! hh using 1; simp [q]
  have hsp : Function.Periodic s 1 := by
    intro t
    dsimp only [s]
    rw [show t+1+c=(t+c)+1 by ring,hrp]
  have hse (t) : s (-t)=s t := by
    rcases hc with rfl|rfl
    · simpa only [s,add_zero] using he t
    · dsimp only [s]
      convert even_periodic_reflect_one hrp he (t+1/2) using 1; congr 1; ring
  have hsn (t) (ht : t∈Ioo (0 : ℝ) (1/2)) : q t<0 := hneg (t+c) ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hmean := delaunay_even_monotone_mean ha hab hs hsp hse hsn (fun t => hf (t+c))
  have hInt : (∫ t in (0 : ℝ)..1,s t^2)=∫ t in (0 : ℝ)..1,r t^2 := by
    dsimp only [s]
    rw [intervalIntegral.integral_comp_add_right (fun t => r t^2)]
    have hp2 : Function.Periodic (fun t => r t^2) 1 := fun t => by dsimp only; rw [hrp t]
    simpa only [zero_add,add_zero,add_comm] using hp2.intervalIntegral_add_eq c 0
  rwa [hInt] at hmean

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.delaunay_chamber_monotone_mean_oai := @OAI.CubicTorus.delaunay_chamber_monotone_mean_oai
