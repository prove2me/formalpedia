-- Prove2me | solution 1 for NoHair.Weyl.kerr_radial_quadrature_values
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:29:05.750269+00:00
-- url     : https://prove2.me/submissions/ca77d4cb-4167-451e-81d2-b4bb482f144d

import Theorems.Thm_NoHair_Weyl_kerr_radial_primitive_derivatives
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open NoHair NoHair.Weyl Filter Set MeasureTheory
open scoped Topology

noncomputable section

/-- A C¹ extension in the reciprocal Weyl radius bounds the radial derivative
by a constant multiple of exp(-s) on each infinite radial ray. -/
private theorem normalized_integral (f rate G : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hd : ∀ s, HasDerivAt f (rate s) s) (hg : ContDiffAt ℝ 1 G 0)
    (hzero : G 0 = 0) (hfg : ∀ s, f s = G (Real.exp (-s))) (s₀ : ℝ) :
    IntegrableOn rate (Ioi s₀) ∧ (∫ s in Ioi s₀, rate s) = -f s₀ := by
  have hG (t : ℝ) (ht : 0 ≤ t) : ContDiffAt ℝ 1 G t := by
    rcases ht.eq_or_lt with h | h
    · simpa only [← h] using hg
    · have hl : ContDiffAt ℝ 1 (fun y : ℝ => -Real.log y) t := by
        fun_prop (disch := exact h.ne')
      apply (hf.contDiffAt.comp t hl).congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds h] with y hy
      simp only [Function.comp_apply, hfg (-Real.log y), neg_neg, Real.exp_log hy]
  have hr : rate = deriv f := funext fun s => (hd s).deriv.symm
  have hc (s : ℝ) : rate s=deriv G (Real.exp (-s))*(-Real.exp (-s)) := by
    have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-s)) s := by
      simpa using (hasDerivAt_id' s).neg.exp
    have h := ((hG (Real.exp (-s)) (Real.exp_pos _).le).differentiableAt (by norm_num)).hasDerivAt.comp s he
    exact (hd s).unique (h.congr_of_eventuallyEq (Eventually.of_forall hfg))
  have hder : ContinuousOn (fun t : ℝ => ‖deriv G t‖) (Icc 0 (Real.exp (-s₀))) := by
    intro t ht
    exact ((hG t ht.1).derivWithin (m := 0) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨K,hK⟩ := isCompact_Icc.bddAbove_image hder
  have hint : IntegrableOn rate (Ioi s₀) := by
    apply ((integrableOn_exp_neg_Ioi s₀).const_mul K).mono'
    · rw [hr]; exact hf.continuous_deriv_one.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
      have ht : Real.exp (-s) ∈ Icc 0 (Real.exp (-s₀)) :=
        ⟨(Real.exp_pos _).le,Real.exp_le_exp.mpr (neg_le_neg (le_of_lt hs))⟩
      have hb := hK (mem_image_of_mem (fun t : ℝ => ‖deriv G t‖) ht)
      rw [hc,norm_mul,norm_neg,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hlim : Tendsto f atTop (𝓝 0) := by
    rw [funext hfg,← hzero]
    exact hg.continuousAt.tendsto.comp (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
  refine ⟨hint,?_⟩
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s _ => hd s) hint hlim

private def values (m a : ℝ) (p : OrbitPoint) : ℝ × ℝ :=
  let k := Real.sqrt (m^2-a^2)
  let x := prolateRadius k p
  let r := m+x
  let c := p.2/x
  let B := 1-c^2
  let P := (r^2+a^2)^2-a^2*kerrDelta m a r*B
  let D := x^2-k^2*c^2
  (-(2*m*r*a)/P, B*P/D)

private def rescaledRadius (k z t : ℝ) : ℝ :=
  (Real.sqrt (1+t^2*(z-k)^2)+Real.sqrt (1+t^2*(z+k)^2))/2

private def compactValues (m a k z t : ℝ) : ℝ × ℝ :=
  let x := rescaledRadius k z t
  let r := m*t+x
  let c := z*t/x
  let B := 1-c^2
  let A := r^2-2*m*r*t+(a*t)^2
  let P := (r^2+(a*t)^2)^2-(a*t)^2*A*B
  let D := x^2-(k*t)^2*c^2
  (-(2*m*r*a*t^3)/P, Real.log (B*P/D)/2)

private theorem rescaled_eq (k z s : ℝ) :
    rescaledRadius k z (Real.exp (-s))=Real.exp (-s)*prolateRadius k (s,z) := by
  let t := Real.exp (-s)
  have ht : 0 < t := Real.exp_pos _
  have hi : t^2*Real.exp (2*s)=1 := by
    dsimp [t]
    rw [sq,← Real.exp_add,← Real.exp_add,show -s+-s+2*s=0 by ring,Real.exp_zero]
  have side (u : ℝ) : Real.sqrt (1+t^2*u^2)=t*Real.sqrt (Real.exp (2*s)+u^2) := by
    rw [show 1+t^2*u^2=t^2*(Real.exp (2*s)+u^2) by rw [mul_add,hi],
      Real.sqrt_mul (sq_nonneg t),Real.sqrt_sq ht.le]
  change (Real.sqrt (1+t^2*(z-k)^2)+Real.sqrt (1+t^2*(z+k)^2))/2=_
  rw [side,side]
  dsimp [prolateRadius]
  ring

private theorem compact_smooth (m a k z : ℝ) :
    ContDiffAt ℝ 1 (fun t => (compactValues m a k z t).1) 0 ∧
    ContDiffAt ℝ 1 (fun t => (compactValues m a k z t).2) 0 := by
  constructor <;> unfold compactValues rescaledRadius <;>
    fun_prop (disch := norm_num)

private theorem compact_at_zero (m a k z : ℝ) : compactValues m a k z 0 = (0,0) := by
  norm_num [compactValues,rescaledRadius]

private theorem compact_agrees (m a s z : ℝ) (hL : 0 < (values m a (s,z)).2) :
    let k := Real.sqrt (m^2-a^2)
    let q := compactValues m a k z (Real.exp (-s))
    (values m a (s,z)).1=q.1 ∧ Real.log (values m a (s,z)).2/2-s=q.2 := by
  let k := Real.sqrt (m^2-a^2)
  let t := Real.exp (-s)
  let x := prolateRadius k (s,z)
  let r := m+x
  let c := z/x
  let B := 1-c^2
  let A := kerrDelta m a r
  let P := (r^2+a^2)^2-a^2*A*B
  let D := x^2-k^2*c^2
  have ht : t ≠ 0 := (Real.exp_pos _).ne'
  have hx : rescaledRadius k z t=t*x := rescaled_eq k z s
  have hc : z*t/(t*x)=c := by dsimp [c]; rw [mul_comm z t, mul_div_mul_left _ _ ht]
  have hr : m*t+t*x=t*r := by dsimp [r]; ring
  have hA : (t*r)^2-2*m*(t*r)*t+(a*t)^2=t^2*A := by dsimp [A,kerrDelta]; ring
  have hP : ((t*r)^2+(a*t)^2)^2-(a*t)^2*(t^2*A)*B=t^4*P := by dsimp [P]; ring
  have hD : (t*x)^2-(k*t)^2*c^2=t^2*D := by dsimp [D]; ring
  have hW : -(2*m*(t*r)*a*t^3)/(t^4*P)=-(2*m*r*a)/P := by
    rw [show -(2*m*(t*r)*a*t^3)=t^4*(-(2*m*r*a)) by ring,mul_div_mul_left _ _ (pow_ne_zero 4 ht)]
  have hL' : B*(t^4*P)/(t^2*D)=t^2*(B*P/D) := by
    rw [show B*(t^4*P)=t^2*(t^2*(B*P)) by ring,mul_div_mul_left _ _ (pow_ne_zero 2 ht),mul_div_assoc]
  change 0 < B*P/D at hL
  change (-(2*m*r*a)/P = (compactValues m a k z t).1) ∧
    (Real.log (B*P/D)/2-s=(compactValues m a k z t).2)
  dsimp only [compactValues]
  rw [hx,hr,hc]
  change _ = -(2*m*(t*r)*a*t^3) /
    (((t*r)^2+(a*t)^2)^2-(a*t)^2*((t*r)^2-2*m*(t*r)*t+(a*t)^2)*B) ∧
    _ = Real.log (B*(((t*r)^2+(a*t)^2)^2-(a*t)^2*((t*r)^2-2*m*(t*r)*t+(a*t)^2)*B)/
      ((t*x)^2-(k*t)^2*c^2)) / 2
  rw [hA,hP,hD,hW,hL',Real.log_mul (pow_ne_zero 2 ht) hL.ne',Real.log_pow]
  dsimp [t]
  rw [Real.log_exp]
  constructor <;> ring

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    HasRadialQuadratures (kerrErnst m a) ∧ ∀ p : OrbitPoint,
      let k := Real.sqrt (m^2-a^2)
      let x := prolateRadius k p
      let r := m+x
      let c := p.2/x
      let B := 1-c^2
      let P := (r^2+a^2)^2-a^2*kerrDelta m a r*B
      let D := x^2-k^2*c^2
      angularShift (kerrErnst m a) p = -(2*m*r*a)/P ∧
      Real.exp (2*conformalExponent (kerrErnst m a) p) = B*P/D := by
  let k := Real.sqrt (m^2-a^2)
  let u := kerrErnst m a
  let W := fun p => (values m a p).1
  let L := fun p => (values m a p).2
  let H := fun p : OrbitPoint => Real.log (L p)/2-p.1
  obtain ⟨hL,hW,hH,hd⟩ := kerr_radial_primitive_derivatives m a hm
  change ∀ p, 0 < L p at hL
  change ContDiff ℝ 1 W at hW
  change ContDiff ℝ 1 H at hH
  have ray (p : OrbitPoint) :
      (IntegrableOn (fun t => shiftRate u (t,p.2)) (Ioi p.1) ∧
       (∫ t in Ioi p.1, shiftRate u (t,p.2)) = -W p) ∧
      (IntegrableOn (fun t => conformalRate u (t,p.2)) (Ioi p.1) ∧
       (∫ t in Ioi p.1, conformalRate u (t,p.2)) = -H p) := by
    obtain ⟨s,z⟩ := p
    have hline : ContDiff ℝ 1 (fun t : ℝ => (t,z)) := contDiff_id.prodMk contDiff_const
    have hzero := compact_at_zero m a k z
    obtain ⟨hw,hh⟩ := compact_smooth m a k z
    constructor
    · exact normalized_integral (fun t => W (t,z)) _ _ (hW.comp hline)
        (fun t => (hd t z).1) hw (congrArg Prod.fst hzero)
        (fun t => (compact_agrees m a t z (hL _)).1) s
    · exact normalized_integral (fun t => H (t,z)) _ _ (hH.comp hline)
        (fun t => (hd t z).2) hh (congrArg Prod.snd hzero)
        (fun t => (compact_agrees m a t z (hL _)).2) s
  refine ⟨fun p => ⟨(ray p).1.1,(ray p).2.1⟩,?_⟩
  intro p
  change angularShift u p = W p ∧ Real.exp (2*conformalExponent u p)=L p
  constructor
  · unfold angularShift
    rw [(ray p).1.2,neg_neg]
  · unfold conformalExponent
    rw [(ray p).2.2]
    have h : 2*(p.1 - -H p)=Real.log (L p) := by dsimp only [H]; ring
    rw [h,Real.exp_log (hL p)]
