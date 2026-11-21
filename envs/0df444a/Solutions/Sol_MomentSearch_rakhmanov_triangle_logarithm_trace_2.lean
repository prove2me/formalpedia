-- Prove2me | solution 2 for MomentSearch.rakhmanov_triangle_logarithm_trace
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:41:10.224584+00:00
-- url     : https://prove2.me/submissions/88c2cd7f-243e-440d-b7fa-fbeaedfb4ade

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_quantile_real_regularization
import Theorems.Thm_MomentSearch_rakhmanov_triangle_phase_geometry


/-!
# Logarithmic trace for the Rakhmanov triangle

The theorem `solution` proves `MomentSearch.rakhmanov_triangle_logarithm_trace`.

Write m = N − k and A(z) = arctan((N/k)√(r²−z²)) with the principal branches.
On |Re z| < r, the radicand has strictly positive real part and Re A > 0.
Let G be a primitive of A with G(0)=0, and set φ(z)=πm/2−NG(z).
On the base, symmetry and the total mass identity give φ(t)=π∫ₜʳρ.
The imaginary part of G(x+iy) increases with y and vanishes at y=0.
Consequently u(z)=exp(−2iφ(z)) has modulus ≤1 on the upper triangle.
Since A is even and commutes with conjugation there and on its reflection,
G(−conj z)=−conj G(z). Thus φ(−conj z)=πm−conj φ(z) and
u(−conj z)=conj u(z).

Both A and G extend continuously to the two real vertices. Indeed A tends to
zero there, and G(z) is the integral of z A(tz) for 0≤t≤1. This expression
extends by uniform continuity of A on the closed triangle. As φ(r)=0,
integration along the right side Z gives 2iφ(Z(t))=B(t), including the factor
Z′=−rs in the definition of B.

Fix w=x−ih with h>0. For 0<q<1, put Λq=log(1+q u), on the principal
branch. Its argument lies in the open right half-plane. For 0<λ<1, shrink
all three triangle vertices towards zero by λ. On this closed triangle,
Λq(z)/(w−z) is differentiable within the triangle. The two upper edges from
λr to −λr therefore give the same integral as the oriented base from λr
to −λr. Let λ increase to one. Joint continuity on the full closed triangle
of Λq and of the Cauchy kernel gives convergence on each affine edge.
Reflection gives the full upper integral as Jq(x,h)−conj Jq(−x,h), where Jq
is the oriented right-side integral without the normalization by π.

Next let q increase to one. On the upper edges, 1+u is nonzero since |u|<1
above the real axis and u=1 at the two vertices. On the base, the zeros of
1+u are the finitely many quantiles. They are simple since φ′(y)=−πρ(y)≠0
there. Thus log|1+u| is integrable, as is also immediate from the proved
real regularization. The Abel majorant and limit below apply, since the
Cauchy multiplier is bounded by 1/h on the real edge.

Off the nodes let T(t)=∫ₜʳρ and n(t)=#{y∈Y | t≤y}. Tail mass decreases
from m to zero and takes each of 1/2,3/2,…,m−1/2 once, in reverse spatial
order. Hence n(t) is the unique integer within 1/2 of T(t). The cell
identity below gives Re Λ=log(2|cos(πT)|) and Im Λ=π(n−T). Finally
Im[(F+iπD)/(x−t−ih)] = [hF+πD(x−t)]/[(x−t)²+h²]. Reversing the base
orientation and dividing by π gives exactly the claimed logarithmic trace.

Source for the contour representation and the phase:
E. A. Rakhmanov, *Bounds for polynomials with a unit discrete norm*,
Annals of Mathematics 165 (2007), §3.1, Theorem 2 and equations (3.9)–(3.11).
-/

open Complex

/-- The principal complex arctangent is differentiable on the open right half-plane. -/
private theorem hasDerivAt_complexArctan_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    HasDerivAt Complex.arctan (1 / (1 + z ^ 2)) z := by
  let a (u : ℂ) := 1 + u * Complex.I
  let b (u : ℂ) := 1 - u * Complex.I
  have ha : a z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [a, Complex.mul_im] at hi
    linarith
  have hb : b z ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [b, Complex.mul_im] at hi
    linarith
  have hs : a z / b z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    apply ne_of_gt
    rw [Complex.div_im, ← sub_div]
    have hden : 0 < Complex.normSq (b z) := Complex.normSq_pos.mpr hb
    apply div_pos _ hden
    simp [a, b, Complex.mul_im, Complex.mul_re]
    nlinarith
  have h1 : HasDerivAt a Complex.I z := by
    simpa only [one_mul] using ((hasDerivAt_id' z).mul_const Complex.I).const_add 1
  have h2 : HasDerivAt b (-Complex.I) z := by
    simpa only [one_mul] using ((hasDerivAt_id' z).mul_const Complex.I).const_sub 1
  have hder := ((h1.div h2 hb).clog hs).const_mul (-Complex.I / 2)
  have hprod : (1 : ℂ) + z ^ 2 = a z * b z := by
    dsimp [a,b]
    calc
      _ = 1 - z ^ 2 * Complex.I ^ 2 := by rw [Complex.I_sq]; ring
      _ = _ := by ring
  have he :
      (-Complex.I / 2) * (((Complex.I * b z - a z * -Complex.I) / b z ^ 2) / (a z / b z)) =
        1 / (1 + z ^ 2) := by
    rw [hprod]
    have hab : a z + b z = 2 := by dsimp [a,b]; ring
    have hsum : Complex.I * b z - a z * -Complex.I = 2 * Complex.I := by
      linear_combination Complex.I * hab
    rw [hsum]
    field_simp [ha, hb]
    norm_num [Complex.I_sq]
  change HasDerivAt Complex.arctan
    ((-Complex.I / 2) * (((Complex.I * b z - a z * -Complex.I) / b z ^ 2) / (a z / b z))) z at hder
  rwa [he] at hder

open Set MeasureTheory
open scoped Real

private theorem arctan_continuousAt_zero : ContinuousAt Complex.arctan 0 := by
  have hA : ContinuousAt (fun z : ℂ => (1 + z * Complex.I) / (1 - z * Complex.I)) 0 :=
    (by fun_prop : Continuous fun z : ℂ => 1 + z * Complex.I).continuousAt.div
      (by fun_prop : Continuous fun z : ℂ => 1 - z * Complex.I).continuousAt (by simp)
  have hL : (1 + 0 * Complex.I) / (1 - 0 * Complex.I) ∈ Complex.slitPlane := by
    simp [Complex.mem_slitPlane_iff]
  exact continuousAt_const.mul ((continuousAt_clog hL).comp (f := fun z : ℂ => (1 + z * Complex.I) / (1 - z * Complex.I)) hA)

private theorem half_power_pos_re {z : ℂ} (hz : 0 < z.re) :
    0 < (z ^ (1/2 : ℂ)).re := by
  have hne : z ≠ 0 := by intro he; rw [he] at hz; norm_num at hz
  have ha := abs_lt.mp ((Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hz))
  rw [Complex.cpow_def_of_ne_zero hne, Complex.exp_re]
  apply mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo _)
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num [Complex.ofReal_div]
  rw [hhalf, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.log_im, mul_zero, zero_add]
  exact ⟨by linarith [ha.1, Real.pi_pos], by linarith [ha.2, Real.pi_pos]⟩

namespace MomentSearch

private theorem arctan_re_positive {z : ℂ} (hz : 0 < z.re) : 0 < (Complex.arctan z).re := by
  let v := (1 + z*Complex.I)/(1-z*Complex.I)
  have hn : 1-z*Complex.I ≠ 0 := by
    intro e
    have := congrArg Complex.im e
    simp at this
    linarith
  have hv : 0 < v.im := by
    dsimp [v]
    rw [Complex.div_im, ← sub_div]
    apply div_pos _ (Complex.normSq_pos.mpr hn)
    simp [Complex.mul_im,Complex.mul_re]
    linarith
  have ha : 0 < v.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hv.le) (fun e => hv.ne' (Complex.arg_eq_zero_iff.mp e.symm).2)
  change 0 < (-Complex.I / 2 * Complex.log v).re
  norm_num [Complex.mul_re,Complex.log_im] at *
  linarith

/-- The analytic equilibrium density has positive real part on the full vertical strip. -/
theorem equilibrium_density_on_strip (r c : ℝ) (hc : 0 < c) :
    let S := {z : ℂ | |z.re| < r}
    let A := fun z : ℂ => Complex.arctan ((c:ℂ)*(((r:ℂ)^2-z^2)^(1/2:ℂ)))
    DifferentiableOn ℂ A S ∧ (∀ z ∈ S, 0 < (A z).re) ∧
      ∃ F : ℂ → ℂ, ∀ z ∈ S, HasDerivWithinAt F (A z) S z := by
  intro S A
  have hr (z : ℂ) (hz : z ∈ S) : 0 < (((r:ℂ)^2-z^2)).re := by
    change |z.re| < r at hz
    have he := abs_lt.mp hz
    simp [pow_two,Complex.mul_re]
    nlinarith [mul_pos (show 0 < r-z.re by linarith [he.2])
      (show 0 < r+z.re by linarith [he.1]),sq_nonneg z.im]
  have hroot (z : ℂ) (hz : z ∈ S) :
      0 < ((c:ℂ)*(((r:ℂ)^2-z^2)^(1/2:ℂ))).re := by
    simpa [Complex.mul_re] using mul_pos hc (half_power_pos_re (hr z hz))
  have hd : DifferentiableOn ℂ A S := by
    intro z hz
    have hbase : DifferentiableAt ℂ (fun z : ℂ => (r:ℂ)^2-z^2) z := by fun_prop
    have hdroot := hbase.cpow_const (c := (1/2:ℂ)) (Complex.mem_slitPlane_iff.mpr (Or.inl (hr z hz)))
    exact ((hasDerivAt_complexArctan_of_re_pos _ (hroot z hz)).differentiableAt.comp z
      (hdroot.const_mul (c:ℂ))).differentiableWithinAt
  refine ⟨hd,fun z hz => arctan_re_positive (hroot z hz), ?_⟩
  apply Convex.exists_forall_hasDerivWithinAt _ hd
  intro x hx y hy a b ha hb hab
  change |(a • x + b • y).re| < r
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  change |x.re| < r at hx
  change |y.re| < r at hy
  have h1 := abs_lt.mp hx
  have h2 := abs_lt.mp hy
  have av := (convex_Ioo (-r) r) (show x.re ∈ Ioo (-r) r from h1) (show y.re ∈ Ioo (-r) r from h2) ha hb hab
  exact abs_lt.mpr av
end MomentSearch

namespace MomentSearch

/-- Cauchy deformation along three affine edges, also valid on a closed convex set. -/
theorem triangle_segment_deformation {S : Set ℂ} (hs : Convex ℝ S)
    {H : ℂ → ℂ} (hd : DifferentiableOn ℂ H S) {a b c : ℂ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    let J := fun p q : ℂ => ∫ t in (0:ℝ)..1, (q-p)*H (AffineMap.lineMap p q t)
    J a b + J b c = J a c := by
  intro J
  obtain ⟨G,dG⟩ := hs.exists_forall_hasDerivWithinAt hd
  have piece (p q : ℂ) (hp : p ∈ S) (hq : q ∈ S) : J p q = G q-G p := by
    let γ : ℝ → ℂ := AffineMap.lineMap p q
    have map : MapsTo γ (Icc 0 1) S := fun _ ht => hs.lineMap_mem hp hq ht
    have cg : Continuous γ := AffineMap.lineMap_continuous
    have deriv (t : ℝ) (ht : t ∈ Icc 0 1) :
        HasDerivWithinAt (G ∘ γ) ((q-p)*H (γ t)) (Icc 0 1) t := by
      exact (dG _ (map ht)).scomp t (AffineMap.hasDerivAt_lineMap.hasDerivWithinAt) map
    have co : ContinuousOn (G ∘ γ) (Icc 0 1) := fun t ht => (deriv t ht).continuousWithinAt
    have ci : ContinuousOn (fun t => (q-p)*H (γ t)) (Icc 0 1) := (continuousOn_const.mul (hd.continuousOn.comp cg.continuousOn map))
    have eqn := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one co
      (fun t ht => (deriv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      (ci.intervalIntegrable_of_Icc zero_le_one)
    simpa [J,γ,Function.comp_def] using eqn
  rw [piece a b ha hb,piece b c hb hc,piece a c ha hc]
  ring
end MomentSearch

namespace MomentSearch

theorem vertical_primitive_im_strictMono (r x : ℝ) (hx : |x| < r) {A G : ℂ → ℂ}
    (hd : ∀ z : ℂ, |z.re| < r → HasDerivWithinAt G (A z) {v : ℂ | |v.re| < r} z)
    (hp : ∀ z : ℂ, |z.re| < r → 0 < (A z).re) :
    StrictMono (fun y : ℝ => (G ((x : ℂ) + (y : ℂ)*Complex.I)).im) := by
  let γ := fun y : ℝ => (x : ℂ) + (y : ℂ)*Complex.I
  have mem (y : ℝ) : |(γ y).re| < r := by simpa [γ] using hx
  have ho : IsOpen {v : ℂ | |v.re| < r} := isOpen_lt Complex.continuous_re.abs continuous_const
  have d (y : ℝ) : HasDerivAt (fun t => (G (γ t)).im) (A (γ y)).re y := by
    have path : HasDerivAt (fun v : ℂ => (x : ℂ) + v*Complex.I) Complex.I (y:ℂ) := by
      simpa using ((hasDerivAt_id' (y:ℂ)).mul_const Complex.I).const_add (x:ℂ)
    have e := ((hd (γ y) (mem y)).hasDerivAt (ho.mem_nhds (mem y))).comp (y:ℂ) path
    have e' := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y e.comp_ofReal
    simpa [Function.comp_def,γ] using e'
  exact strictMono_of_hasDerivAt_pos d (fun y => hp _ (mem y))

end MomentSearch

namespace MomentSearch

/-- Uniform bound up to the Abel limit, also when the trace has isolated log poles. -/
theorem abel_log_majorant (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1)
    (u : ℂ) (hu : ‖u‖ ≤ 1) (hne : 1+u ≠ 0) :
    ‖Complex.log (1+(q:ℂ)*u)‖ ≤ |Real.log ‖1+u‖| + Real.log 2 + Real.pi := by
  let v := 1+(q:ℂ)*u
  have qu : ‖(q:ℂ)*u‖ ≤ q := by
    simpa [norm_mul,abs_of_nonneg hq] using mul_le_mul_of_nonneg_left hu hq
  have lo : 1-q ≤ ‖v‖ := by
    have e := norm_sub_le v ((q:ℂ)*u)
    have en : v - (q:ℂ)*u = 1 := by simp [v]
    rw [en,norm_one] at e
    linarith
  have up : ‖v‖ ≤ 2 := by
    have e := norm_add_le (1:ℂ) ((q:ℂ)*u)
    simp only [norm_one] at e
    dsimp [v]; linarith
  have half : ‖1+u‖/2 ≤ ‖v‖ := by
    have e : (1:ℂ)+u = v + ((1-q:ℝ):ℂ)*u := by dsimp [v]; push_cast; ring
    have e' := norm_add_le v (((1-q:ℝ):ℂ)*u)
    rw [← e,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)] at e'
    nlinarith [mul_le_mul_of_nonneg_left hu (show 0 ≤ 1-q by linarith)]
  have lg := Real.log_le_log (half_pos (norm_pos_iff.mpr hne)) half
  rw [Real.log_div (norm_pos_iff.mpr hne).ne' (by norm_num)] at lg
  have ug := Real.log_le_log (show 0 < ‖v‖ by linarith) up
  have re : |Real.log ‖v‖| ≤ |Real.log ‖1+u‖| + Real.log 2 := by
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le (Real.log ‖1+u‖),abs_nonneg (Real.log ‖1+u‖)]
  apply (Complex.norm_le_abs_re_add_abs_im (Complex.log v)).trans
  rw [Complex.log_re,Complex.log_im]
  exact add_le_add re (Complex.abs_arg_le_pi v)

end MomentSearch

namespace MomentSearch
open Filter
open scoped Topology

theorem abel_log_integral_limit (a b : ℝ) (u W : ℝ → ℂ)
    (um : Measurable u) (wm : Measurable W) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ t ∈ uIoc a b, ‖u t‖ ≤ 1) (hW : ∀ t ∈ uIoc a b, ‖W t‖ ≤ M)
    (hne : ∀ᵐ t ∂volume, t ∈ uIoc a b → 1+u t ≠ 0)
    (hi : IntervalIntegrable (fun t => Real.log ‖1+u t‖) volume a b) :
    Tendsto (fun q : ℝ => ∫ t in a..b, W t * Complex.log (1+(q:ℂ)*u t))
      (𝓝[<] 1) (𝓝 (∫ t in a..b, W t * Complex.log (1+u t))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => M*(|Real.log ‖1+u t‖|+Real.log 2+Real.pi))
  · exact .of_forall fun q => (show Measurable (fun t => W t * Complex.log (1+(q:ℂ)*u t)) by fun_prop).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 by norm_num))] with q hq hp
    filter_upwards [hne] with t hn
    intro ht
    rw [norm_mul]
    exact mul_le_mul (hW t ht) (abel_log_majorant q (le_of_lt hp) hq _ (hu t ht) (hn ht)) (norm_nonneg _) hM
  · exact ((hi.abs.add intervalIntegrable_const).add intervalIntegrable_const).const_mul _
  · filter_upwards [hne] with t hn
    intro ht
    have slit : 1+u t ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      by_cases h : (1+u t).im = 0
      · left
        have h₀ := (Complex.abs_re_le_norm (u t)).trans (hu t ht)
        have nn := (abs_le.mp h₀).1
        have ne : (1+u t).re ≠ 0 := fun e => hn ht (Complex.ext e h)
        simp only [Complex.add_re,Complex.one_re] at *
        exact lt_of_le_of_ne (by linarith) ne.symm
      · exact Or.inr h
    have cont : ContinuousAt (fun q : ℝ => W t * Complex.log (1+(q:ℂ)*u t)) 1 := by
      apply continuousAt_const.mul
      exact (continuousAt_clog (by simpa using slit : 1+((1:ℝ):ℂ)*u t ∈ Complex.slitPlane)).comp (f := fun q : ℝ => 1+(q:ℂ)*u t) (by fun_prop)
    simpa using (cont.continuousWithinAt (s := Iio 1)).tendsto
end MomentSearch

namespace MomentSearch

/-- Boundary value away from the midpoint of a quantile cell. -/
theorem quantile_cell_log_trace (T : ℝ) (n : ℤ) (h : |(n:ℝ)-T| < 1/2) :
    let v := 1 + Complex.exp (-2*(Real.pi:ℂ)*(T:ℂ)*Complex.I)
    (Complex.log v).re = Real.log (2*|Real.cos (Real.pi*T)|) ∧
    (Complex.log v).im = Real.pi*((n:ℝ)-T) := by
  intro v
  let θ := Real.pi*((n:ℝ)-T)
  have hh := abs_lt.mp h
  have ang : -(Real.pi/2) < θ ∧ θ < Real.pi/2 := by
    dsimp [θ]; constructor <;> nlinarith [Real.pi_pos,mul_lt_mul_of_pos_left hh.1 Real.pi_pos,
      mul_lt_mul_of_pos_left hh.2 Real.pi_pos]
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ang
  have shift : Real.cos θ = |Real.cos (Real.pi*T)| := by
    rw [← abs_of_pos hc]
    change |Real.cos (Real.pi*((n:ℝ)-T))| = _
    rw [show Real.pi*((n:ℝ)-T) = n*Real.pi-Real.pi*T by ring,Real.cos_int_mul_pi_sub,abs_mul,abs_zpow]
    norm_num
  let e := Complex.exp ((θ:ℂ)*Complex.I)
  have unit : ‖e‖ = 1 := by simp [e,Complex.norm_exp]
  have period : Complex.exp ((θ:ℂ)*Complex.I + (θ:ℂ)*Complex.I) =
      Complex.exp (-2*(Real.pi:ℂ)*(T:ℂ)*Complex.I) := by
    rw [show (θ:ℂ)*Complex.I+(θ:ℂ)*Complex.I =
      (n:ℂ)*(2*(Real.pi:ℂ)*Complex.I)+(-2*(Real.pi:ℂ)*(T:ℂ)*Complex.I) by dsimp [θ]; push_cast; ring,
      Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,one_mul]
  have factor : v = ((2*Real.cos θ : ℝ):ℂ)*e := by
    change 1+Complex.exp _ = _
    rw [← period,Complex.exp_add]
    rw [Complex.ofReal_mul (2:ℝ) (Real.cos θ),Complex.ofReal_cos]
    dsimp [Complex.cos,e]
    have ee := Complex.exp_add (-(θ:ℂ)*Complex.I) ((θ:ℂ)*Complex.I)
    rw [show -(θ:ℂ)*Complex.I+(θ:ℂ)*Complex.I = 0 by ring,Complex.exp_zero] at ee
    linear_combination ee
  have pos : 0 < 2*Real.cos θ := by positivity
  constructor
  · rw [Complex.log_re,factor,norm_mul,unit,mul_one,Complex.norm_real, Real.norm_eq_abs,abs_of_pos pos,shift]
  · rw [Complex.log_im,factor,Complex.arg_real_mul _ pos]
    change (Complex.exp ((θ:ℂ)*Complex.I)).arg = θ
    rw [Complex.arg_exp]
    simp only [Complex.mul_I_im,Complex.ofReal_re]
    apply (toIocMod_eq_self _).2
    constructor <;> linarith [ang.1,ang.2,Real.pi_pos]
end MomentSearch

namespace MomentSearch

theorem count_half_mass_levels (m : ℕ) (T : ℝ) (h₀ : 0 ≤ T) (hm : T ≤ m)
    (hoff : ∀ j : Fin m, T ≠ (j.val : ℝ)+1/2) :
    ∃ n : ℕ, (∑ j : Fin m, if (j.val:ℝ)+1/2 ≤ T then (1:ℝ) else 0) = n ∧
      |(n:ℝ)-T| < 1/2 := by
  classical
  let n := ⌊T+1/2⌋₊
  have hpos : 0 ≤ T+1/2 := by linarith
  have hl : (n:ℝ) ≤ T+1/2 := Nat.floor_le hpos
  have hg : T+1/2 < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have hn : n ≤ m := by
    by_contra! hn
    have := (show (m:ℝ)+1 ≤ n by exact_mod_cast hn)
    linarith
  have ne : (n:ℝ) ≠ T+1/2 := by
    intro he
    have hn₀ : 0 < n := by
      by_contra! hh
      have hzero : n = 0 := by omega
      rw [hzero,Nat.cast_zero] at he
      linarith
    let j : Fin m := ⟨n-1,by omega⟩
    have hj : (j.val:ℝ) = (n:ℝ)-1 := by
      change ((n-1:ℕ):ℝ) = _; rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    exact hoff j (by linarith)
  refine ⟨n,?_,abs_lt.mpr ⟨by linarith,by linarith [lt_of_le_of_ne hl ne]⟩⟩
  have iff' (j : ℕ) : (j:ℝ)+1/2 ≤ T ↔ j < n := by
    constructor
    · intro hj
      by_contra! he
      have : (n:ℝ) ≤ j := by exact_mod_cast he
      linarith
    · intro hj
      have : (j:ℝ)+1 ≤ n := by exact_mod_cast hj
      linarith
  simp_rw [iff']
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < n then (1:ℝ) else 0)]
  rw [← Finset.sum_filter]
  have sets : (Finset.range m).filter (fun j => j < n) = Finset.range n := by
    ext j; simp only [Finset.mem_filter,Finset.mem_range]; omega
  simp [sets]
end MomentSearch

namespace MomentSearch

theorem quantile_log_trace_from_levels (a b : ℝ) (hab : a ≤ b) (m : ℕ)
    (T : ℝ → ℝ) (hc : ContinuousOn T (Icc a b)) (hT : StrictAntiOn T (Icc a b))
    (ha : T a = m) (hb : T b = 0) (Y : Finset ℝ) (hcard : Y.card = m)
    (hnodes : ∀ t ∈ Icc a b, Real.cos (Real.pi*T t) = 0 → t ∈ Y)
    (t : ℝ) (ht : t ∈ Icc a b) (hoff : t ∉ Y) :
    let v := 1 + Complex.exp (-2*(Real.pi:ℂ)*(T t:ℂ)*Complex.I)
    (Complex.log v).re = Real.log (2*|Real.cos (Real.pi*T t)|) ∧
    (Complex.log v).im = Real.pi*((∑ y ∈ Y, if t ≤ y then (1:ℝ) else 0)-T t) := by
  classical
  have levels (i : Fin m) : ∃ y ∈ Icc a b, T y = (i.val:ℝ)+1/2 := by
    apply intermediate_value_Icc' hab hc
    rw [ha,hb]
    have hi : (i.val:ℝ)+1 ≤ m := by exact_mod_cast i.isLt
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i.val]
  choose y hy hyT using levels
  have inj : Function.Injective y := by
    intro i j e
    apply Fin.ext
    exact_mod_cast (show (i.val:ℝ) = j.val by linarith [hyT i,hyT j,congrArg T e])
  have roots (i : Fin m) : y i ∈ Y := by
    apply hnodes _ (hy i)
    rw [Real.cos_eq_zero_iff,hyT]
    exact ⟨i.val,by push_cast; ring⟩
  have heq : Finset.univ.image y = Y := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact roots i
    · simp [Finset.card_image_of_injective _ inj,hcard]
  have ne (j : Fin m) : T t ≠ (j.val:ℝ)+1/2 := by
    intro e
    have same : t = y j := hT.injOn ht (hy j) (e.trans (hyT j).symm)
    exact hoff (same ▸ roots j)
  obtain ⟨n,hcount,hr⟩ := count_half_mass_levels m (T t)
    (hb ▸ hT.antitoneOn ht (right_mem_Icc.mpr hab) ht.2)
    (ha ▸ hT.antitoneOn (left_mem_Icc.mpr hab) ht ht.1) ne
  have cc : (∑ z ∈ Y, if t ≤ z then (1:ℝ) else 0) = n := by
    rw [← heq,Finset.sum_image (fun _ _ _ _ h => inj h)]
    convert hcount using 1
    apply Finset.sum_congr rfl
    intro j _
    have cut : t ≤ y j ↔ (j.val:ℝ)+1/2 ≤ T t := by
      rw [← hyT j]
      exact (hT.le_iff_ge (hy j) ht).symm
    simp_rw [cut]
  rw [cc]
  exact quantile_cell_log_trace (T t) (n:ℤ) (by exact_mod_cast hr)
end MomentSearch

namespace MomentSearch

/-- Cauchy deformation of the Abel-regularized logarithm on a convex domain. -/
theorem abel_triangle_segment_deformation {S : Set ℂ} (hs : Convex ℝ S)
    (u : ℂ → ℂ) (du : DifferentiableOn ℂ u S) (hu : ∀ z ∈ S, ‖u z‖ ≤ 1)
    (w : ℂ) (hw : w ∉ S) (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1)
    (a b c : ℂ) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    let H := fun z : ℂ => Complex.log (1+(q:ℂ)*u z)/(w-z)
    let J := fun p v : ℂ => ∫ t in (0:ℝ)..1, (v-p)*H (AffineMap.lineMap p v t)
    J a b + J b c = J a c := by
  intro H J
  apply triangle_segment_deformation hs _ ha hb hc
  intro z hz
  have bound : ‖(q:ℂ)*u z‖ ≤ q := by
    simpa [norm_mul,abs_of_nonneg hq] using mul_le_mul_of_nonneg_left (hu z hz) hq
  have slit : 1+(q:ℂ)*u z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans bound)).1
    simp only [Complex.add_re,Complex.one_re]
    linarith
  exact ((differentiableWithinAt_const (1:ℂ)).add ((du z hz).const_mul (q:ℂ))).clog slit |>.div
       ((differentiableWithinAt_const w).sub differentiableWithinAt_id) (sub_ne_zero.mpr (fun e => hw (e ▸ hz)))
end MomentSearch

namespace MomentSearch

/-- The vertices may lie on the boundary, where the integrand need only be continuous. -/
theorem triangle_segment_deformation_closure {S : Set ℂ} (hs : Convex ℝ S)
    {H : ℂ → ℂ} (hd : DifferentiableOn ℂ H S) (co : ContinuousOn H (closure S))
    {a b c : ℂ} (ha : a ∈ closure S) (hb : b ∈ closure S) (hc : c ∈ closure S) :
    let J := fun p q : ℂ => ∫ t in (0:ℝ)..1, (q-p)*H (AffineMap.lineMap p q t)
    J a b + J b c = J a c := by
  intro J
  let f : C(closure S,ℂ) := ⟨_,continuousOn_iff_continuous_domRestrict.mp co⟩
  obtain ⟨F,he⟩ := ContinuousMap.exists_restrict_eq isClosed_closure f
  have eqf : EqOn F H (closure S) := fun t ht => congrArg (fun g : C(closure S,ℂ) => g ⟨t,ht⟩) he
  let K := fun p q : ℂ => ∫ t in (0:ℝ)..1, (q-p)*F (AffineMap.lineMap p q t)
  have agree (p q : ℂ) (hp : p ∈ closure S) (hq : q ∈ closure S) : K p q = J p q := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact congrArg ((q-p)*·) (eqf (hs.closure.lineMap_mem hp hq ht))
  have cK : Continuous (fun z : ℂ × ℂ => K z.1 z.2) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    simp only [Function.uncurry_def,AffineMap.lineMap_apply_module]
    fun_prop
  have dF : DifferentiableOn ℂ (F : ℂ → ℂ) S := hd.congr (eqf.mono subset_closure)
  let D : Set (ℂ × ℂ × ℂ) := S ×ˢ (S ×ˢ S)
  have eq : EqOn (fun z : ℂ × ℂ × ℂ => K z.1 z.2.1 + K z.2.1 z.2.2)
      (fun z => K z.1 z.2.2) D :=
    fun z hz => triangle_segment_deformation hs dF hz.1 hz.2.1 hz.2.2
  have pair {p q : ℂ × ℂ × ℂ → ℂ} (cp : Continuous p) (cq : Continuous q) :
      Continuous (fun z => K (p z) (q z)) := cK.comp (cp.prodMk cq)
  have cl := eq.closure
    ((pair continuous_fst (continuous_fst.comp continuous_snd)).add
      (pair (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)))
    (pair continuous_fst (continuous_snd.comp continuous_snd))
  have mem : (a,b,c) ∈ closure D := by
    simpa only [D,closure_prod_eq] using (show (a,b,c) ∈ closure S ×ˢ (closure S ×ˢ closure S) from ⟨ha,hb,hc⟩)
  simpa only [agree _ _ ha hb,agree _ _ hb hc,agree _ _ ha hc] using cl mem
end MomentSearch

namespace MomentSearch
open Filter
open scoped Topology

/-- The primitive obtained by integrating along a segment extends differentiably
within the closure if the density extends continuously there. -/
theorem primitive_on_convex_closure {S : Set ℂ} (hs : Convex ℝ S)
    {A : ℂ → ℂ} (dA : DifferentiableOn ℂ A S) (cA : ContinuousOn A (closure S))
    {o : ℂ} (ho : o ∈ closure S) :
    ∃ G : ℂ → ℂ, G o = 0 ∧
      (∀ p ∈ closure S, HasDerivWithinAt G (A p) (closure S) p) ∧
      ∀ p ∈ closure S, ∀ z ∈ closure S, G z-G p =
        ∫ t in (0:ℝ)..1, (z-p)*A (AffineMap.lineMap p z t) := by
  let J := fun p q : ℂ => ∫ t in (0:ℝ)..1, (q-p)*A (AffineMap.lineMap p q t)
  let G := J o
  have inc (p : ℂ) (hp : p ∈ closure S) (z : ℂ) (hz : z ∈ closure S) :
      G z-G p = J p z := by
    have e := triangle_segment_deformation_closure hs dA cA ho hp hz
    change G p+J p z=G z at e
    linear_combination -e
  refine ⟨G,by simp [G,J],?_,inc⟩
  let f : C(closure S,ℂ) := ⟨_,continuousOn_iff_continuous_domRestrict.mp cA⟩
  obtain ⟨F,he⟩ := ContinuousMap.exists_restrict_eq isClosed_closure f
  have eqf : EqOn F A (closure S) := fun t ht => congrArg (fun g : C(closure S,ℂ) => g ⟨t,ht⟩) he
  intro p hp
  let K := fun z : ℂ => ∫ t in (0:ℝ)..1, F (AffineMap.lineMap p z t)
  have cK : Continuous K := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    simp only [Function.uncurry_def,AffineMap.lineMap_apply_module]
    fun_prop
  have val : K p = A p := by simp [K,eqf hp]
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  rw [← val]
  apply cK.continuousAt.continuousWithinAt.tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hC : z ∈ closure S := hz.1
  have hne : z ≠ p := hz.2
  have e : J p z = (z-p)*K z := by
    unfold J K
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact congrArg ((z-p)*·) (eqf (hs.closure.lineMap_mem hp hC ht)).symm
  rw [slope_def_field,inc p hp z hC,e]
  field_simp [sub_ne_zero.mpr hne]
end MomentSearch

namespace MomentSearch

/-- A primitive increment on an affine path in the normalization used for B. -/
theorem primitive_increment_affine (A G : ℂ → ℂ) (S : Set ℂ) (p d : ℂ)
    (inc : ∀ z ∈ S, G z-G p = ∫ t in (0:ℝ)..1, (z-p)*A (AffineMap.lineMap p z t))
    (t : ℝ) (ht : p+(t:ℂ)*d ∈ S) :
    G (p+(t:ℂ)*d)-G p = d * ∫ v in (0:ℝ)..t, A (p+(v:ℂ)*d) := by
  rw [inc _ ht,intervalIntegral.integral_const_mul]
  have path (v : ℝ) : AffineMap.lineMap p (p+(t:ℂ)*d) v =
      p+((t*v:ℝ):ℂ)*d := by
    rw [AffineMap.lineMap_apply_module',Complex.real_smul]
    push_cast; ring
  simp_rw [path]
  have changeVar := intervalIntegral.smul_integral_comp_mul_left
    (a := (0:ℝ)) (b := 1) (fun v : ℝ => A (p+(v:ℂ)*d)) t
  simp only [mul_zero,mul_one,Complex.real_smul] at changeVar
  rw [← changeVar]
  ring
end MomentSearch

namespace MomentSearch
open Filter
open scoped Topology

private theorem strip_closure (r : ℝ) (hr : 0 < r) :
    closure {z : ℂ | |z.re| < r} = {z : ℂ | |z.re| ≤ r} := by
  apply subset_antisymm
  · exact closure_minimal (fun z hz => (show |z.re| < r from hz).le)
      (isClosed_le Complex.continuous_re.abs continuous_const)
  intro z hz
  have ht : Tendsto (fun t : ℝ => (t:ℂ)*z) (𝓝[<] 1) (𝓝 z) := by
    simpa using (show Continuous (fun t : ℝ => (t:ℂ)*z) by fun_prop).continuousAt (x := (1:ℝ)) |>.continuousWithinAt
      (s := Iio (1:ℝ)) |>.tendsto
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 by norm_num))] with t ht h₀
  have h₁ : t < 1 := ht
  have hpos : 0 < t := h₀
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero, abs_mul,abs_of_pos hpos]
  change |z.re| ≤ r at hz
  exact (mul_le_mul_of_nonneg_left hz hpos.le).trans_lt (by nlinarith [mul_pos (sub_pos.mpr h₁) hr])

theorem equilibrium_density_continuous_closed_strip (r c : ℝ) (hc : 0 < c) :
    ContinuousOn (fun z : ℂ => Complex.arctan ((c:ℂ)*(((r:ℂ)^2-z^2)^(1/2:ℂ))))
      {z : ℂ | |z.re| ≤ r} := by
  intro z hz
  let v : ℂ := (r:ℂ)^2-z^2
  have hnorm := abs_le.mp (show |z.re| ≤ r from hz)
  have nn : 0 ≤ v.re := by
    simp [v,pow_two,Complex.mul_re]
    nlinarith [mul_nonneg (show 0 ≤ r-z.re by linarith [hnorm.2])
      (show 0 ≤ r+z.re by linarith [hnorm.1]),sq_nonneg z.im]
  have cv : ContinuousAt (fun z : ℂ => ((r:ℂ)^2-z^2)^(1/2:ℂ)) z :=
    (Complex.continuousAt_cpow_const_of_re_pos (Or.inl nn) (by norm_num : 0 < (1/2:ℂ).re)).comp
      (f := fun z : ℂ => (r:ℂ)^2-z^2) (by fun_prop)
  have ca : ContinuousAt (fun z : ℂ => (c:ℂ)*(((r:ℂ)^2-z^2)^(1/2:ℂ))) z := continuousAt_const.mul cv
  apply ContinuousAt.continuousWithinAt
  apply (show ContinuousAt Complex.arctan ((c:ℂ)*v^(1/2:ℂ)) from ?_).comp (f := fun z : ℂ => (c:ℂ)*(((r:ℂ)^2-z^2)^(1/2:ℂ))) ca
  rcases nn.eq_or_lt with e | hpos
  · have imz : z.im = 0 := by
      simp [v,pow_two,Complex.mul_re] at e
      nlinarith [mul_nonneg (show 0 ≤ r-z.re by linarith [hnorm.2])
        (show 0 ≤ r+z.re by linarith [hnorm.1]),sq_nonneg z.im]
    have zero : v = 0 := Complex.ext e.symm (by simp [v,pow_two,Complex.mul_im,imz])
    simp only [zero,Complex.zero_cpow (by norm_num : (1/2:ℂ) ≠ 0),mul_zero]
    exact arctan_continuousAt_zero
  · apply (hasDerivAt_complexArctan_of_re_pos _ ?_).continuousAt
    simpa [Complex.mul_re] using mul_pos hc (half_power_pos_re hpos)
end MomentSearch

namespace MomentSearch

/-- A phase primitive with its value fixed at the right endpoint. It extends
to both real vertices and its increments are the stated affine integrals. -/
theorem equilibrium_primitive_from_right (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    let S := {z : ℂ | |z.re| ≤ r}
    let A := fun z : ℂ => Complex.arctan ((c:ℂ)*(((r:ℂ)^2-z^2)^(1/2:ℂ)))
    ∃ G : ℂ → ℂ, G r = 0 ∧ (∀ z ∈ S, HasDerivWithinAt G (A z) S z) ∧
      ∀ p ∈ S, ∀ d : ℂ, ∀ t : ℝ, p+(t:ℂ)*d ∈ S →
        G (p+(t:ℂ)*d)-G p = d * ∫ v in (0:ℝ)..t, A (p+(v:ℂ)*d) := by
  intro S A
  let U := {z : ℂ | |z.re| < r}
  have cl : closure U = S := strip_closure r hr
  have conv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    change |(a • x + b • y).re| < r
    simp only [Complex.add_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    exact abs_lt.mpr ((convex_Ioo (-r) r)
      (show x.re ∈ Ioo (-r) r from abs_lt.mp (show |x.re| < r from hx))
      (show y.re ∈ Ioo (-r) r from abs_lt.mp (show |y.re| < r from hy)) ha hb hab)
  have hd : DifferentiableOn ℂ A U := (equilibrium_density_on_strip r c hc).1
  have co : ContinuousOn A (closure U) := cl ▸ equilibrium_density_continuous_closed_strip r c hc
  have mem : (r:ℂ) ∈ closure U := by rw [cl]; exact (abs_of_pos hr).le
  obtain ⟨G,hG,dG,inc⟩ := primitive_on_convex_closure conv hd co mem
  rw [cl] at dG inc
  exact ⟨G,hG,dG,fun p hp d t ht => primitive_increment_affine A G S p d (inc p hp) t ht⟩

end MomentSearch

namespace MomentSearch

theorem equilibrium_density_at_real (r c x : ℝ) (hx : |x| ≤ r) :
    Complex.arctan ((c:ℂ)*(((r:ℂ)^2-(x:ℂ)^2)^(1/2:ℂ))) =
      (Real.arctan (c*Real.sqrt (r^2-x^2)):ℂ) := by
  have hab := abs_le.mp hx
  have hv : 0 ≤ r^2-x^2 := by nlinarith [mul_nonneg (show 0 ≤ r-x by linarith) (show 0 ≤ r+x by linarith)]
  rw [Complex.ofReal_arctan,Complex.ofReal_mul,Real.sqrt_eq_rpow, Complex.ofReal_cpow hv]
  push_cast
  rfl

/-- The strip primitive agrees simultaneously with the complex side phase
and the real tail phase. -/
theorem equilibrium_primitive_side_base (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    let S := {z : ℂ | |z.re| ≤ r}
    let A := fun z : ℂ => Complex.arctan ((c:ℂ)*(((r:ℂ)^2-z^2)^(1/2:ℂ)))
    let s : ℂ := ⟨1/2,-Real.sqrt 3/2⟩
    let Z := fun t : ℝ => (r:ℂ)*(1-s*t)
    ∃ G : ℂ → ℂ, G r = 0 ∧ (∀ z ∈ S, HasDerivWithinAt G (A z) S z) ∧
      (∀ t ∈ Icc (0:ℝ) 2, G (Z t) = (-(r:ℂ)*s)*∫ u in (0:ℝ)..t, A (Z u)) ∧
      (∀ x ∈ Icc (-r) r, G x = -((∫ t in x..r, Real.arctan (c*Real.sqrt (r^2-t^2))):ℝ)) ∧
      ∀ p ∈ S, ∀ d : ℂ, ∀ t : ℝ, p+(t:ℂ)*d ∈ S →
        G (p+(t:ℂ)*d)-G p = d * ∫ v in (0:ℝ)..t, A (p+(v:ℂ)*d) := by
  intro S A s Z
  obtain ⟨G,zero,der,inc⟩ := equilibrium_primitive_from_right r c hr hc
  refine ⟨G,zero,der,?_,?_,inc⟩
  · intro t ht
    have path (v : ℝ) : (r:ℂ)+(v:ℂ)*(-(r:ℂ)*s) = Z v := by dsimp [Z]; ring
    have mem : Z t ∈ S := by
      change |(Z t).re| ≤ r
      simp [Z,s,Complex.mul_re,Complex.mul_im]
      rw [abs_of_pos hr,abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1-(2:ℝ)⁻¹*t)]
      nlinarith [mul_nonneg hr.le ht.1]
    have e := inc (r:ℂ) (show (r:ℂ) ∈ S from (abs_of_pos hr).le) (-(r:ℂ)*s) t (path t ▸ mem)
    simpa only [path,zero,sub_zero] using e
  · intro x hx
    have e := inc (x:ℂ) (show (x:ℂ) ∈ S from abs_le.mpr hx) (1:ℂ) (r-x)
      (by change |((x:ℂ)+((r-x:ℝ):ℂ)*1).re| ≤ r; simp [abs_of_pos hr])
    have eval : (x:ℂ)+((r-x:ℝ):ℂ) = (r:ℂ) := by push_cast; ring
    simp only [one_mul,mul_one] at e
    rw [eval,zero,zero_sub] at e
    have he : (∫ v in (0:ℝ)..r-x, A ((x:ℂ)+(v:ℂ))) =
        ∫ v in (0:ℝ)..r-x, (Real.arctan (c*Real.sqrt (r^2-(x+v)^2)):ℂ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le (by linarith [hx.2])] at hv
      simpa only [A,Complex.ofReal_add] using equilibrium_density_at_real r c (x+v) (abs_le.mpr
        ⟨by linarith [hx.1,hv.1],by linarith [hv.2]⟩)
    rw [he] at e
    have he' := intervalIntegral.integral_comp_add_left (fun t => (Real.arctan (c*Real.sqrt (r^2-t^2)):ℂ))
      (a := 0) (b := r-x) x
    simp only [add_zero,add_sub_cancel] at he'
    rw [he'] at e
    simp only [intervalIntegral,integral_complex_ofReal,← Complex.ofReal_sub] at e ⊢
    linear_combination -e
end MomentSearch

namespace MomentSearch
open scoped ComplexConjugate

private theorem arctan_conj_right {z : ℂ} (hz : 0 < z.re) :
    Complex.arctan (conj z) = conj (Complex.arctan z) := by
  let v := (1+z*Complex.I)/(1-z*Complex.I)
  have hn : 1-z*Complex.I ≠ 0 := by
    intro e
    have hi := congrArg Complex.im e
    simp at hi
    linarith
  have pos : 0 < v.im := by
    dsimp [v]; rw [Complex.div_im,← sub_div]
    apply div_pos _ (Complex.normSq_pos.mpr hn)
    simp [Complex.mul_im,Complex.mul_re]; linarith
  have hv : v.arg ≠ Real.pi := fun e => pos.ne' (Complex.arg_eq_pi_iff.mp e).2
  have hvc : (conj v).arg ≠ Real.pi := by
    intro e
    have h := (Complex.arg_eq_pi_iff.mp e).2
    simp only [Complex.conj_im,neg_eq_zero] at h
    exact pos.ne' h
  have eqn : (1+conj z*Complex.I)/(1-conj z*Complex.I) = (conj v)⁻¹ := by
    simp [v,map_div₀,map_add,Complex.conj_I,sub_eq_add_neg]
  change -Complex.I/2*Complex.log _ = conj (-Complex.I/2*Complex.log v)
  rw [eqn,Complex.log_inv _ hvc,Complex.log_conj _ hv]
  simp [show conj (2:ℂ) = 2 from map_ofNat _ 2]
  ring

theorem equilibrium_density_reflection (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    let A := fun z : ℂ => Complex.arctan ((c:ℂ)*(((r:ℂ)^2-z^2)^(1/2:ℂ)))
    ∀ z : ℂ, |z.re| ≤ r → A (-(conj z)) = conj (A z) := by
  intro A
  let S := {z : ℂ | |z.re| < r}
  have eq : EqOn (fun z => A (-(conj z))) (fun z => conj (A z)) S := by
    intro z hz
    let v := (r:ℂ)^2-z^2
    have he := abs_lt.mp (show |z.re| < r from hz)
    have pos : 0 < v.re := by
      simp [v,pow_two,Complex.mul_re]; nlinarith [mul_pos (show 0 < r-z.re by linarith [he.2])
        (show 0 < r+z.re by linarith [he.1]),sq_nonneg z.im]
    have ha : v.arg ≠ Real.pi := Complex.slitPlane_arg_ne_pi (Complex.mem_slitPlane_iff.mpr (Or.inl pos))
    have cpos : 0 < ((c:ℂ)*v^(1/2:ℂ)).re := by simpa [Complex.mul_re] using mul_pos hc (half_power_pos_re pos)
    have ve : (r:ℂ)^2-(-(conj z))^2 = conj v := by simp [v]
    dsimp only [A]
    rw [ve,Complex.conj_cpow _ _ ha]
    simpa [v,show conj (2:ℂ) = 2 from map_ofNat _ 2] using arctan_conj_right cpos
  have co : ContinuousOn A (closure S) := (strip_closure r hr) ▸ equilibrium_density_continuous_closed_strip r c hc
  have map : MapsTo (fun z : ℂ => -(conj z)) (closure S) (closure S) := by
    rw [show closure S = {z : ℂ | |z.re| ≤ r} from strip_closure r hr]
    intro z hz
    simpa using hz
  have cl := eq.of_subset_closure (co.comp (by fun_prop) map)
    (Complex.continuous_conj.comp_continuousOn co) subset_closure (Subset.rfl)
  intro z hz
  exact cl ((strip_closure r hr).symm ▸ hz)
end MomentSearch

namespace MomentSearch
open scoped ComplexConjugate

private theorem interval_conjugate (a b : ℝ) (f : ℝ → ℂ) :
    (∫ t in a..b, conj (f t)) = conj (∫ t in a..b, f t) := by
  simp only [intervalIntegral,integral_conj,map_sub]

/-- Reflection of a primitive increment across the imaginary axis. -/
theorem reflected_primitive_increment (r : ℝ) (hr : 0 < r) (A G : ℂ → ℂ)
    (hA : ∀ z : ℂ, |z.re| ≤ r → A (-(conj z)) = conj (A z))
    (inc : ∀ p : ℂ, |p.re| ≤ r → ∀ d : ℂ, ∀ t : ℝ, |(p+(t:ℂ)*d).re| ≤ r →
      G (p+(t:ℂ)*d)-G p = d * ∫ v in (0:ℝ)..t, A (p+(v:ℂ)*d))
    (z : ℂ) (hz : |z.re| ≤ r) :
    G (-(conj z))-G (-(r:ℂ)) = -(conj (G z-G r)) := by
  let d := z-(r:ℂ)
  have p (v : ℝ) : -(r:ℂ)+(v:ℂ)*(-(conj d)) = -(conj ((r:ℂ)+(v:ℂ)*d)) := by
    simp; ring
  have endp : (r:ℂ)+((1:ℝ):ℂ)*d = z := by dsimp [d]; ring
  have endm : -(r:ℂ)+((1:ℝ):ℂ)*(-(conj d)) = -(conj z) := by rw [p,endp]
  have pp := inc (r:ℂ) (by simpa using (abs_of_pos hr).le) d 1 (endp ▸ hz)
  have mm := inc (-(r:ℂ)) (by simpa using (abs_of_pos hr).le) (-(conj d)) 1
    (show |((-(r:ℂ))+((1:ℝ):ℂ)*(-(conj d))).re| ≤ r by rw [endm]; simpa using hz)
  rw [endp] at pp
  rw [endm] at mm
  rw [mm,pp,map_mul,← interval_conjugate]
  have reflected : (∫ v in (0:ℝ)..1, A (-(r:ℂ)+(v:ℂ)*(-(conj d)))) =
      ∫ v in (0:ℝ)..1, conj (A ((r:ℂ)+(v:ℂ)*d)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    change A _ = _
    rw [p]
    apply hA
    have hu := abs_le.mp hz
    simp [d,Complex.mul_re]
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hu.2),
      mul_nonneg hv.1 (show 0 ≤ r+z.re by linarith [hu.1]),
      mul_nonneg hr.le (sub_nonneg.mpr hv.2)]
  rw [reflected]; ring
end MomentSearch

namespace MomentSearch

/-- Nonnegative vertical derivative up to the sides of the strip. -/
theorem strip_primitive_im_nonnegative (r : ℝ) (A G : ℂ → ℂ)
    (hd : ∀ z : ℂ, |z.re| ≤ r → HasDerivWithinAt G (A z) {v : ℂ | |v.re| ≤ r} z)
    (hA : ∀ z : ℂ, |z.re| ≤ r → 0 ≤ (A z).re)
    (base : ∀ x : ℝ, |x| ≤ r → (G x).im = 0) :
    ∀ z : ℂ, |z.re| ≤ r → 0 ≤ z.im → 0 ≤ (G z).im := by
  intro z hz hi
  let γ := fun t : ℝ => (z.re:ℂ)+(t:ℂ)*Complex.I
  have mem (t : ℝ) : |(γ t).re| ≤ r := by simpa [γ] using hz
  have d (t : ℝ) : HasDerivAt (fun t => (G (γ t)).im) (A (γ t)).re t := by
    have path : HasDerivAt γ Complex.I t := by
      have e : HasDerivAt (fun u : ℂ => (z.re:ℂ)+u*Complex.I) Complex.I (t:ℂ) := by
        simpa using ((hasDerivAt_id' (t:ℂ)).mul_const Complex.I).const_add (z.re:ℂ)
      exact e.comp_ofReal
    have de := (hd _ (mem t)).scomp_hasDerivAt t path mem
    have di := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t de
    simpa [Function.comp_def,smul_eq_mul,Complex.I_mul_im] using di
  have mono := monotone_of_hasDerivAt_nonneg d (fun t => hA _ (mem t))
  have e := mono hi
  simpa [γ,base _ hz,Complex.re_add_im] using e

theorem equilibrium_density_nonnegative_closed_strip (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    let A := fun z : ℂ => Complex.arctan ((c:ℂ)*(((r:ℂ)^2-z^2)^(1/2:ℂ)))
    ∀ z : ℂ, |z.re| ≤ r → 0 ≤ (A z).re := by
  intro A
  let S := {z : ℂ | |z.re| ≤ r}
  have closed : IsClosed S := isClosed_le Complex.continuous_re.abs continuous_const
  have co : ContinuousOn (fun z => (A z).re) S :=
    Complex.continuous_re.comp_continuousOn (equilibrium_density_continuous_closed_strip r c hc)
  have subset : {z : ℂ | |z.re| < r} ⊆ {z ∈ S | 0 ≤ (A z).re} := fun z hz =>
    ⟨(show |z.re| < r from hz).le,((equilibrium_density_on_strip r c hc).2.1 z hz).le⟩
  have e := closure_minimal subset
    (co.preimage_isClosed_of_isClosed closed (isClosed_Ici (a := (0:ℝ))))
  rw [strip_closure r hr] at e
  intro z hz
  exact (e hz).2
end MomentSearch

namespace MomentSearch
open scoped ComplexConjugate

/-- Reparametrization between a unit segment and the side's affine coordinate. -/
private theorem edge_reparam (H : ℂ → ℂ) (p d : ℂ) (t : ℝ) :
    (∫ v in (0:ℝ)..1, (p+(t:ℂ)*d-p)*H (AffineMap.lineMap p (p+(t:ℂ)*d) v)) =
      ∫ v in (0:ℝ)..t, d*H (p+(v:ℂ)*d) := by
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have path (v : ℝ) : AffineMap.lineMap p (p+(t:ℂ)*d) v =
      p+((t*v:ℝ):ℂ)*d := by rw [AffineMap.lineMap_apply_module',Complex.real_smul]; push_cast; ring
  simp_rw [path]
  have e := intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := 1) (fun v : ℝ => H (p+(v:ℂ)*d)) t
  simp only [mul_zero,mul_one,Complex.real_smul] at e
  rw [← e]; ring

/-- Reflection and orientation for the regularized Cauchy integral. -/
theorem triangle_reflected_cauchy (r : ℝ) (p d w : ℂ)
    (S : Set ℂ) (hs : Convex ℝ S) (L : ℂ → ℂ)
    (hL : DifferentiableOn ℂ L S) (hw : w ∉ S)
    (hr : (r:ℂ) ∈ S) (hl : -(r:ℂ) ∈ S) (hp : p ∈ S)
    (he : (r:ℂ)+(2:ℂ)*d=p) (hsym : -(conj p)=p)
    (reflec : ∀ t ∈ Icc (0:ℝ) 2, L (-(conj ((r:ℂ)+(t:ℂ)*d))) = conj (L ((r:ℂ)+(t:ℂ)*d))) :
    let J := fun u : ℂ => ∫ t in (0:ℝ)..2, d*L ((r:ℂ)+(t:ℂ)*d)/(u-((r:ℂ)+(t:ℂ)*d))
    J w - conj (J (-(conj w))) = -(∫ t in (-r)..r, L t/(w-(t:ℂ))) := by
  intro J
  let H := fun z : ℂ => L z/(w-z)
  have dh : DifferentiableOn ℂ H S := fun z hz =>
    (hL z hz).div ((differentiableWithinAt_const w).sub differentiableWithinAt_id) (sub_ne_zero.mpr (fun e => hw (e ▸ hz)))
  let K := fun a b : ℂ => ∫ v in (0:ℝ)..1, (b-a)*H (AffineMap.lineMap a b v)
  have tri : K r (-r) + K (-r) p = K r p := triangle_segment_deformation hs dh hr hl hp
  have rr : K r p = J w := by
    have e := edge_reparam H (r:ℂ) d 2
    norm_num only [Complex.ofReal_ofNat] at e
    rw [he] at e
    simpa only [K,J,H,mul_div_assoc] using e
  have path (t : ℝ) : -(r:ℂ)+(t:ℂ)*(-(conj d)) = -(conj ((r:ℂ)+(t:ℂ)*d)) := by simp; ring
  have endm : -(r:ℂ)+((2:ℝ):ℂ)*(-(conj d)) = p := by rw [path]; norm_num only [Complex.ofReal_ofNat,he,hsym]
  have ll : K (-r) p = conj (J (-(conj w))) := by
    have e := edge_reparam H (-(r:ℂ)) (-(conj d)) 2
    rw [endm] at e
    rw [show K (-r) p = _ from e]
    unfold J
    rw [← interval_conjugate]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    dsimp only [H]
    rw [path,reflec t ht]
    simp only [map_div₀,map_mul,map_sub,map_neg,RingHomCompTriple.comp_apply,RingHom.id_apply, sub_neg_eq_add]
    rw [show -w - conj ((r:ℂ)+(t:ℂ)*d) = -(w+conj ((r:ℂ)+(t:ℂ)*d)) by ring]
    simp only [div_neg,neg_mul,mul_div_assoc]
  have bb : K r (-r) = -(∫ t in (-r)..r, H t) := by
    have e := edge_reparam H (r:ℂ) (1:ℂ) (-r-r)
    have ee : (r:ℂ)+((-r-r:ℝ):ℂ)*1 = -(r:ℂ) := by push_cast; ring
    rw [ee] at e
    simp only [one_mul,mul_one,← Complex.ofReal_add] at e
    have ch := intervalIntegral.integral_comp_add_left (fun t : ℝ => H t) (a := 0) (b := -r-r) r
    simp only [add_zero,add_sub_cancel] at ch
    rw [ch,intervalIntegral.integral_symm (a := -r) (b := r)] at e
    exact e
  rw [bb,ll,rr] at tri
  change _ = -(∫ t in (-r)..r, H t)
  linear_combination -tri
end MomentSearch

namespace MomentSearch
open scoped ComplexConjugate

theorem equilibrium_exponential_phase (r c N : ℝ) (hr : 0 < r) (hc : 0 < c) (hN : 0 < N)
    (m : ℕ) (total : N*(∫ t in (-r)..r, Real.arctan (c*Real.sqrt (r^2-t^2))) = Real.pi*m) :
    let S := {z : ℂ | |z.re| ≤ r}
    let A := fun z : ℂ => Complex.arctan ((c:ℂ)*(((r:ℂ)^2-z^2)^(1/2:ℂ)))
    let s : ℂ := ⟨1/2,-Real.sqrt 3/2⟩
    let Z := fun t : ℝ => (r:ℂ)*(1-s*t)
    ∃ u : ℂ → ℂ, Continuous u ∧ DifferentiableOn ℂ u S ∧
      (∀ z ∈ S, 0 ≤ z.im → ‖u z‖ ≤ 1) ∧
      (∀ z ∈ S, u (-(conj z)) = conj (u z)) ∧
      (∀ t ∈ Icc (0:ℝ) 2, u (Z t) =
        Complex.exp (-(2*Complex.I*(N:ℂ)*r*s * ∫ v in (0:ℝ)..t, A (Z v)))) ∧
      ∀ x ∈ Icc (-r) r, u x = Complex.exp (-2*Complex.I*(N:ℂ)*
        ((∫ t in x..r, Real.arctan (c*Real.sqrt (r^2-t^2))):ℝ)) := by
  intro S A s Z
  obtain ⟨G,h0,dG,side,base,inc⟩ := equilibrium_primitive_side_base r c hr hc
  have co : ContinuousOn G S := fun z hz => (dG z hz).continuousWithinAt
  let g : C(S,ℂ) := ⟨_,continuousOn_iff_continuous_domRestrict.mp co⟩
  have closed : IsClosed S := isClosed_le Complex.continuous_re.abs continuous_const
  obtain ⟨F,he⟩ := ContinuousMap.exists_restrict_eq closed g
  have eqF : EqOn F G S := fun z hz => congrArg (fun f : C(S,ℂ) => f ⟨z,hz⟩) he
  let C : ℂ := 2*Complex.I*(N:ℂ)
  let u := fun z => Complex.exp (C * F z)
  have dG' : DifferentiableOn ℂ G S := fun z hz => (dG z hz).differentiableWithinAt
  have dF : DifferentiableOn ℂ (F : ℂ → ℂ) S := DifferentiableOn.congr dG' eqF
  refine ⟨u,by dsimp [u]; fun_prop, ((differentiableOn_const C).mul dF).cexp, ?_,?_,?_,?_⟩
  · intro z hz hi
    have nn := strip_primitive_im_nonnegative r A G dG
      (equilibrium_density_nonnegative_closed_strip r c hr hc)
      (fun x hx => by rw [base x (abs_le.mp hx)]; simp) z hz hi
    rw [show u z = Complex.exp (C*G z) by rw [← eqF hz],Complex.norm_exp,Real.exp_le_one_iff]
    simp [C,Complex.mul_re,Complex.mul_im]
    nlinarith [mul_nonneg hN.le nn]
  · intro z hz
    have hmz : -(conj z) ∈ S := by simpa [S] using hz
    have reflG := reflected_primitive_increment r hr A G (equilibrium_density_reflection r c hr hc) inc z hz
    have e := base (-r) (left_mem_Icc.mpr (by linarith))
    rw [Complex.ofReal_neg] at e
    rw [h0,sub_zero] at reflG
    have Gs : G (-(conj z)) = G (-(r:ℂ)) - conj (G z) := by linear_combination reflG
    have et : C * G (-(r:ℂ)) = -(m:ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by
      rw [e]; dsimp [C]
      have h := congrArg Complex.ofReal total
      push_cast at h ⊢
      linear_combination -2*Complex.I*h
    have per : Complex.exp (C*G (-(r:ℂ))) = 1 := by
      rw [et,neg_mul,Complex.exp_neg,Complex.exp_nat_mul_two_pi_mul_I,inv_one]
    dsimp only [u]
    rw [eqF hmz,eqF hz,Gs,mul_sub,Complex.exp_sub,per,← Complex.exp_conj]
    simp [C,show conj (2:ℂ) = 2 from map_ofNat _ 2, ← neg_mul]
    rw [← Complex.exp_neg]
    congr 1
    ring
  · intro t ht
    have hz : Z t ∈ S := by
      change |(Z t).re| ≤ r
      simp [Z,s,Complex.mul_re,Complex.mul_im,abs_of_pos hr]
      rw [abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1-(2:ℝ)⁻¹*t)]
      nlinarith [mul_nonneg hr.le ht.1]
    dsimp only [u]
    rw [eqF hz,side t ht]
    congr 1
    dsimp only [C]; ring
  · intro x hx
    dsimp only [u]; rw [eqF (show (x:ℂ) ∈ S from abs_le.mpr hx),base x hx]
    congr 1
    dsimp [C]; ring
end MomentSearch

namespace MomentSearch
open Filter
open scoped Topology ComplexConjugate

private theorem abel_limit_compact_weight (a b : ℝ) (u W : ℝ → ℂ)
    (um : Measurable u) (wm : Measurable W) (wc : ContinuousOn W (uIcc a b))
    (hu : ∀ t ∈ uIcc a b, ‖u t‖ ≤ 1)
    (hne : ∀ᵐ t ∂volume, t ∈ uIoc a b → 1+u t ≠ 0)
    (hi : IntervalIntegrable (fun t => Real.log ‖1+u t‖) volume a b) :
    Tendsto (fun q : ℝ => ∫ t in a..b, W t * Complex.log (1+(q:ℂ)*u t))
      (𝓝[<] 1) (𝓝 (∫ t in a..b, W t * Complex.log (1+u t))) := by
  obtain ⟨p,hp,hmax⟩ := isCompact_uIcc.exists_isMaxOn ⟨a,left_mem_uIcc⟩ wc.norm
  exact abel_log_integral_limit a b u W um wm _ (norm_nonneg _)
    (fun t ht => hu t (uIoc_subset_uIcc ht)) (fun t ht => hmax (uIoc_subset_uIcc ht)) hne hi

theorem triangle_boundary_abel_limit (r : ℝ) (hr : 0 ≤ r) (d w : ℂ)
    (S : Set ℂ) (hs : Convex ℝ S) (u : ℂ → ℂ) (cu : Continuous u)
    (du : DifferentiableOn ℂ u S) (hu : ∀ z ∈ S, ‖u z‖ ≤ 1)
    (hw : w ∉ S) (hw' : -(conj w) ∉ S)
    (hb : ∀ t ∈ Icc (-r) r, (t:ℂ) ∈ S)
    (hz : ∀ t ∈ Icc (0:ℝ) 2, (r:ℂ)+(t:ℂ)*d ∈ S)
    (hpeak : -(conj ((r:ℂ)+2*d)) = (r:ℂ)+2*d)
    (reflec : ∀ t ∈ Icc (0:ℝ) 2, u (-(conj ((r:ℂ)+(t:ℂ)*d))) = conj (u ((r:ℂ)+(t:ℂ)*d)))
    (hside : ∀ t ∈ Icc (0:ℝ) 2, 1+u ((r:ℂ)+(t:ℂ)*d) ≠ 0)
    (hae : ∀ᵐ t ∂volume, t ∈ uIoc (-r) r → 1+u (t:ℂ) ≠ 0)
    (hi : IntervalIntegrable (fun t : ℝ => Real.log ‖1+u (t:ℂ)‖) volume (-r) r) :
    let L := fun z : ℂ => Complex.log (1+u z)
    let J := fun v : ℂ => ∫ t in (0:ℝ)..2, d*L ((r:ℂ)+(t:ℂ)*d)/(v-((r:ℂ)+(t:ℂ)*d))
    J w - conj (J (-(conj w))) = -(∫ t in (-r)..r, L t/(w-(t:ℂ))) := by
  intro L J
  let Z := fun t : ℝ => (r:ℂ)+(t:ℂ)*d
  let Lq := fun (q : ℝ) (z : ℂ) => Complex.log (1+(q:ℂ)*u z)
  let Jq := fun (v : ℂ) (q : ℝ) => ∫ t in (0:ℝ)..2, d*Lq q (Z t)/(v-Z t)
  have cZ : Continuous Z := by dsimp [Z]; fun_prop
  have sideLim (v : ℂ) (hv : v ∉ S) : Tendsto (Jq v) (𝓝[<] 1) (𝓝 (J v)) := by
    have W : ContinuousOn (fun t => d/(v-Z t)) (uIcc 0 2) := by
      rw [uIcc_of_le (by norm_num)]
      exact continuousOn_const.div (continuous_const.sub cZ).continuousOn
        (fun t ht => sub_ne_zero.mpr (fun e => hv (e ▸ hz t ht)))
    have cLog : ContinuousOn (fun t => Real.log ‖1+u (Z t)‖) (uIcc 0 2) := by
      rw [uIcc_of_le (by norm_num)]
      exact (continuous_const.add (cu.comp cZ)).norm.continuousOn.log
        (fun t ht => norm_ne_zero_iff.mpr (hside t ht))
    have out := abel_limit_compact_weight 0 2 (fun t => u (Z t)) (fun t => d/(v-Z t))
      (cu.comp cZ).measurable (by dsimp [Z]; fun_prop) W
      (by rw [uIcc_of_le (by norm_num)]; exact fun t ht => hu _ (hz t ht))
      (.of_forall (fun t ht => hside t (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] using uIoc_subset_uIcc ht)))
      cLog.intervalIntegrable
    simpa only [Jq,J,L,Lq,Z,mul_div_right_comm] using out
  have baseLim := abel_limit_compact_weight (-r) r (fun t : ℝ => u t) (fun t : ℝ => (1:ℂ)/(w-t))
    (cu.comp Complex.continuous_ofReal).measurable (by fun_prop)
    (by
      rw [uIcc_of_le (by linarith)]
      exact continuousOn_const.div (continuous_const.sub Complex.continuous_ofReal).continuousOn
        (fun t ht => sub_ne_zero.mpr (fun e => hw (e ▸ hb t ht))))
    (by rw [uIcc_of_le (by linarith)]; exact fun t ht => hu _ (hb t ht)) hae hi
  have right : Tendsto (fun q => -(∫ t in (-r)..r, Lq q t/(w-t))) (𝓝[<] 1)
      (𝓝 (-(∫ t in (-r)..r, L t/(w-t)))) := by
    simpa only [Lq,L,one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using baseLim.neg
  have left := (sideLim w hw).sub (Complex.continuous_conj.continuousAt.tendsto.comp (sideLim _ hw'))
  apply tendsto_nhds_unique (left.congr' ?_) right
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 by norm_num))] with q hq hp
  have slit (z : ℂ) (h : ‖u z‖ ≤ 1) : 1+(q:ℂ)*u z ∈ Complex.slitPlane := by
    have normle : ‖(q:ℂ)*u z‖ ≤ q := by simpa [norm_mul,abs_of_pos (show 0<q from hp)] using mul_le_mul_of_nonneg_left h (le_of_lt hp)
    have e := (abs_le.mp ((Complex.abs_re_le_norm _).trans normle)).1
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.add_re,Complex.one_re]
    linarith [show q<1 from hq]
  apply triangle_reflected_cauchy r _ d w S hs (Lq q) _ hw
    (hb r (right_mem_Icc.mpr (by linarith))) (by simpa using hb (-r) (left_mem_Icc.mpr (by linarith)))
    (hz 2 (by norm_num)) rfl hpeak
  · intro t ht
    dsimp only [Lq]
    rw [reflec t ht,← Complex.log_conj _ (Complex.slitPlane_arg_ne_pi (slit _ (hu _ (hz t ht))))]
    simp
  · exact fun z h => ((differentiableWithinAt_const (1:ℂ)).add ((du z h).const_mul (q:ℂ))).clog (slit z (hu z h))
end MomentSearch

namespace MomentSearch
open scoped ComplexConjugate

theorem cauchy_boundary_imaginary_part (r x h : ℝ) (hr : 0 ≤ r) (hh : 0 < h)
    (L : ℝ → ℂ) (F D : ℝ → ℝ) (J J' : ℂ)
    (meas : Measurable L) (hF : IntervalIntegrable F volume (-r) r)
    (hD : IntervalIntegrable D volume (-r) r)
    (trace : ∀ᵐ t ∂volume, t ∈ Ioc (-r) r →
      (L t).re = F t ∧ (L t).im = Real.pi*D t)
    (he : J-conj J' = -(∫ t in (-r)..r, L t/((x:ℂ)-(h:ℂ)*Complex.I-(t:ℂ)))) :
    (∫ t in (-r)..r, D t*((t-x)/((x-t)^2+h^2))) =
      (∫ t in (-r)..r, h/((x-t)^2+h^2)*F t)/Real.pi + J.im/Real.pi + J'.im/Real.pi := by
  let W := fun t : ℝ => (x:ℂ)-(h:ℂ)*Complex.I-(t:ℂ)
  let den := fun t : ℝ => (x-t)^2+h^2
  have hp (t : ℝ) : 0 < den t := by dsimp [den]; positivity
  have heq (t : ℝ) : Complex.normSq (W t) = den t := by
    simp [W,den,Complex.normSq_apply,pow_two,Complex.mul_re,Complex.mul_im]
  have hne (t : ℝ) : W t ≠ 0 := fun e => by have := hp t; rw [← heq,e] at this; simp at this
  have coK : Continuous (fun t => (t-x)/den t) :=
    (continuous_id.sub continuous_const).div (by dsimp [den]; fun_prop) (fun t => (hp t).ne')
  have coP : Continuous (fun t => h/den t) :=
    continuous_const.div (by dsimp [den]; fun_prop) (fun t => (hp t).ne')
  have iD := hD.mul_continuousOn coK.continuousOn
  have iF := hF.continuousOn_mul coP.continuousOn
  have order : -r ≤ r := by linarith
  have hL : IntervalIntegrable L volume (-r) r := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le order]
    apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le order).mp
      (hF.abs.add (hD.abs.const_mul Real.pi))).mono' meas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae trace] with t ht ht'
    obtain ⟨a,b⟩ := ht' ht
    simpa [a,b,abs_mul,abs_of_pos Real.pi_pos] using Complex.norm_le_abs_re_add_abs_im (L t)
  have iQ : IntervalIntegrable (fun t => L t/W t) volume (-r) r := by
    simp_rw [div_eq_mul_inv]
    apply hL.mul_continuousOn
    exact ((show Continuous W by dsimp [W]; fun_prop).inv₀ hne).continuousOn
  have imE := congrArg Complex.im he
  change (J-conj J').im = (-(∫ t in (-r)..r, L t/W t)).im at imE
  have comm : (∫ t in (-r)..r, L t/W t).im = ∫ t in (-r)..r, (L t/W t).im := by
    rw [intervalIntegral.integral_of_le order,intervalIntegral.integral_of_le order]
    exact (integral_im ((intervalIntegrable_iff_integrableOn_Ioc_of_le order).mp iQ)).symm
  simp only [Complex.sub_im,Complex.conj_im,sub_neg_eq_add,Complex.neg_im,comm] at imE
  have split : (∫ t in (-r)..r, (L t/W t).im) =
      (∫ t in (-r)..r, h/den t*F t) - Real.pi*(∫ t in (-r)..r, D t*((t-x)/den t)) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub iF (iD.const_mul Real.pi)]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [trace] with t ht
    intro hm
    rw [uIoc_of_le order] at hm
    obtain ⟨a,b⟩ := ht hm
    simp only [Complex.div_im,heq,a,b,W,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.mul_I_re,Complex.mul_I_im,neg_zero,zero_sub,sub_zero]
    ring
  rw [split] at imE
  change (∫ t in (-r)..r, D t*((t-x)/den t)) = (∫ t in (-r)..r, h/den t*F t)/Real.pi + J.im/Real.pi + J'.im/Real.pi
  rw [← add_div,← add_div,eq_div_iff Real.pi_ne_zero]
  linarith only [imE]
end MomentSearch

namespace MomentSearch
theorem norm_one_add_phase_exp (θ : ℝ) :
    ‖1 + Complex.exp (-2*Complex.I*(θ:ℂ))‖ = 2*|Real.cos θ| := by
  have factor : (1:ℂ)+Complex.exp (-2*Complex.I*(θ:ℂ)) =
      (2*(Real.cos θ:ℂ))*Complex.exp (-(θ:ℂ)*Complex.I) := by
    rw [Complex.ofReal_cos]
    dsimp [Complex.cos]
    rw [show -2*Complex.I*(θ:ℂ) = -(θ:ℂ)*Complex.I + -(θ:ℂ)*Complex.I by ring,Complex.exp_add]
    have e := Complex.exp_add ((θ:ℂ)*Complex.I) (-(θ:ℂ)*Complex.I)
    rw [show (θ:ℂ)*Complex.I + -(θ:ℂ)*Complex.I = 0 by ring,Complex.exp_zero] at e
    linear_combination e
  rw [factor,norm_mul,norm_mul,Complex.norm_exp]
  simp [-Complex.ofReal_cos]
end MomentSearch

open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
private theorem massIntegral (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (har : r^2+a^2=1) :
    (∫ x in (-r)..r, Real.arctan (Real.sqrt (r^2-x^2)/a)) = Real.pi*(1-a) := by
  let S (x : ℝ) := Real.sqrt (r^2-x^2)
  let W (x : ℝ) := Real.sqrt (1-x^2)
  let A (x : ℝ) := Real.arctan (S x/a)
  let G (x : ℝ) := x*A x + Real.arcsin (a*x/(r*W x)) - a*Real.arcsin (x/r)
  have wpos (x : ℝ) (hx : x ∈ Icc (-r) r) : 0 < W x := by
    apply Real.sqrt_pos.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ r+x by linarith [hx.1]),sq_pos_of_pos ha]
  have cg : ContinuousOn G (Icc (-r) r) := by
    have d : ContinuousOn (fun x => a*x/(r*W x)) (Icc (-r) r) :=
      (continuous_const.mul continuous_id).continuousOn.div
        (show Continuous (fun x => r*W x) by dsimp [W]; fun_prop).continuousOn
        (fun x hx => (mul_pos hr (wpos x hx)).ne')
    have ca : Continuous A := by dsimp [A,S]; fun_prop
    exact ((continuous_id.mul ca).continuousOn.add (Real.continuous_arcsin.comp_continuousOn d)).sub
      (show Continuous (fun x => a*Real.arcsin (x/r)) by fun_prop).continuousOn
  have dg (x : ℝ) (hx : x ∈ Ioo (-r) r) : HasDerivAt G (A x) x := by
    have hs0 : 0 < r^2-x^2 := by
      nlinarith [mul_pos (sub_pos.mpr hx.2) (show 0<r+x by linarith [hx.1])]
    have hs : 0 < S x := Real.sqrt_pos.mpr hs0
    have hw := wpos x ⟨hx.1.le,hx.2.le⟩
    have hss : S x ^ 2 = r^2-x^2 := Real.sq_sqrt hs0.le
    have hww : W x ^ 2 = 1-x^2 := Real.sq_sqrt (Real.sqrt_pos.mp hw).le
    have hden : r^2*(W x)^2 - (a*x)^2 = (S x)^2 := by
      rw [hww,hss]
      linear_combination -x^2*har
    have ds : HasDerivAt S (-x/S x) x := by
      convert! (((hasDerivAt_id x).pow 2).const_sub (r^2)).sqrt hs0.ne' using 1
      dsimp [S]; ring
    have dw : HasDerivAt W (-x/W x) x := by
      convert! (((hasDerivAt_id x).pow 2).const_sub 1).sqrt (Real.sqrt_pos.mp hw).ne' using 1
      dsimp [W]; ring
    have da : HasDerivAt A (-a*x/(S x * W x^2)) x := by
      convert! (Real.hasDerivAt_arctan (S x/a)).comp x (ds.div_const a) using 1
      have hd : a^2 + (S x)^2 = (W x)^2 := by linarith
      field_simp [ha.ne',hs.ne',hw.ne']
      linear_combination -x*hd
    have dq : HasDerivAt (fun u => a*u/(r*W u)) (a/(r*W x^3)) x := by
      convert! (((hasDerivAt_id x).const_mul a).div (dw.const_mul r) (mul_pos hr hw).ne') using 1
      field_simp [hr.ne',hw.ne']
      simp only [id_eq]
      linear_combination -hww
    have root {u v : ℝ} (hv : 0<v) (h : 1-u^2=v^2) :
        u ≠ -1 ∧ u ≠ 1 ∧ Real.sqrt (1-u^2)=v := by
      exact ⟨by rintro rfl; nlinarith [sq_pos_of_pos hv],
        by rintro rfl; nlinarith [sq_pos_of_pos hv],by rw [h,Real.sqrt_sq hv.le]⟩
    obtain ⟨hq1,hq2,hq⟩ := root (u := a*x/(r*W x)) (div_pos hs (mul_pos hr hw)) (by
      field_simp [hr.ne',hw.ne']; linarith only [hden])
    obtain ⟨ht1,ht2,ht⟩ := root (u := x/r) (div_pos hs hr) (by
      field_simp [hr.ne']; linarith only [hss])
    have dg' := (((hasDerivAt_id x).mul da).add
      ((Real.hasDerivAt_arcsin hq1 hq2).comp x dq)).sub
      (((Real.hasDerivAt_arcsin ht1 ht2).comp x ((hasDerivAt_id x).div_const r)).const_mul a)
    convert! dg' using 1
    rw [hq,ht]
    simp only [id_eq,one_mul]
    field_simp [hr.ne',hs.ne',hw.ne']
    linear_combination a*hww
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show -r ≤ r by linarith)
    cg dg (Continuous.intervalIntegrable (u := A) (by dsimp [A,S]; fun_prop) ..)
  have wr : W r = a := by dsimp [W]; rw [show 1-r^2=a^2 by linarith,Real.sqrt_sq ha.le]
  have wr' : W (-r) = a := by simpa [W] using wr
  have ar : A r = 0 := by simp [A,S]
  have ar' : A (-r) = 0 := by simp [A,S]
  change (∫ x in (-r)..r, A x) = _
  rw [hint]
  dsimp only [G]
  rw [wr,wr',ar,ar',show a*r/(r*a)=1 by field_simp,show a*(-r)/(r*a)= -1 by field_simp]
  simp [hr.ne', Real.arcsin_neg, Real.arcsin_one]
  ring

private theorem phaseLogIntegrable (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ)^2/(N : ℝ)^2)
    let ρ : ℝ → ℝ := fun t => (N : ℝ)/Real.pi * Real.arctan ((N : ℝ)/k * Real.sqrt (r^2-t^2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    IntegrableOn (fun z => Real.log (2*|f z|)) (Ioc (-r) r) := by
  intro r ρ f
  obtain ⟨_,Y,_,_,hzero,g,hg,hprod⟩ := MomentSearch.rakhmanov_quantile_real_regularization N k hk hkN
  have hr1 : r ≤ 1 := by
    dsimp [r]; rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [div_nonneg (sq_nonneg (k:ℝ)) (sq_nonneg (N:ℝ))]⟩
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have sub : Icc (-r) r ⊆ Icc (-1:ℝ) 1 := Icc_subset_Icc (neg_le_neg hr1) hr1
  have logs (y : ℝ) : IntegrableOn (fun t : ℝ => Real.log |t-y|) (Ioc (-r) r) := by
    simp only [Real.log_abs]
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (show -r ≤ r by linarith)).mp
    convert! (intervalIntegral.intervalIntegrable_log' (a := -r-y) (b := r-y)).comp_sub_right y using 1 <;> ring
  have hi : IntegrableOn (fun t : ℝ => Real.log 2 + (∑ y ∈ Y, Real.log |t-y|) - Real.log (g t)) (Ioc (-r) r) :=
    ((integrableOn_const (by simp)).add (integrable_finsetSum _ (fun y _ => logs y))).sub
      (((hg.log (fun z hz => (hprod z hz).1.ne')).mono sub).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (μ := volume)
    (show ∀ᵐ t ∂volume, t ∉ Y from (compl_mem_ae_iff.mpr (Y.finite_toSet.measure_zero volume)))] with t ht hy
  have ht' := sub (Ioc_subset_Icc_self ht)
  have hf : f t ≠ 0 := fun he => hy ((hzero t ht').mpr he)
  have he := congrArg (fun v : ℝ => Real.log |v|) (hprod t ht').2
  change Real.log |∏ y ∈ Y, (t-y)| = Real.log |g t * f t| at he
  have hn (y : ℝ) (h : y ∈ Y) : |t-y| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr (fun e => hy (e ▸ h)))
  simp only [Finset.abs_prod,Real.log_prod hn,
    abs_mul,abs_of_pos (hprod t ht').1,Real.log_mul (hprod t ht').1.ne' (abs_ne_zero.mpr hf)] at he
  rw [Real.log_mul (by norm_num) (abs_ne_zero.mpr hf)]
  dsimp only at *
  linarith only [he]

private theorem triangle_one_add_ne (B : ℝ → ℂ)
    (hB : ContinuousOn B (Set.Icc 0 2))
    (hsector : ∀ t ∈ Set.Icc 0 2, Real.sqrt 3 * |(B t).im| ≤ (B t).re) :
    ∀ t ∈ Set.Icc (0:ℝ) 2, 1+Complex.exp (-(B t)) ≠ 0 := by
  let s := Real.sqrt 3
  have hs : 0 < s := by dsimp [s]; positivity
  have heB : ContinuousOn (fun t => (1 : ℂ) + Complex.exp (-(B t))) (Set.Icc 0 2) :=
    continuousOn_const.add (Complex.continuous_exp.comp_continuousOn hB.neg)
  have hpositive (t : ℝ) (ht : t ∈ Set.Icc 0 2) :
      0 < (1 + Complex.exp (-(B t))).re := by
    have hr0 : 0 ≤ (B t).re := (mul_nonneg hs.le (abs_nonneg _)).trans (hsector t ht)
    by_cases hz : 0 < (B t).re
    · have hq : Real.exp (-(B t).re) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have hc := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (B t).im)
        (Real.exp_pos (-(B t).re)).le
      simp only [Complex.add_re, Complex.one_re, Complex.exp_re, Complex.neg_re,
        Complex.neg_im, Real.cos_neg]
      linarith
    · have hr : (B t).re = 0 := le_antisymm (le_of_not_gt hz) hr0
      have hi : (B t).im = 0 := abs_eq_zero.mp (le_antisymm
        (nonpos_of_mul_nonpos_right (hr ▸ hsector t ht) hs) (abs_nonneg _))
      simp only [Complex.add_re, Complex.one_re, Complex.exp_re, Complex.neg_re,
        Complex.neg_im, hr, hi, neg_zero, Real.exp_zero, Real.cos_zero, mul_one]
      norm_num
  intro t ht e
  have hp := hpositive t ht
  rw [e] at hp; exact (lt_irrefl 0) hp
theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
    let Z : ℝ → ℂ := fun t => (r : ℂ) * (1 - s * t)
    let B : ℝ → ℂ := fun t => 2 * Complex.I * (N : ℂ) * r * s *
      ∫ v in (0 : ℝ)..t, Complex.arctan ((N : ℂ) / k *
        (((r : ℂ)^2 - (Z v)^2) ^ (1/2 : ℂ)))
    let E : ℝ → ℝ → ℝ := fun x h => (∫ t in (0 : ℝ)..2,
      Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s) /
        ((x : ℂ) - (h : ℂ)*Complex.I - Z t)).im / Real.pi
    let P : ℝ → ℝ → ℝ := fun x h => (∫ t in (-r)..r,
      h / ((x-t)^2+h^2) * Real.log (2*|f t|)) / Real.pi
    ∀ Y : Finset ℝ, Y.card = N-k → (∀ y ∈ Y, y ∈ Set.Ioo (-r) r) →
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, z ∈ Y ↔ f z = 0) →
      ∀ x h : ℝ, 0 < h →
        (∫ t in (-r)..r,
          ((∑ y ∈ Y, if t ≤ y then (1 : ℝ) else 0) - (∫ u in t..r, ρ u)) *
            ((t-x)/((x-t)^2+h^2))) = P x h + E x h + E (-x) h := by 
  classical
  intro r ρ f s Z B E P
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have cf : Continuous ρ := by dsimp [ρ]; fun_prop
  let F := fun u : ℝ => ∫ t in (-r)..u, ρ t
  have htot : F r = (N : ℝ) - k  := by
    let c : ℝ := (k:ℝ)/N
    have hc : 0 < c := div_pos hk' hN
    have hcr : c < 1 := (div_lt_one hN).mpr (by exact_mod_cast hkN)
    have hrdef : r = Real.sqrt (1-c^2) := by simp only [r,c,div_pow]
    have hv : 0 < 1-c^2 := by nlinarith [mul_pos (sub_pos.mpr hcr) (show 0<1+c by positivity)]
    have hr : 0 < r := hrdef ▸ Real.sqrt_pos.mpr hv
    have har : r^2+c^2=1 := by rw [hrdef, Real.sq_sqrt hv.le]; ring
    have hrat (z : ℝ) : (N:ℝ)/k*z = z/c := by dsimp [c]; field_simp
    dsimp [F,ρ]
    simp_rw [hrat]
    rw [intervalIntegral.integral_const_mul, massIntegral c r hc hr har]
    dsimp [c]; field_simp
  have hr1 : r ≤ 1 := by
    dsimp [r]
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [div_nonneg (sq_nonneg (k:ℝ)) (sq_nonneg (N:ℝ))]⟩
  have htail : (∫ t in r..1, ρ t) = 0 := by
    have hzero : Set.EqOn ρ (fun _ => 0) (Set.uIcc r 1) := by
      rw [Set.uIcc_of_le hr1]
      intro u hu
      have hr : 0 ≤ r := Real.sqrt_nonneg _
      have huv : r^2-u^2 ≤ 0 := by nlinarith [sq_le_sq' (by linarith [hu.1]) hu.1]
      simp [ρ, Real.sqrt_eq_zero_of_nonpos huv]
    simpa using intervalIntegral.integral_congr (μ := MeasureTheory.volume) hzero
  let m := N-k
  have hm : (m:ℝ) = (N:ℝ)-k := Nat.cast_sub hkN.le
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  let T := fun z : ℝ => ∫ u in z..1, ρ u
  have dt (z : ℝ) : HasDerivAt T (-ρ z) z :=
    intervalIntegral.integral_hasDerivAt_left (cf.intervalIntegrable z 1)
      cf.stronglyMeasurable.stronglyMeasurableAtFilter cf.continuousAt
  have ct : Continuous T := continuous_iff_continuousAt.mpr (fun z => (dt z).continuousAt)
  have tr : T r = 0 := htail
  have tl : T (-r) = m := by
    have eq := intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable (μ := volume) (-r) r) (cf.intervalIntegrable r 1)
    change (∫ t in (-r)..1, ρ t) = _; rw [← eq,htail,add_zero]; exact htot.trans hm.symm
  have pos (y : ℝ) (hy : y ∈ Ioo (-r) r) : 0 < ρ y := by
    have hv : 0 < r^2-y^2 := by nlinarith [mul_pos (sub_pos.mpr hy.2) (show 0<r+y by linarith [hy.1])]
    dsimp [ρ]; exact mul_pos (by positivity) (Real.arctan_pos.mpr (by positivity))
  have strict : StrictAntiOn T (Icc (-r) r) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc ..) ct.continuousOn
    intro z hz
    rw [interior_Icc] at hz
    rw [(dt z).deriv]
    exact neg_neg_of_pos (pos _ hz)
  let c : ℝ := (N:ℝ)/k
  let A₀ := fun t : ℝ => Real.arctan (c*Real.sqrt (r^2-t^2))
  have hc : 0 < c := div_pos hN hk'
  have hrp : 0 < r := by
    dsimp [r]; apply Real.sqrt_pos.mpr
    rw [← div_pow,sub_pos]
    simpa only [one_pow] using (sq_lt_sq₀ (div_nonneg hk'.le hN.le) zero_le_one).mpr ((div_lt_one hN).mpr (by exact_mod_cast hkN))
  have phase (x : ℝ) : (N:ℝ)*(∫ t in x..r, A₀ t) = Real.pi*T x := by
    have add := intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable (μ := volume) x r) (cf.intervalIntegrable r 1)
    change _ = Real.pi*(∫ t in x..1, ρ t)
    rw [← add,htail,add_zero]
    change _ = Real.pi*(∫ t in x..r, ((N:ℝ)/Real.pi)*A₀ t)
    rw [intervalIntegral.integral_const_mul]; field_simp
  have total : (N:ℝ)*(∫ t in (-r)..r,A₀ t) = Real.pi*m := by rw [phase,tl]
  obtain ⟨u,cu,du,nu,refu,side₀,base⟩ := MomentSearch.equilibrium_exponential_phase r c N hrp hc hN m total
  have side : ∀ t ∈ Icc (0:ℝ) 2, u (Z t) = Complex.exp (-(B t)) := by
    simpa only [Z,B,s,c,Complex.ofReal_div,Complex.ofReal_natCast] using side₀
  have bu (t : ℝ) (ht : t ∈ Icc (-r) r) :
      u t = Complex.exp (-2*Complex.I*((Real.pi*T t:ℝ):ℂ)) := by
    rw [base t ht,← phase]
    push_cast; congr 1; ring
  let S := {z : ℂ | |z.re| ≤ r ∧ 0 ≤ z.im}
  let d : ℂ := -(r:ℂ)*s
  have zp (t : ℝ) : (r:ℂ)+(t:ℂ)*d = Z t := by dsimp [Z,d]; ring
  have rangeZ (t : ℝ) (ht : t ∈ Icc (0:ℝ) 2) : Z t ∈ S := by
    change |(Z t).re| ≤ r ∧ 0 ≤ (Z t).im
    simp [Z,s,Complex.mul_re,Complex.mul_im,abs_of_pos hrp]
    constructor
    · rw [abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1-(2:ℝ)⁻¹*t)]
      nlinarith [mul_nonneg hr ht.1]
    · exact mul_nonpos_of_nonneg_of_nonpos hr (mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg 3)) (by norm_num)) ht.1)
  have conv : Convex ℝ S := by
    have re := (convex_Icc (-r) r).linear_preimage Complex.reCLM.toLinearMap
    have im := (convex_Ici (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap
    have sets : S = (Complex.reCLM ⁻¹' Icc (-r) r) ∩ (Complex.imCLM ⁻¹' Ici 0) := by
      ext z; exact and_congr abs_le Iff.rfl
    rw [sets]; exact re.inter im
  have peak : -(conj ((r:ℂ)+2*d)) = (r:ℂ)+2*d := by
    apply Complex.ext <;> simp [d,s,Complex.mul_re,Complex.mul_im]
    ring
  obtain ⟨_,_,_,_,_,_,sector⟩ := MomentSearch.rakhmanov_triangle_phase_geometry N k hk hkN
  change ∀ t ∈ Icc (0:ℝ) 2, Real.sqrt 3*|(B t).im| ≤ (B t).re at sector
  have nz := triangle_one_add_ne B (MomentSearch.rakhmanov_triangle_phase_geometry N k hk hkN).choose_spec.1 sector
  intro Y hcard hy hzero x h hh
  let W := (x:ℂ)-(h:ℂ)*Complex.I
  have hw : W ∉ S := fun e => (show ¬0 ≤ W.im by simpa [W] using hh) e.2
  have hw' : -(conj W) ∉ S := fun e => (show ¬0 ≤ (-(conj W)).im by simpa [W] using hh) e.2
  have hf (t : ℝ) (ht : t ∈ Icc (-r) r) : ‖1+u t‖ = 2*|f t| := by
    rw [bu t ht]; exact MomentSearch.norm_one_add_phase_exp _
  have sub : Icc (-r) r ⊆ Icc (-1:ℝ) 1 := Icc_subset_Icc (neg_le_neg hr1) hr1
  have aeN : ∀ᵐ t ∂volume, t ∉ Y := compl_mem_ae_iff.mpr (Y.finite_toSet.measure_zero volume)
  have ord : -r ≤ r := by linarith
  have ae0 : ∀ᵐ t ∂volume, t ∈ uIoc (-r) r → 1+u (t:ℂ) ≠ 0 := by
    filter_upwards [aeN] with t hn ht
    rw [uIoc_of_le ord] at ht
    have hi := Ioc_subset_Icc_self ht
    have hfn : f t ≠ 0 := fun e => hn ((hzero t (sub hi)).mpr e)
    exact norm_ne_zero_iff.mp ((hf t hi).trans_ne (mul_ne_zero (by norm_num) (abs_ne_zero.mpr hfn)))
  have iF : IntervalIntegrable (fun t => Real.log (2*|f t|)) volume (-r) r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ord).2 (phaseLogIntegrable N k hk hkN)
  have iLog : IntervalIntegrable (fun t : ℝ => Real.log ‖1+u t‖) volume (-r) r := by
    apply iF.congr
    intro t ht
    rw [uIoc_of_le ord] at ht
    simp only [hf t (Ioc_subset_Icc_self ht)]
  have edge := MomentSearch.triangle_boundary_abel_limit r hr d W S conv u cu
    (du.mono (fun z hz => hz.1)) (fun z hz => nu z hz.1 hz.2) hw hw'
    (fun t ht => ⟨abs_le.mpr ht,le_rfl⟩)
    (fun t ht => zp t ▸ rangeZ t ht) peak (fun t ht => refu _ ((zp t ▸ rangeZ t ht).1))
    (fun t ht => by rw [zp,side t ht]; exact nz t ht) ae0 iLog
  let L := fun t : ℝ => Complex.log (1+u t)
  let D := fun t : ℝ => (∑ y ∈ Y, if t ≤ y then (1:ℝ) else 0) - (∫ v in t..r,ρ v)
  have tail (t : ℝ) : (∫ v in t..r,ρ v) = T t := by
    have e := intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable (μ := volume) t r) (cf.intervalIntegrable r 1)
    simpa [T,htail] using e
  have trace : ∀ᵐ t ∂volume, t ∈ Ioc (-r) r → (L t).re = Real.log (2*|f t|) ∧ (L t).im = Real.pi*D t := by
    filter_upwards [aeN] with t hn ht
    have hi := Ioc_subset_Icc_self ht
    obtain ⟨hre,him⟩ := MomentSearch.quantile_log_trace_from_levels (-r) r ord m T ct.continuousOn strict tl tr Y hcard
      (fun v hv e => (hzero v (sub hv)).mpr e) t hi hn
    have e : L t = Complex.log (1+Complex.exp (-2*(Real.pi:ℂ)*(T t:ℂ)*Complex.I)) := by
      dsimp [L]; rw [bu t hi]; push_cast; congr 2; ring
    rw [e]; exact ⟨hre,by simpa only [D,tail] using him⟩
  have iD : IntervalIntegrable D volume (-r) r := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ord).2
    have each (y : ℝ) : IntegrableOn (fun t : ℝ => if t ≤ y then (1:ℝ) else 0) (Ioc (-r) r) :=
      (integrableOn_const (by simp)).indicator measurableSet_Iic
    exact (integrable_finsetSum Y (fun y _ => each y)).sub
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le ord).1 (ct.intervalIntegrable ..)).congr (by filter_upwards with t; exact (tail t).symm))
  let J := fun v : ℂ => ∫ t in (0:ℝ)..2, d*Complex.log (1+u (Z t))/(v-Z t)
  have ce : J W - conj (J (-(conj W))) = -(∫ t in (-r)..r,L t/(W-t)) := by
    simpa only [J,L,zp] using edge
  have res := MomentSearch.cauchy_boundary_imaginary_part r x h hr hh L _ D (J W) (J (-(conj W)))
    (by dsimp [L]; fun_prop) iF iD trace ce
  have sideE (a : ℝ) : (J ((a:ℂ)-(h:ℂ)*Complex.I)).im/Real.pi = E a h := by
    dsimp only [J,E]
    congr 2
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [side t ht,mul_comm d]
    rfl
  have ew : -(conj W) = ((-x:ℝ):ℂ)-(h:ℂ)*Complex.I := by simp [W]; ring
  rw [ew] at res
  exact (by simpa only [W,sideE,P,D] using res)
