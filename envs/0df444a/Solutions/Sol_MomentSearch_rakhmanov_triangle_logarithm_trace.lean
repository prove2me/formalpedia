-- Prove2me | solution 1 for MomentSearch.rakhmanov_triangle_logarithm_trace
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:38:16.426567+00:00
-- url     : https://prove2.me/submissions/cce13d1b-950a-49e9-8a04-85a4c0683aea

import Mathlib

/-!
# Logarithmic trace for the Rakhmanov triangle

The strip primitive extends the real quantile phase to the two sides of the
triangle. Abel regularization permits Cauchy deformation across the base and
dominated convergence at the nodal logarithmic singularities.
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

open scoped BigOperators
open Set
namespace MomentSearch

theorem one_add_exp_two_mul_I (a : ℝ) :
    (1 : ℂ) + Complex.exp (2 * (a : ℂ) * Complex.I) =
      (2 * Real.cos a : ℝ) * Complex.exp ((a : ℂ) * Complex.I) := by
  have e : Complex.exp (-(a : ℂ) * Complex.I) *
      Complex.exp ((a : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, show -(a : ℂ) * Complex.I + (a : ℂ) * Complex.I = 0 by ring,
      Complex.exp_zero]
  have s : Complex.exp ((a : ℂ) * Complex.I) *
      Complex.exp ((a : ℂ) * Complex.I) = Complex.exp (2 * (a : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos]
  rw [show -(a : ℂ) * Complex.I = -((a : ℂ) * Complex.I) by ring] at e
  unfold Complex.cos
  rw [show -(a : ℂ) * Complex.I = -((a : ℂ) * Complex.I) by ring]
  calc
    1 + Complex.exp (2 * (a : ℂ) * Complex.I) =
        (Complex.exp ((a : ℂ) * Complex.I) +
          Complex.exp (-((a : ℂ) * Complex.I))) * Complex.exp ((a : ℂ) * Complex.I) := by
      rw [add_mul, e, s, add_comm]
    _ = 2 * ((Complex.exp ((a : ℂ) * Complex.I) +
          Complex.exp (-((a : ℂ) * Complex.I))) / 2) * Complex.exp ((a : ℂ) * Complex.I) := by ring

/-- The principal logarithm of the real-axis trace in one half-mass cell. -/
theorem quantile_boundary_log (v : ℝ) (j : ℤ) (hj : |(j : ℝ) - v| < 1/2) :
    Complex.log (1 + Complex.exp (-2 * (Real.pi : ℂ) * (v : ℂ) * Complex.I)) =
      (Real.log (2 * |Real.cos (Real.pi * v)|) : ℂ) +
      ((Real.pi * ((j : ℝ) - v) : ℝ) : ℂ) * Complex.I := by
  let a := Real.pi * ((j : ℝ) - v)
  let b := -(Real.pi * v)
  have ha : a ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    have h := abs_lt.mp hj
    constructor <;> dsimp [a] <;> nlinarith [mul_lt_mul_of_pos_left h.1 Real.pi_pos,
      mul_lt_mul_of_pos_left h.2 Real.pi_pos]
  have hc := Real.cos_pos_of_mem_Ioo ha
  have hperiod : Complex.exp (2 * (a : ℂ) * Complex.I) =
      Complex.exp (2 * (b : ℂ) * Complex.I) := by
    have harg : 2 * (a : ℂ) * Complex.I =
        2 * (b : ℂ) * Complex.I + j * (2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [a,b]
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hnorm (x : ℝ) :
      ‖1 + Complex.exp (2 * (x : ℂ) * Complex.I)‖ = 2 * |Real.cos x| := by
    rw [one_add_exp_two_mul_I, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hab : 2 * Real.cos a = 2 * |Real.cos (Real.pi * v)| := by
    rw [← abs_of_pos hc, ← hnorm, hperiod, hnorm]
    simp [b]
  have harg' : 2 * (b : ℂ) * Complex.I = -2 * (Real.pi : ℂ) * (v : ℂ) * Complex.I := by
    dsimp [b]; push_cast; ring
  rw [← harg', ← hperiod, one_add_exp_two_mul_I, ← hab]
  change Complex.log _ = (Real.log (2 * Real.cos a) : ℂ) + (a : ℂ) * Complex.I
  have he : Complex.exp ((Real.log (2 * Real.cos a) : ℂ) + (a : ℂ) * Complex.I) =
      ((2 * Real.cos a : ℝ) : ℂ) * Complex.exp ((a : ℂ) * Complex.I) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (by positivity)]
  rw [← he]
  apply Complex.log_exp
  · simp; linarith [ha.1,Real.pi_pos]
  · simp; linarith [ha.2,Real.pi_pos]

/-- Away from the nodes, the tail quantile count is the unique nearest integer. -/
theorem quantile_tail_nearest_integer {a b : ℝ} (hab : a ≤ b)
    (T : ℝ → ℝ) (m : ℕ) (Y : Finset ℝ) (hc : ContinuousOn T (Icc a b))
    (hs : StrictAntiOn T (Icc a b)) (ha : T a = m) (hb : T b = 0)
    (hcard : Y.card = m)
    (hroot : ∀ y ∈ Icc a b, y ∈ Y ↔ Real.cos (Real.pi * T y) = 0)
    {t : ℝ} (ht : t ∈ Icc a b) (hout : t ∉ Y) :
    |(∑ y ∈ Y, if t ≤ y then (1:ℝ) else 0) - T t| < 1/2 := by
  classical
  have level (i : Fin m) : ∃ y ∈ Icc a b, T y = (i.val:ℝ)+1/2 := by
    have hi : (i.val:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast i.isLt
    apply intermediate_value_Icc' hab hc
    rw [ha,hb]
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i.val]
  choose y hy hlevel using level
  have inj : Function.Injective y := by
    intro i j he
    apply Fin.ext
    exact_mod_cast (show (i.val:ℝ) = j.val by linarith [hlevel i,hlevel j,congrArg T he])
  have hcos (j : ℤ) {v : ℝ} (hj : v = (j:ℝ)+1/2) : Real.cos (Real.pi*v) = 0 := by
    apply Real.cos_eq_zero_iff.mpr
    exact ⟨j,by rw [hj]; ring⟩
  have hyY (i : Fin m) : y i ∈ Y := by
    apply (hroot _ (hy i)).mpr
    exact hcos i.val (by push_cast; exact hlevel i)
  have himage : Y = Finset.univ.image y := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
      exact hyY i
    · rw [hcard,Finset.card_image_of_injective _ inj,Finset.card_univ, Fintype.card_fin]
  have hnon : 0 ≤ T t := hb ▸ hs.antitoneOn ht ⟨hab,le_rfl⟩ ht.2
  have hle : T t ≤ m := ha ▸ hs.antitoneOn ⟨le_rfl,hab⟩ ht ht.1
  let j := ⌊T t + 1/2⌋₊
  have hj0 : (j:ℝ) ≤ T t+1/2 := Nat.floor_le (by linarith)
  have hj1 : T t+1/2 < (j:ℝ)+1 := Nat.lt_floor_add_one _
  have hjm : j ≤ m := by
    have hh : (j:ℝ) < (m:ℝ)+1 := by linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast hh)
  have hj0' : (j:ℝ) < T t+1/2 := by
    apply lt_of_le_of_ne hj0
    intro he
    exact hout ((hroot _ ht).mpr (hcos ((j:ℤ)-1) (by push_cast; linarith)))
  have hind (i : Fin m) : t ≤ y i ↔ i.val < j := by
    have hv : t ≤ y i ↔ T (y i) ≤ T t := by
      constructor
      · exact hs.antitoneOn ht (hy i)
      · intro h
        by_contra! h'
        exact (not_lt_of_ge h) (hs (hy i) ht h')
    rw [hv,hlevel]
    constructor
    · intro h
      have h' : (i.val:ℝ) < (j:ℝ) := by linarith
      exact_mod_cast h'
    · intro h
      have h' : (i.val:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast h
      linarith
  have hfilter : ((Finset.range j).image (fun i =>
      if hi : i < m then y ⟨i,hi⟩ else a)) = Y.filter (fun z => t ≤ z) := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      have hij := Finset.mem_range.mp hi
      have him := hij.trans_le hjm
      simp only [dif_pos him,Finset.mem_filter]
      exact ⟨hyY ⟨i,him⟩,(hind ⟨i,him⟩).mpr hij⟩
    · intro hz
      obtain ⟨hzY,hzt⟩ := Finset.mem_filter.mp hz
      rw [himage] at hzY
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hzY
      exact Finset.mem_image.mpr ⟨i.val,Finset.mem_range.mpr ((hind i).mp hzt),by simp [i.isLt]⟩
  have heq : (Y.filter (fun z => t ≤ z)).card = j := by
    rw [← hfilter, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi l hl he
    have him := (Finset.mem_range.mp hi).trans_le hjm
    have hlm := (Finset.mem_range.mp hl).trans_le hjm
    simp only [dif_pos him,dif_pos hlm] at he
    exact congrArg Fin.val (inj he)
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one,heq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩


open MeasureTheory Filter

private theorem ae_not_in_finset (Y : Finset ℝ) : ∀ᵐ t ∂volume, t ∉ Y := by
  rw [ae_iff]
  simpa using Y.finite_toSet.measure_zero volume

private theorem intervalIntegrable_node_log {a b : ℝ} (y : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log (t-y)) volume a b := by
  convert (intervalIntegral.intervalIntegrable_log' (a := a-y) (b := b-y)).comp_sub_right y using 1 <;> ring_nf

/-- Factorization by the real quantile polynomial accounts for every logarithmic pole. -/
theorem intervalIntegrable_log_quantile {a b : ℝ} (hab : a ≤ b) (Y : Finset ℝ)
    (f g : ℝ → ℝ) (hg : ContinuousOn g (Icc a b))
    (hfactor : ∀ t ∈ Icc a b, 0 < g t ∧ (∏ y ∈ Y, (t-y)) = g t * f t) :
    IntervalIntegrable (fun t => Real.log (2*|f t|)) volume a b := by
  have lg : IntervalIntegrable (fun t => Real.log (g t)) volume a b :=
    (hg.log (fun t ht => (hfactor t ht).1.ne')).intervalIntegrable_of_Icc hab
  have hsum : IntervalIntegrable (fun t => ∑ y ∈ Y, Real.log (t-y)) volume a b := by
    have he : (fun t => ∑ y ∈ Y, Real.log (t-y)) =
        (∑ y ∈ Y, fun t => Real.log (t-y)) := by
      funext t; rw [Finset.sum_apply]
    rw [he]
    exact IntervalIntegrable.sum Y fun y _ => intervalIntegrable_node_log y
  refine (intervalIntegrable_const.add (hsum.sub lg) :
    IntervalIntegrable (fun t => Real.log 2 + ((∑ y ∈ Y, Real.log (t-y)) - Real.log (g t))) volume a b).congr_ae ?_
  have hu := ae_restrict_mem (μ := volume) (measurableSet_uIoc (a := a) (b := b))
  have hy := ae_restrict_of_ae (s := uIoc a b) (ae_not_in_finset Y)
  filter_upwards [hu,hy] with t ht hy
  have ht' : t ∈ Icc a b := by simpa [uIcc_of_le hab] using uIoc_subset_uIcc ht
  obtain ⟨pos,fact⟩ := hfactor t ht'
  have sub_ne (y : ℝ) (hy' : y ∈ Y) : t-y ≠ 0 := sub_ne_zero.mpr <| by
    intro h; exact hy (h ▸ hy')
  have hf : f t ≠ 0 := by
    intro h
    rw [h,mul_zero] at fact
    exact (Finset.prod_ne_zero_iff.mpr sub_ne) fact
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (abs_ne_zero.mpr hf), Real.log_abs,
    ← Real.log_prod sub_ne, fact, Real.log_mul pos.ne' hf]
  ring

/-- Output of the real-axis calculation, in the orientation of the base from left to right. -/
theorem quantile_base_trace {a b : ℝ} (hab : a ≤ b) (T g : ℝ → ℝ) (m : ℕ) (Y : Finset ℝ)
    (hc : Continuous T) (hs : StrictAntiOn T (Icc a b)) (ha : T a = m) (hb : T b = 0)
    (hcard : Y.card = m) (hroot : ∀ y ∈ Icc a b, y ∈ Y ↔ Real.cos (Real.pi * T y) = 0)
    (hg : ContinuousOn g (Icc a b))
    (hfactor : ∀ t ∈ Icc a b, 0 < g t ∧
      (∏ y ∈ Y, (t-y)) = g t * Real.cos (Real.pi * T t))
    (x h : ℝ) (hh : 0 < h) :
    let u := fun t : ℝ => Complex.exp (-2*(Real.pi:ℂ)*(T t:ℂ)*Complex.I)
    let D := fun t : ℝ => (∑ y ∈ Y, if t ≤ y then (1:ℝ) else 0) - T t
    IntervalIntegrable (fun t => Real.log ‖1+u t‖) volume a b ∧
    (∀ᵐ t ∂volume, t ∈ uIoc a b → 1+u t ≠ 0) ∧
    (∫ t in a..b, D t * ((t-x)/((x-t)^2+h^2))) =
      (∫ t in a..b, h/((x-t)^2+h^2) * Real.log (2*|Real.cos (Real.pi*T t)|))/Real.pi -
       (∫ t in a..b, Complex.log (1+u t)/((x:ℂ)-(h:ℂ)*Complex.I-(t:ℂ))).im/Real.pi := by
  intro u D
  let F := fun t : ℝ => Real.log (2*|Real.cos (Real.pi*T t)|)
  let W := fun t : ℝ => (x:ℂ)-(h:ℂ)*Complex.I-(t:ℂ)
  let Q := fun t : ℝ => (x-t)^2+h^2
  have norm_id (t : ℝ) : ‖1+u t‖ = 2*|Real.cos (Real.pi*T t)| := by
    let v := -(Real.pi*T t)
    have e : u t = Complex.exp (2*(v:ℂ)*Complex.I) := by
      dsimp [u,v]; push_cast; congr 1; ring
    rw [e,one_add_exp_two_mul_I,norm_mul, Complex.norm_exp_ofReal_mul_I,mul_one,
      Complex.norm_real, Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    simp [v]
  have Fint : IntervalIntegrable F volume a b :=
    intervalIntegrable_log_quantile hab Y _ g hg hfactor
  have ae_data : ∀ᵐ t ∂volume, t ∈ uIoc a b → t ∈ Icc a b ∧ t ∉ Y := by
    filter_upwards [ae_not_in_finset Y] with t hy ht
    exact ⟨by simpa [uIcc_of_le hab] using uIoc_subset_uIcc ht,hy⟩
  have hne : ∀ᵐ t ∂volume, t ∈ uIoc a b → 1+u t ≠ 0 := by
    filter_upwards [ae_data] with t hdata ht
    obtain ⟨ht',hy⟩ := hdata ht
    have hc' : Real.cos (Real.pi*T t) ≠ 0 := fun e => hy ((hroot t ht').mpr e)
    intro e
    have hn := norm_id t
    rw [e,norm_zero] at hn
    have hp := abs_pos.mpr hc'
    linarith
  refine ⟨by simpa only [norm_id] using Fint, hne, ?_⟩
  have hQ (t : ℝ) : 0 < Q t := by dsimp [Q]; positivity
  have hW (t : ℝ) : W t ≠ 0 := by
    intro e
    have e' := congrArg Complex.im e
    simp only [W,Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.I_im,Complex.I_re, Complex.ofReal_re,
      mul_one,zero_mul,add_zero,sub_zero,zero_sub,Complex.zero_im] at e'
    linarith
  have hlog : IntervalIntegrable (fun t => Complex.log (1+u t)) volume a b := by
    have hi := (Fint.abs.add (intervalIntegrable_const (c := Real.pi)))
    have hm : Measurable (fun t => Complex.log (1+u t)) :=
      Complex.measurable_log.comp ((continuous_const.add (by dsimp [u]; fun_prop)).measurable)
    rw [intervalIntegrable_iff] at hi ⊢
    apply hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro t
    have arg := Complex.abs_arg_le_pi (1+u t)
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add (by simp [Complex.log_re,norm_id,F]) (by simpa only [Complex.log_im] using arg))
  have hdiv : IntervalIntegrable (fun t => Complex.log (1+u t) / W t) volume a b := by
    simp_rw [div_eq_mul_inv]
    exact hlog.mul_continuousOn (((show Continuous W by dsimp [W]; fun_prop).inv₀ hW).continuousOn)
  have hspl : ∀ᵐ t ∂volume, t ∈ uIoc a b →
      (Complex.log (1+u t) / W t).im = (h/Q t)*F t - Real.pi*(D t*((t-x)/Q t)) := by
    filter_upwards [ae_data] with t hdata ht
    obtain ⟨ht',hy⟩ := hdata ht
    have hnear := quantile_tail_nearest_integer hab T m Y hc.continuousOn hs ha hb hcard hroot ht' hy
    let n : ℕ := (Y.filter fun y => t ≤ y).card
    have hn : (∑ y ∈ Y, if t ≤ y then (1:ℝ) else 0) = (n:ℝ) := by
      classical
      rw [← Finset.sum_filter, Finset.sum_const,nsmul_eq_mul,mul_one]
    have hcell := quantile_boundary_log (T t) (n:ℤ) (by simpa [hn] using hnear)
    change Complex.log (1+u t) = _ at hcell
    have re : (Complex.log (1 + u t)).re = F t := by
      rw [hcell]
      simp [F, Complex.mul_re]
    have im : (Complex.log (1 + u t)).im = Real.pi * D t := by
      rw [hcell]
      simp [D,n, Complex.mul_im]
    rw [Complex.div_im,re,im]
    simp only [W,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,mul_one,mul_zero,add_zero,sub_self,sub_zero,zero_sub]
    dsimp [Q]
    ring
  have hFin : IntervalIntegrable (fun t => (h/Q t)*F t) volume a b := by
    simp_rw [mul_comm (h/Q _) (F _)]
    exact Fint.mul_continuousOn ((continuous_const.div (by dsimp [Q]; fun_prop)
      (fun t => (hQ t).ne')).continuousOn)
  have hIm : IntervalIntegrable (fun t => (Complex.log (1+u t)/W t).im) volume a b :=
    intervalIntegrable_iff.mpr (Complex.imCLM.integrable_comp hdiv.def')
  have hTail : IntervalIntegrable (fun t => D t*((t-x)/Q t)) volume a b := by
    have aux := hFin.sub hIm
    have hh : (fun t => Real.pi*(D t*((t-x)/Q t))) =ᵐ[volume.restrict (uIoc a b)]
        (fun t => h/Q t*F t-(Complex.log (1+u t)/W t).im) := by
      filter_upwards [ae_restrict_of_ae (s := uIoc a b) hspl,
        ae_restrict_mem (μ := volume) measurableSet_uIoc] with t e ht
      linarith [e ht]
    have aux' := aux.congr_ae hh.symm
    convert aux'.const_mul Real.pi⁻¹ using 1
    ext t
    field_simp [Real.pi_ne_zero]
  have eq := intervalIntegral.integral_congr_ae hspl
  rw [intervalIntegral.integral_sub hFin (hTail.const_mul _),intervalIntegral.integral_const_mul] at eq
  have imint := Complex.imCLM.intervalIntegral_comp_comm hdiv
  change (∫ t in a..b, (Complex.log (1+u t)/W t).im) = _ at imint
  rw [imint] at eq
  change (∫ t in a..b, Complex.log (1+u t)/W t).im = _ at eq
  change (∫ t in a..b, D t*((t-x)/Q t)) =
      (∫ t in a..b, h/Q t*F t)/Real.pi -
        (∫ t in a..b, Complex.log (1+u t)/W t).im/Real.pi
  rw [← sub_div, eq]
  have he : (∫ t in a..b, h/Q t*F t) -
      ((∫ t in a..b, h/Q t*F t) - Real.pi * ∫ t in a..b, D t*((t-x)/Q t)) =
      Real.pi * ∫ t in a..b, D t*((t-x)/Q t) := by ring
  rw [he, mul_div_cancel_left₀ _ Real.pi_ne_zero]

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

open Filter MeasureTheory
open scoped Topology

private theorem regularQuotient (Y : Finset ℝ) (f : ℝ → ℝ) (cf : Continuous f)
    (roots : ∀ z ∈ Icc (-1:ℝ) 1, z ∈ Y ↔ f z = 0)
    (simple : ∀ y ∈ Y, f y = 0 ∧ HasDerivAt f (deriv f y) y ∧ deriv f y ≠ 0)
    (below : ∀ y ∈ Y, y < 1) (one : f 1 = 1) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc (-1:ℝ) 1) ∧
      ∀ z ∈ Icc (-1:ℝ) 1, 0 < g z ∧ (∏ y ∈ Y, (z-y)) = g z * f z := by
  classical
  let P := fun z => ∏ y ∈ Y, (z-y)
  let Q := fun y z => ∏ u ∈ Y.erase y, (z-u)
  let g := fun z => if z ∈ Y then Q z z / deriv f z else P z / f z
  have cp : Continuous P := by dsimp [P]; fun_prop
  have cq (y : ℝ) : Continuous (Q y) := by dsimp [Q]; fun_prop
  have prod (y : ℝ) (hy : y ∈ Y) (z : ℝ) : Q y z * (z-y) = P z :=
    Y.prod_erase_mul (fun t => z-t) hy
  have cg : ContinuousOn g (Icc (-1:ℝ) 1) := by
    intro y hy
    by_cases h : y ∈ Y
    · obtain ⟨hz,hd,hn⟩ := simple y h
      let D := Function.update (fun z => (f z-f y)/(z-y)) y (deriv f y)
      have cd : ContinuousAt D y := hd.continuousAt_div
      have hD : D y ≠ 0 := by simpa [D] using hn
      apply ContinuousAt.continuousWithinAt
      apply ((cq y).continuousAt.div cd hD).congr_of_eventuallyEq
      have hnb := (Y.erase y).finite_toSet.isClosed.isOpen_compl.mem_nhds
        (show y ∈ (↑(Y.erase y) : Set ℝ)ᶜ by simp)
      filter_upwards [hnb] with z hze
      by_cases e : z = y
      · subst z; simp [g,h,D]
      · have hnot : z ∉ Y := fun hY => hze (Finset.mem_erase.mpr ⟨e,hY⟩)
        simp only [g,if_neg hnot,Pi.div_apply,D,Function.update_of_ne e,hz,sub_zero,← prod y h z]
        rw [div_div_eq_mul_div]
    · have hn : f y ≠ 0 := fun he => h ((roots y hy).mpr he)
      apply ContinuousAt.continuousWithinAt
      apply (cp.continuousAt.div cf.continuousAt hn).congr_of_eventuallyEq
      filter_upwards [Y.finite_toSet.isClosed.isOpen_compl.mem_nhds h] with z hz
      simp [g,show z ∉ Y from hz]
  have nonzero (z : ℝ) (hz : z ∈ Icc (-1:ℝ) 1) : g z ≠ 0 := by
    by_cases h : z ∈ Y
    · simp only [g,if_pos h]
      exact div_ne_zero (Finset.prod_ne_zero_iff.mpr fun t ht =>
        sub_ne_zero.mpr (Finset.mem_erase.mp ht).1.symm) (simple z h).2.2
    · simp only [g,if_neg h]
      exact div_ne_zero (Finset.prod_ne_zero_iff.mpr fun t ht =>
        sub_ne_zero.mpr (fun e => h (e ▸ ht))) (fun he => h ((roots z hz).mpr he))
  have g1 : 0 < g 1 := by
    have h1 : (1:ℝ) ∉ Y := fun h => lt_irrefl _ (below 1 h)
    simpa [g,h1,one,P] using Finset.prod_pos (s := Y) (fun y hy => sub_pos.mpr (below y hy))
  refine ⟨g,cg,fun z hz => ⟨?_,?_⟩⟩
  · by_contra! hn
    obtain ⟨v,hv,he⟩ := intermediate_value_Icc hz.2 (cg.mono (Icc_subset_Icc_left hz.1))
      (show (0:ℝ) ∈ Icc (g z) (g 1) from ⟨hn,g1.le⟩)
    exact nonzero v ⟨hz.1.trans hv.1,hv.2⟩ he
  · by_cases h : z ∈ Y
    · rw [(simple z h).1,mul_zero]
      exact Finset.prod_eq_zero h (sub_self z)
    · change P z = _; simp [g,h,div_mul_cancel₀ _ (show f z ≠ 0 from fun he => h ((roots z hz).mpr he))]


/-- The real phase on the base, including its mass and the regular factor at the nodes. -/
theorem rakhmanov_real_phase (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ)^2/(N:ℝ)^2)
    let ρ := fun z : ℝ => (N:ℝ)/Real.pi * Real.arctan
      ((N:ℝ)/(k:ℝ)*Real.sqrt (r^2-z^2))
    let T := fun z : ℝ => ∫ t in z..r, ρ t
    let f := fun z : ℝ => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    0 < r ∧ r ≤ 1 ∧ Continuous T ∧ StrictAntiOn T (Icc (-r) r) ∧
    T (-r) = ((N-k:ℕ):ℝ) ∧ T r = 0 ∧
    (∀ t : ℝ, f t = Real.cos (Real.pi*T t)) ∧
    ∀ Y : Finset ℝ, (∀ y ∈ Y, y ∈ Ioo (-r) r) →
      (∀ t ∈ Icc (-1:ℝ) 1, t ∈ Y ↔ f t = 0) →
      ∃ g : ℝ → ℝ, ContinuousOn g (Icc (-r) r) ∧
        ∀ t ∈ Icc (-r) r, 0 < g t ∧ (∏ y ∈ Y, (t-y)) = g t * Real.cos (Real.pi*T t) := by
  intro r ρ T f
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  let c : ℝ := (k:ℝ)/N
  have hc : 0 < c := div_pos hk' hN
  have hcr : c < 1 := (div_lt_one hN).mpr (by exact_mod_cast hkN)
  have hrdef : r = Real.sqrt (1-c^2) := by simp only [r,c,div_pow]
  have hv : 0 < 1-c^2 := by nlinarith [mul_pos (sub_pos.mpr hcr) (show 0<1+c by positivity)]
  have hr : 0 < r := hrdef ▸ Real.sqrt_pos.mpr hv
  have har : r^2+c^2=1 := by rw [hrdef,Real.sq_sqrt hv.le]; ring
  have hr1 : r ≤ 1 := by nlinarith [sq_nonneg c]
  have cf : Continuous ρ := by dsimp [ρ]; fun_prop
  have htot : T (-r) = ((N-k:ℕ):ℝ) := by
    have hrat (z : ℝ) : (N:ℝ)/k*z = z/c := by dsimp [c]; field_simp
    dsimp [T,ρ]
    simp_rw [hrat]
    rw [intervalIntegral.integral_const_mul, massIntegral c r hc hr har, Nat.cast_sub hkN.le]
    dsimp [c]; field_simp
  have htail : (∫ t in r..1, ρ t) = 0 := by
    have hzero : Set.EqOn ρ (fun _ => 0) (Set.uIcc r 1) := by
      rw [Set.uIcc_of_le hr1]
      intro u hu
      have huv : r^2-u^2 ≤ 0 := by nlinarith [sq_le_sq' (by linarith [hu.1]) hu.1]
      simp [ρ,Real.sqrt_eq_zero_of_nonpos huv]
    simpa using intervalIntegral.integral_congr (μ := volume) hzero
  have dt (z : ℝ) : HasDerivAt T (-ρ z) z :=
    intervalIntegral.integral_hasDerivAt_left (cf.intervalIntegrable z r)
      cf.stronglyMeasurable.stronglyMeasurableAtFilter cf.continuousAt
  have ct : Continuous T := continuous_iff_continuousAt.mpr (fun z => (dt z).continuousAt)
  have pos (y : ℝ) (hy : y ∈ Ioo (-r) r) : 0 < ρ y := by
    have hv : 0 < r^2-y^2 := by nlinarith [mul_pos (sub_pos.mpr hy.2) (show 0<r+y by linarith [hy.1])]
    dsimp [ρ]; exact mul_pos (by positivity) (Real.arctan_pos.mpr (by positivity))
  have strict : StrictAntiOn T (Icc (-r) r) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc ..) ct.continuousOn
    intro z hz
    rw [interior_Icc] at hz
    rw [(dt z).deriv]
    exact neg_neg_of_pos (pos _ hz)
  have fT (z : ℝ) : f z = Real.cos (Real.pi*T z) := by
    dsimp [f,T]
    rw [← intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable z r) (cf.intervalIntegrable r 1),htail,add_zero]
  refine ⟨hr,hr1,ct,strict,htot,by simp [T],fT, ?_⟩
  intro Y hY hroot
  have hf : f = fun z => Real.cos (Real.pi*T z) := funext fT
  have df (z : ℝ) : HasDerivAt f _ z := hf ▸ ((dt z).const_mul Real.pi).cos
  have cf' : Continuous f := continuous_iff_continuousAt.mpr fun z => (df z).continuousAt
  have incl : Icc (-r) r ⊆ Icc (-1:ℝ) 1 := Icc_subset_Icc (by linarith) hr1
  obtain ⟨g,hg,hgf⟩ := regularQuotient Y f cf' hroot (by
    intro y hy
    have hfy := (hroot y (incl (Ioo_subset_Icc_self (hY y hy)))).mp hy
    have hd := df y
    refine ⟨hfy,hd.deriv ▸ hd,?_⟩
    rw [hd.deriv]
    change -Real.sin (Real.pi*T y) * (Real.pi * -ρ y) ≠ 0
    apply mul_ne_zero (neg_ne_zero.mpr ?_) (mul_ne_zero Real.pi_ne_zero (neg_ne_zero.mpr (pos y (hY y hy)).ne'))
    have e := Real.cos_eq_zero_iff_sin_eq.mp ((fT y) ▸ hfy)
    rcases e with e | e <;> rw [e] <;> norm_num)
    (fun y hy => (hY y hy).2.trans_le hr1) (by simp [f])
  refine ⟨g,hg.mono incl,fun t ht => ?_⟩
  simpa only [fT] using hgf t (incl ht)


open scoped ComplexConjugate

end MomentSearch

namespace MomentSearch
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate

/-- The analytic continuation of the real tail phase, normalized at the right vertex. -/
theorem rakhmanov_contour_phase (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ)^2/(N:ℝ)^2)
    let ρ := fun z : ℝ => (N:ℝ)/Real.pi * Real.arctan
      ((N:ℝ)/(k:ℝ)*Real.sqrt (r^2-z^2))
    let T := fun z : ℝ => ∫ t in z..r, ρ t
    let s : ℂ := ⟨1/2,-Real.sqrt 3/2⟩
    let Z := fun t : ℝ => (r:ℂ)*(1-s*t)
    let B := fun t : ℝ => (2*Complex.I*(N:ℂ)*r*s) *
      ∫ v in (0:ℝ)..t, Complex.arctan ((N:ℂ)/k*(((r:ℂ)^2-Z v^2)^(1/2:ℂ)))
    ∃ u : ℂ → ℂ, Continuous u ∧
      DifferentiableOn ℂ u {z : ℂ | z.re ∈ Ioo (-r) r ∧ 0 < z.im} ∧
      (∀ z : ℂ, z.re ∈ Icc (-r) r → 0 ≤ z.im → ‖u z‖ ≤ 1) ∧
      (∀ z : ℂ, z.re ∈ Icc (-r) r → 0 ≤ z.im → u (-conj z) = conj (u z)) ∧
      (∀ t ∈ Icc (-r) r, u (t:ℂ) = Complex.exp (-2*(Real.pi:ℂ)*(T t:ℂ)*Complex.I)) ∧
      ∀ t ∈ Icc (0:ℝ) 2, u (Z t) = Complex.exp (-(B t)) ∧ 1+u (Z t) ≠ 0 := by
  intro r ρ T s Z B
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  let c := (N:ℝ)/k
  have hc : 0 < c := div_pos hN hk'
  have hcc : ((c:ℝ):ℂ) = (N:ℂ)/k := by simp [c]
  obtain ⟨hr,_,_,_,htot,_,_,_⟩ := rakhmanov_real_phase N k hk hkN
  change 0 < r at hr
  change T (-r) = ((N-k:ℕ):ℝ) at htot
  let S := {z : ℂ | |z.re| ≤ r}
  let A := fun z : ℂ => Complex.arctan ((c:ℂ)*(((r:ℂ)^2-z^2)^(1/2:ℂ)))
  obtain ⟨G,Gzero,Gder,Ginc⟩ := equilibrium_primitive_from_right r c hr hc
  change G (r:ℂ) = 0 at Gzero
  change ∀ z ∈ S, HasDerivWithinAt G (A z) S z at Gder
  change ∀ p ∈ S, ∀ d : ℂ, ∀ t : ℝ, p+(t:ℂ)*d ∈ S →
    G (p+(t:ℂ)*d)-G p = d * ∫ v in (0:ℝ)..t, A (p+(v:ℂ)*d) at Ginc
  have Gbase (t : ℝ) (ht : t ∈ Icc (-r) r) :
      G (t:ℂ) = -(Real.pi/(N:ℝ)*(T t):ℝ) := by
    have he := Ginc t (by exact abs_le.mpr ht) 1 (r-t)
      (by change |((t:ℂ)+((r-t:ℝ):ℂ)*1).re| ≤ r; simp [abs_of_pos hr])
    have er : (t:ℂ)+((r-t:ℝ):ℂ) = (r:ℂ) := by push_cast; ring
    simp only [one_mul,mul_one] at he
    rw [er,Gzero,zero_sub] at he
    have he' : (∫ v in (0:ℝ)..r-t, A ((t:ℂ)+(v:ℂ))) =
        ∫ v in (0:ℝ)..r-t, Complex.ofReal (Real.arctan (c*Real.sqrt (r^2-(t+v)^2))) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le (by linarith [ht.2])] at hv
      simpa only [A,Complex.ofReal_add] using equilibrium_density_at_real r c (t+v) (abs_le.mpr
        ⟨by linarith [ht.1,hv.1],by linarith [hv.2]⟩)
    rw [he'] at he
    have he'' := intervalIntegral.integral_comp_add_left (fun v =>
      Complex.ofReal (Real.arctan (c*Real.sqrt (r^2-v^2)))) (a := 0) (b := r-t) t
    rw [add_zero,add_sub_cancel] at he''
    rw [he'',intervalIntegral.integral_ofReal] at he
    have Tscale : Real.pi/(N:ℝ)*T t = ∫ v in t..r, Real.arctan (c*Real.sqrt (r^2-v^2)) := by
      dsimp [T,ρ,c]
      rw [intervalIntegral.integral_const_mul]
      field_simp [Real.pi_ne_zero,hN.ne']
    rw [Tscale]
    exact neg_eq_iff_eq_neg.mp he
  have Gim (z : ℂ) (hz : z ∈ S) (hi : 0 ≤ z.im) : 0 ≤ (G z).im := by
    apply strip_primitive_im_nonnegative r A G Gder
      (equilibrium_density_nonnegative_closed_strip r c hr hc) _ z hz hi
    intro t ht
    rw [Gbase _ (abs_le.mp ht)]
    simp
  let U := fun z : ℂ => Complex.exp (2*Complex.I*(N:ℂ)*G z)
  have cG : ContinuousOn G S := fun z hz => (Gder z hz).continuousWithinAt
  have cU : ContinuousOn U S := (continuousOn_const.mul cG).cexp
  have Sclosed : IsClosed S := isClosed_le Complex.continuous_re.abs continuous_const
  let F : C(S,ℂ) := ⟨_,continuousOn_iff_continuous_domRestrict.mp cU⟩
  obtain ⟨u,hu⟩ := ContinuousMap.exists_restrict_eq Sclosed F
  have eu : EqOn u U S := fun z hz => congrArg (fun f : C(S,ℂ) => f ⟨z,hz⟩) hu
  refine ⟨u,u.continuous,?_,?_,?_,?_,?_⟩
  · let V := {z : ℂ | z.re ∈ Ioo (-r) r ∧ 0 < z.im}
    have hv : V ⊆ S := fun z hz => abs_le.mpr ⟨hz.1.1.le,hz.1.2.le⟩
    apply DifferentiableOn.congr _ (eu.mono hv)
    intro z hz
    exact (((Gder z (hv hz)).mono hv).const_mul (2*Complex.I*(N:ℂ))).cexp.differentiableWithinAt
  · intro z hz hi
    have hz' : z ∈ S := abs_le.mpr hz
    rw [eu hz',show ‖U z‖ = Real.exp (-2*(N:ℝ)*(G z).im) by
      simp only [U,Complex.norm_exp]
      congr 1
      simp [Complex.mul_re,Complex.mul_im]]
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hN.le (Gim z hz' hi)])
  · intro z hz _hi
    have hz' : z ∈ S := abs_le.mpr hz
    have hzr : -conj z ∈ S := by change |(-conj z).re| ≤ r; simpa using (show |z.re| ≤ r from hz')
    rw [eu hz', eu hzr]
    have hrfl := reflected_primitive_increment r hr A G
      (equilibrium_density_reflection r c hr hc) Ginc z hz'
    rw [Gzero,sub_zero] at hrfl
    have left : -(r:ℂ) = ((-r:ℝ):ℂ) := by simp
    have hleft := Gbase (-r) ⟨le_rfl,by linarith⟩
    rw [← left,htot] at hleft
    have hg : G (-conj z) = G (-(r:ℂ)) - conj (G z) := by linear_combination hrfl
    dsimp [U]
    rw [hg,hleft]
    have e : 2*Complex.I*(N:ℂ) * (-↑(Real.pi/↑N*↑(N-k:ℕ)) - conj (G z)) =
        -(↑((N-k:ℕ):ℤ) * (2*(Real.pi:ℂ)*Complex.I)) +
          conj (2*Complex.I*(N:ℂ)*G z) := by
      simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast,
        map_mul,Complex.conj_I, map_ofNat, map_natCast]
      push_cast
      have hn : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp [hn]
      ring
    rw [e,Complex.exp_add,Complex.exp_neg,Complex.exp_int_mul_two_pi_mul_I,inv_one,one_mul,Complex.exp_conj]
  · intro t ht
    rw [eu (show (t:ℂ) ∈ S from abs_le.mpr ht)]
    simp only [U,Gbase t ht]
    push_cast
    congr 1
    field_simp [show (N:ℂ) ≠ 0 by exact_mod_cast hN.ne']
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht2 : t ≤ 2 := ht.2
    have Zre : (Z t).re = r*(1-t/2) := by
      simp only [Z,s,Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,zero_mul,sub_zero]
      ring
    have Zim : (Z t).im = r*(Real.sqrt 3*t/2) := by
      simp only [Z,s,Complex.mul_im,Complex.sub_im,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,zero_mul,add_zero,zero_add,zero_sub]
      ring
    have hz : Z t ∈ S := by
      change |(Z t).re| ≤ r
      rw [Zre,abs_le]
      exact ⟨by nlinarith [mul_nonneg hr.le (show 0 ≤ 1-t/2 by linarith)],
        by nlinarith [mul_nonneg hr.le ht0]⟩
    have Zaffine (v : ℝ) : (r:ℂ)+(v:ℂ)*(-(r:ℂ)*s) = Z v := by dsimp [Z]; ring
    have ge := Ginc r (by change |r| ≤ r; exact (abs_of_pos hr).le) (-(r:ℂ)*s) t (Zaffine t ▸ hz)
    simp only [Zaffine,Gzero,sub_zero] at ge
    refine ⟨?_,?_⟩
    · rw [eu hz]
      dsimp [U,B]
      rw [ge]
      simp only [A,hcc]
      congr 1
      ring
    by_cases et : t = 0
    · subst t
      have ez : Z 0 = (r:ℂ) := by simp [Z]
      rw [ez] at hz
      rw [ez,eu hz]
      norm_num [U,Gzero]
    · have htpos := lt_of_le_of_ne ht0 (Ne.symm et)
      have hr' : |(Z t).re| < r := by
        rw [Zre,abs_lt]
        exact ⟨by nlinarith [mul_nonneg hr.le (show 0 ≤ 1-t/2 by linarith)],
          by nlinarith [mul_pos hr htpos]⟩
      have hi : 0 < (Z t).im := by rw [Zim]; positivity
      have inc : {z : ℂ | |z.re| < r} ⊆ S := fun z hz => (show |z.re| < r from hz).le
      have pr := vertical_primitive_im_strictMono r (Z t).re hr'
        (fun z hz => (Gder z (inc hz)).mono inc) (equilibrium_density_on_strip r c hc).2.1
      have cast : ((Z t).re:ℂ)+(Z t).im*Complex.I = Z t := Complex.re_add_im _
      have g0 : (G ((Z t).re:ℂ)).im = 0 := by
        rw [Gbase _ (abs_le.mp hr'.le)]
        simp
      have im0 := pr hi
      simp only [Complex.ofReal_zero,zero_mul,add_zero,g0,cast] at im0
      have bound : ‖u (Z t)‖ < 1 := by
        rw [eu hz]
        simp only [U,Complex.norm_exp, Real.exp_lt_one_iff]
        simp [Complex.mul_re,Complex.mul_im]
        nlinarith [mul_pos hN im0]
      intro e
      have v : u (Z t) = -1 := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using e)
      rw [v,norm_neg,norm_one] at bound
      exact (lt_irrefl _ bound)

end MomentSearch


namespace MomentSearch
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate

/-- The open upper half of the strip has the expected closure, including the real base. -/
theorem upper_strip_closure (r : ℝ) (hr : 0 < r) :
    closure {z : ℂ | z.re ∈ Ioo (-r) r ∧ 0 < z.im} =
      {z : ℂ | z.re ∈ Icc (-r) r ∧ 0 ≤ z.im} := by
  let S := {z : ℂ | z.re ∈ Ioo (-r) r ∧ 0 < z.im}
  let C := {z : ℂ | z.re ∈ Icc (-r) r ∧ 0 ≤ z.im}
  have hC : IsClosed C :=
    ((isClosed_Icc.preimage Complex.continuous_re).inter (isClosed_Ici.preimage Complex.continuous_im))
  have incl : S ⊆ C := by
    intro z hz; exact ⟨⟨hz.1.1.le,hz.1.2.le⟩,hz.2.le⟩
  change closure S = C
  apply subset_antisymm (closure_minimal incl hC)
  intro z hz
  have ht : Tendsto (fun q : ℝ => (q:ℂ)*z+(1-(q:ℂ))*Complex.I) (𝓝[<] 1) (𝓝 z) := by
    simpa using (show Continuous (fun q : ℝ => (q:ℂ)*z+(1-(q:ℂ))*Complex.I) by fun_prop).continuousAt (x := (1:ℝ)) |>.continuousWithinAt
      (s := Iio (1:ℝ)) |>.tendsto
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (0:ℝ)<1 by norm_num))] with q hq hq0
  have hq1 : q < 1 := hq
  have hp : 0 < q := hq0
  change ((q:ℂ)*z+(1-(q:ℂ))*Complex.I).re ∈ Ioo (-r) r ∧
    0 < (((q:ℂ)*z+(1-(q:ℂ))*Complex.I)).im
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.sub_im,Complex.one_im,mul_zero,zero_mul,sub_zero,
    mul_one,add_zero]
  have hl := mul_le_mul_of_nonneg_left hz.1.1 hp.le
  have hR := mul_le_mul_of_nonneg_left hz.1.2 hp.le
  refine ⟨⟨by nlinarith [mul_pos hr (sub_pos.mpr hq1)],by nlinarith [mul_pos hr (sub_pos.mpr hq1)]⟩,?_⟩
  simp [Complex.add_im,Complex.mul_im]
  linarith [mul_nonneg hp.le hz.2]

/-- Cauchy deformation continues to hold at the Abel limit on each of the three edges. -/
theorem triangle_log_deformation_limit {S : Set ℂ} (hs : Convex ℝ S)
    (u : ℂ → ℂ) (du : DifferentiableOn ℂ u S) (uco : Continuous u)
    (hu : ∀ z ∈ closure S, ‖u z‖ ≤ 1)
    (w : ℂ) (d : ℝ) (hp : 0 < d) (hw : ∀ z ∈ closure S, d ≤ ‖w-z‖)
    (a b c : ℂ) (ha : a ∈ closure S) (hb : b ∈ closure S) (hc : c ∈ closure S) :
    let e := fun p q : ℂ => AffineMap.lineMap p q
    let ok := fun p q : ℂ =>
      (∀ᵐ t ∂volume, t ∈ uIoc (0:ℝ) 1 → 1+u (e p q t) ≠ 0) ∧
      IntervalIntegrable (fun t => Real.log ‖1+u (e p q t)‖) volume 0 1
    let J := fun p q : ℂ => ∫ t in (0:ℝ)..1, (q-p)*Complex.log (1+u (e p q t))/(w-e p q t)
    ok a b → ok a c → ok b c → J a b + J b c = J a c := by
  intro e ok J oab oac obc
  let H := fun q : ℝ => fun z : ℂ => Complex.log (1+(q:ℂ)*u z)/(w-z)
  let K := fun q : ℝ => fun p v : ℂ => ∫ t in (0:ℝ)..1, (v-p)*H q (e p v t)
  have denom (z : ℂ) (hz : z ∈ closure S) : w-z ≠ 0 := by
    intro e
    have hw' := hw _ hz
    rw [e,norm_zero] at hw'
    linarith
  have slit (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) (z : ℂ) (hz : z ∈ closure S) :
      1+(q:ℂ)*u z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    have bound : ‖(q:ℂ)*u z‖ ≤ q := by
      simpa [norm_mul,abs_of_nonneg hq] using mul_le_mul_of_nonneg_left (hu z hz) hq
    have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans bound)).1
    simp only [Complex.add_re,Complex.one_re]
    linarith
  have hK (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) : K q a b + K q b c = K q a c := by
    apply triangle_segment_deformation_closure hs _ _ ha hb hc
    · intro z hz
      have hz' := subset_closure hz
      exact ((differentiableWithinAt_const (1:ℂ)).add ((du z hz).const_mul (q:ℂ))).clog
        (slit q hq hq' z hz') |>.div
          ((differentiableWithinAt_const w).sub differentiableWithinAt_id) (denom _ hz')
    · intro z hz
      have n : ContinuousWithinAt (fun z => 1+(q:ℂ)*u z) (closure S) z :=
        (continuous_const.add (continuous_const.mul uco)).continuousWithinAt
      exact (n.clog (slit q hq hq' z hz)).div
        ((continuous_const.sub continuous_id).continuousWithinAt) (denom _ hz)
  have lim (p v : ℂ) (hp' : p ∈ closure S) (hv' : v ∈ closure S) (oh : ok p v) :
      Tendsto (fun q : ℝ => K q p v) (𝓝[<] 1) (𝓝 (J p v)) := by
    let W := fun t : ℝ => (v-p)/(w-e p v t)
    have ct : Continuous (e p v : ℝ → ℂ) := by
      change Continuous (fun t : ℝ => AffineMap.lineMap p v t)
      simp only [AffineMap.lineMap_apply_module',Complex.real_smul]
      fun_prop
    have um : Measurable (fun t => u (e p v t)) := (uco.comp ct).measurable
    have wm : Measurable W := measurable_const.div ((continuous_const.sub ct).measurable)
    have mem (t : ℝ) (ht : t ∈ uIoc (0:ℝ) 1) : e p v t ∈ closure S := by
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using uIoc_subset_uIcc ht
      exact hs.closure.lineMap_mem hp' hv' ht'
    have bound (t : ℝ) (ht : t ∈ uIoc (0:ℝ) 1) : ‖W t‖ ≤ ‖v-p‖/d := by
      simp only [W,norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hp (hw _ (mem t ht))
    have lim := abel_log_integral_limit 0 1 (fun t => u (e p v t)) W um wm (‖v-p‖/d) (by positivity)
      (fun t ht => hu _ (mem t ht)) bound oh.1 oh.2
    simpa only [K,J,H,W,div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using lim
  have e1 := (lim a b ha hb oab).add (lim b c hb hc obc)
  have eventuallyEq : Filter.EventuallyEq (𝓝[<] (1:ℝ)) (fun q => K q a b + K q b c) (fun q => K q a c) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (show (0:ℝ) < 1 by norm_num))] with q hq hq0
    exact hK q (show 0 < q from hq0).le hq
  exact tendsto_nhds_unique e1 ((lim a c ha hc oac).congr' eventuallyEq.symm)

end MomentSearch


namespace MomentSearch
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate

private theorem cauchy_kernel_reflection (x h : ℝ) (z : ℂ) :
    (x:ℂ)-(h:ℂ)*Complex.I-(-conj z) =
      -conj ((-x:ℝ)-(h:ℂ)*Complex.I-z) := by
  push_cast
  simp only [map_sub,map_mul,map_neg,Complex.conj_ofReal,Complex.conj_I]
  ring

set_option maxHeartbeats 800000 in
/-- A symmetric phase on the upper strip gives the contour formula with the explicit two side orientations. -/
theorem symmetric_upper_strip_contour (r : ℝ) (hr : 0 < r) (u : ℂ → ℂ) (cu : Continuous u)
    (du : DifferentiableOn ℂ u {z : ℂ | z.re ∈ Ioo (-r) r ∧ 0 < z.im})
    (hu : ∀ z : ℂ, z.re ∈ Icc (-r) r → 0 ≤ z.im → ‖u z‖ ≤ 1)
    (symm : ∀ z : ℂ, z.re ∈ Icc (-r) r → 0 ≤ z.im → u (-conj z) = conj (u z))
    (Y : Finset ℝ)
    (hbase : ∀ t ∈ Icc (-r) r, t ∉ Y → 1+u (t:ℂ) ≠ 0)
    (hlog : IntervalIntegrable (fun t : ℝ => Real.log ‖1+u (t:ℂ)‖) volume (-r) r)
    (x h : ℝ) (hh : 0 < h) :
    let s : ℂ := ⟨1/2,-Real.sqrt 3/2⟩
    let Z := fun t : ℝ => (r:ℂ)*(1-s*t)
    let L := fun z : ℂ => Complex.log (1+u z)
    let R := fun v : ℝ => ∫ t in (0:ℝ)..2, L (Z t) * (-(r:ℂ)*s) /
      ((v:ℂ)-(h:ℂ)*Complex.I-Z t)
    (∀ t ∈ Icc (0:ℝ) 2, 1+u (Z t) ≠ 0) →
    (∫ t in (-r)..r, L (t:ℂ)/((x:ℂ)-(h:ℂ)*Complex.I-(t:ℂ))) =
      conj (R (-x)) - R x := by
  intro s Z L R hside
  let S := {z : ℂ | z.re ∈ Ioo (-r) r ∧ 0 < z.im}
  let C := {z : ℂ | z.re ∈ Icc (-r) r ∧ 0 ≤ z.im}
  have cl : closure S = C := upper_strip_closure r hr
  have conv : Convex ℝ S := by
    have e : S = (Complex.reCLM ⁻¹' Ioo (-r) r) ∩ (Complex.imCLM ⁻¹' Ioi 0) := rfl
    rw [e]
    exact ((convex_Ioo (-r) r).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi 0).linear_preimage Complex.imCLM.toLinearMap)
  let a : ℂ := (-r:ℝ)
  let b : ℂ := (r:ℝ)
  let c := Z 2
  let w := (x:ℂ)-(h:ℂ)*Complex.I
  let v := (-(r:ℂ)*s)
  let e : ℂ → ℂ → ℝ → ℂ := fun p q t => AffineMap.lineMap p q t
  let J := fun p q : ℂ => ∫ t in (0:ℝ)..1, (q-p)*L (e p q t)/(w-e p q t)
  have mem_a : a ∈ closure S := by rw [cl]; exact ⟨⟨le_rfl,by change -r ≤ r; linarith⟩,by simp [a]⟩
  have mem_b : b ∈ closure S := by rw [cl]; exact ⟨⟨by change -r ≤ r; linarith,le_rfl⟩,by simp [b]⟩
  have Zre (t : ℝ) : (Z t).re = r*(1-t/2) := by simp only [Z,s,Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero]; ring
  have Zim (t : ℝ) : (Z t).im = r*(Real.sqrt 3*t/2) := by simp only [Z,s,Complex.mul_im,Complex.sub_im,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,add_zero,zero_add,zero_sub]; ring
  have mem_Z (t : ℝ) (ht : t ∈ Icc (0:ℝ) 2) : Z t ∈ C := by
    change (Z t).re ∈ Icc (-r) r ∧ 0 ≤ (Z t).im
    rw [Zre,Zim]
    exact ⟨⟨by nlinarith [mul_nonneg hr.le (show 0 ≤ 1-t/2 by linarith [ht.2])],
      by nlinarith [mul_nonneg hr.le ht.1]⟩, by positivity [ht.1]⟩
  have mem_c : c ∈ closure S := cl ▸ mem_Z 2 ⟨by norm_num,le_rfl⟩
  have norm_u (z : ℂ) (hz : z ∈ closure S) : ‖u z‖ ≤ 1 := by
    rw [cl] at hz
    exact hu _ hz.1 hz.2
  have norm_w (z : ℂ) (hz : z ∈ closure S) : h ≤ ‖w-z‖ := by
    rw [cl] at hz
    have q := (Complex.abs_im_le_norm (w-z))
    rw [show (w-z).im = -(h+z.im) by simp [w,Complex.mul_im]; ring,abs_neg,
      abs_of_nonneg (by linarith [hz.2])] at q
    linarith [hz.2]
  have path_base (t : ℝ) : e a b t = ((-r+(2*r)*t : ℝ):ℂ) := by
    change AffineMap.lineMap a b t = _
    rw [AffineMap.lineMap_apply_module',Complex.real_smul]
    dsimp [a,b]; push_cast; ring
  have path_right (t : ℝ) : e b c t = Z (2*t) := by
    change AffineMap.lineMap b c t = _
    rw [AffineMap.lineMap_apply_module',Complex.real_smul]
    dsimp [b,c,Z]
    push_cast; ring
  have path_left (t : ℝ) : e a c t = -conj (Z (2*t)) := by
    change AffineMap.lineMap a c t = _
    have cre : c.re = 0 := by rw [show c = Z 2 from rfl,Zre]; ring
    have cs : -conj c = c := by apply Complex.ext <;> simp [cre]
    rw [AffineMap.lineMap_apply_module',Complex.real_smul, ← path_right]
    change _ = -conj (AffineMap.lineMap b c t)
    rw [AffineMap.lineMap_apply_module',Complex.real_smul]
    simp only [map_add,map_mul,map_sub,Complex.conj_ofReal]
    rw [show conj b = b by simp [b], show conj c = -c by simpa using congrArg Neg.neg cs]
    dsimp [a,b]; push_cast; ring
  have log_arg_ne (z : ℂ) (hz : z ∈ C) : (1+u z).arg ≠ Real.pi := by
    have ab : |(u z).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (hu _ hz.1 hz.2)
    intro e
    have n := (Complex.arg_eq_pi_iff.mp e).1
    simp only [Complex.add_re,Complex.one_re] at n
    linarith [(abs_le.mp ab).1]
  have Lsym (t : ℝ) (ht : t ∈ Icc (0:ℝ) 2) :
      L (-conj (Z t)) = conj (L (Z t)) := by
    unfold L
    rw [symm _ (mem_Z _ ht).1 (mem_Z _ ht).2]
    simpa using Complex.log_conj (1+u (Z t)) (log_arg_ne _ (mem_Z _ ht))
  have well_base :
      (∀ᵐ t ∂volume, t ∈ uIoc (0:ℝ) 1 → 1+u (e a b t) ≠ 0) ∧
      IntervalIntegrable (fun t => Real.log ‖1+u (e a b t)‖) volume 0 1 := by
    constructor
    · let bad := Y.image (fun y => (y+r)/(2*r))
      have hn : ∀ᵐ t ∂volume, t ∉ bad := by
        rw [ae_iff]
        simpa using bad.finite_toSet.measure_zero volume
      filter_upwards [hn] with t ht hm
      rw [path_base]
      have hmem : t ∈ Icc (0:ℝ) 1 := by simpa using uIoc_subset_uIcc hm
      have hreal : -r+(2*r)*t ∈ Icc (-r) r := ⟨by nlinarith [mul_nonneg hr.le hmem.1],
        by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hmem.2)]⟩
      apply hbase _ hreal
      intro hy
      apply ht
      apply Finset.mem_image.mpr
      refine ⟨_,hy,?_⟩
      field_simp [hr.ne']; ring
    · simp_rw [path_base]
      have ei := hlog.comp_add_left (-r)
      have hj := ei.comp_mul_left (c := 2*r)
      convert hj using 1 <;> field_simp [hr.ne'] <;> ring
  have well_side (p q : ℂ) (nonzero : ∀ t ∈ Icc (0:ℝ) 1, 1+u (e p q t) ≠ 0) :
      (∀ᵐ t ∂volume, t ∈ uIoc (0:ℝ) 1 → 1+u (e p q t) ≠ 0) ∧
      IntervalIntegrable (fun t => Real.log ‖1+u (e p q t)‖) volume 0 1 := by
    refine ⟨.of_forall (fun t ht => nonzero _ (by simpa using uIoc_subset_uIcc ht)),?_⟩
    have ct : Continuous (fun t : ℝ => e p q t) := by
      change Continuous (fun t : ℝ => AffineMap.lineMap p q t)
      simp only [AffineMap.lineMap_apply_module',Complex.real_smul]
      fun_prop
    exact (((continuous_const.add (cu.comp ct)).norm.continuousOn.log
      (fun t ht => norm_ne_zero_iff.mpr (nonzero t ht)))).intervalIntegrable_of_Icc zero_le_one
  have right_ok : ∀ t ∈ Icc (0:ℝ) 1, 1+u (e b c t) ≠ 0 := by
    intro t ht
    rw [path_right]
    exact hside _ ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have left_ok : ∀ t ∈ Icc (0:ℝ) 1, 1+u (e a c t) ≠ 0 := by
    intro t ht
    have ht' : 2*t ∈ Icc (0:ℝ) 2 := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    rw [path_left,symm _ (mem_Z _ ht').1 (mem_Z _ ht').2]
    simpa using (map_ne_zero (starRingEnd ℂ)).mpr (hside _ ht')
  have deform : J a b + J b c = J a c :=
    triangle_log_deformation_limit conv u du cu norm_u w h hh norm_w a b c
      mem_a mem_b mem_c well_base (well_side _ _ left_ok) (well_side _ _ right_ok)
  have ebase : J a b = ∫ t in (-r)..r, L (t:ℂ)/(w-(t:ℂ)) := by
    let F := fun t : ℝ => L (t:ℂ)/(w-(t:ℂ))
    have he := intervalIntegral.smul_integral_comp_add_mul
      (a := (0:ℝ)) (b := 1) F (2*r) (-r)
    simp only [mul_zero,add_zero,mul_one] at he
    rw [show -r+2*r = r by ring,Complex.real_smul,← intervalIntegral.integral_const_mul] at he
    rw [show J a b = ∫ t in (0:ℝ)..1, (b-a)*L (e a b t)/(w-e a b t) from rfl]
    simp_rw [path_base]
    convert he using 1
    apply intervalIntegral.integral_congr
    intro t _
    rw [show b-a = ((2*r:ℝ):ℂ) by dsimp [a,b]; push_cast; ring]
    simp [F, mul_div_assoc]
  have eright : J b c = R x := by
    let F := fun t : ℝ => v*L (Z t)/(w-Z t)
    have he := intervalIntegral.smul_integral_comp_mul_left
      (a := (0:ℝ)) (b := 1) F 2
    simp only [mul_zero,mul_one,Complex.real_smul,Complex.ofReal_ofNat] at he
    rw [← intervalIntegral.integral_const_mul] at he
    have hb : c-b = 2*v := by dsimp [c,Z,b,v]; ring
    have lhs : J b c = ∫ t in (0:ℝ)..1, (2:ℂ)*F (2*t) := by
      change (∫ t in (0:ℝ)..1, (c-b)*L (e b c t)/(w-e b c t)) = _
      simp_rw [path_right,hb,F,mul_div_assoc, mul_assoc]
    rw [lhs, he]
    simp_rw [R,F,v,w, mul_comm (-(r:ℂ)*s)]
  have eleft : J a c = conj (R (-x)) := by
    let F := fun t : ℝ => conj (v*L (Z t)/(((-x:ℝ):ℂ)-(h:ℂ)*Complex.I-Z t))
    have he := intervalIntegral.smul_integral_comp_mul_left
      (a := (0:ℝ)) (b := 1) F 2
    simp only [mul_zero,mul_one,Complex.real_smul,Complex.ofReal_ofNat] at he
    rw [← intervalIntegral.integral_const_mul] at he
    have ha : c-a = -2*conj v := by
      have p1 := path_left 1
      change AffineMap.lineMap a c 1 = _ at p1
      simp only [AffineMap.lineMap_apply_one,mul_one] at p1
      rw [p1]
      simp [Z,a,v,show conj (2:ℂ) = 2 from map_ofNat _ 2]
      ring
    have lhs : J a c = ∫ t in (0:ℝ)..1, (2:ℂ)*F (2*t) := by
      change (∫ t in (0:ℝ)..1, (c-a)*L (e a c t)/(w-e a c t)) = _
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using ht
      have ht'' : 2*t ∈ Icc (0:ℝ) 2 := ⟨by linarith [ht'.1],by linarith [ht'.2]⟩
      change (c-a)*L (e a c t)/(w-e a c t) = (2:ℂ)*F (2*t)
      rw [path_left,ha,Lsym _ ht'']
      dsimp [w,F]
      rw [cauchy_kernel_reflection]
      simp only [map_div₀,map_mul,div_neg]
      ring
    rw [lhs,he]
    dsimp [F,R,v]
    simp_rw [mul_comm (-(r:ℂ)*s)]
    simp only [intervalIntegral,integral_conj,map_sub]
  rw [ebase,eright,eleft] at deform
  exact eq_sub_iff_add_eq.mpr deform
end MomentSearch


open Set MeasureTheory
open MomentSearch
open scoped ComplexConjugate

set_option maxHeartbeats 800000 in
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
  intro r ρ f s Z B E P Y hY hcY hroots x h hh
  let T := fun t : ℝ => ∫ v in t..r, ρ v
  obtain ⟨hr,hr1,hc,hs,ha,hb,hft,hg⟩ := rakhmanov_real_phase N k hk hkN
  change 0 < r at hr
  change r ≤ 1 at hr1
  change ∀ t : ℝ, f t = Real.cos (Real.pi*T t) at hft
  obtain ⟨g,cg,eg⟩ := hg Y hcY hroots
  have hab : -r ≤ r := by linarith
  have roots (t : ℝ) (ht : t ∈ Icc (-r) r) : t ∈ Y ↔ Real.cos (Real.pi*T t) = 0 := by
    rw [← hft t]
    exact hroots t (Icc_subset_Icc (by linarith) hr1 ht)
  obtain ⟨hlog,_,e⟩ := quantile_base_trace hab T g (N-k) Y hc hs ha hb hY roots cg eg x h hh
  obtain ⟨u,cu,du,hu,sym,base,side⟩ := rakhmanov_contour_phase N k hk hkN
  change ∀ t ∈ Icc (-r) r, u (t:ℂ) = Complex.exp (-2*(Real.pi:ℂ)*(T t:ℂ)*Complex.I) at base
  change ∀ t ∈ Icc (0:ℝ) 2, u (Z t) = Complex.exp (-(B t)) ∧ 1+u (Z t) ≠ 0 at side
  let V := fun t : ℝ => Complex.exp (-2*(Real.pi:ℂ)*(T t:ℂ)*Complex.I)
  have hn (t : ℝ) (ht : t ∈ Icc (-r) r) (hy : t ∉ Y) : 1+u (t:ℂ) ≠ 0 := by
    rw [base t ht]
    let b := -(Real.pi*T t)
    have he : -2*(Real.pi:ℂ)*(T t:ℂ)*Complex.I = 2*(b:ℂ)*Complex.I := by
      dsimp [b]; push_cast; ring
    rw [he,one_add_exp_two_mul_I]
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    have q : Real.cos (Real.pi*T t) ≠ 0 := fun eq => hy ((roots t ht).mpr eq)
    exact_mod_cast (show 2*Real.cos b ≠ 0 by simp [b,q])
  have hi : IntervalIntegrable (fun t : ℝ => Real.log ‖1+u (t:ℂ)‖) volume (-r) r := by
    refine hlog.congr (fun t ht => ?_)
    have ht' : t ∈ Icc (-r) r := by simpa [uIcc_of_le hab] using uIoc_subset_uIcc ht
    change Real.log ‖1+V t‖ = _
    rw [base t ht']
  have defo := symmetric_upper_strip_contour r hr u cu du hu sym Y hn hi x h hh
    (fun t ht => (side t ht).2)
  let J := fun v : ℝ => ∫ t in (0:ℝ)..2, Complex.log (1+u (Z t)) * (-(r:ℂ)*s) /
      ((v:ℂ)-(h:ℂ)*Complex.I-Z t)
  let J' := fun v : ℝ => ∫ t in (0:ℝ)..2, Complex.log (1+Complex.exp (-(B t))) * (-(r:ℂ)*s) /
      ((v:ℂ)-(h:ℂ)*Complex.I-Z t)
  have hj (v : ℝ) : J v = J' v := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 2 := by simpa using ht
    change Complex.log (1+u (Z t)) * _ / _ = _
    rw [(side t ht').1]
  change (∫ t in (-r)..r, Complex.log (1+u (t:ℂ))/((x:ℂ)-(h:ℂ)*Complex.I-(t:ℂ))) =
    conj (J (-x)) - J x at defo
  rw [hj,hj] at defo
  have ebase : (∫ t in (-r)..r, Complex.log (1+u (t:ℂ))/((x:ℂ)-(h:ℂ)*Complex.I-(t:ℂ))) =
      ∫ t in (-r)..r, Complex.log (1+V t)/((x:ℂ)-(h:ℂ)*Complex.I-(t:ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (-r) r := by simpa [uIcc_of_le hab] using ht
    change Complex.log (1+u (t:ℂ))/_ = Complex.log (1+V t)/_
    rw [base t ht']
  rw [ebase] at defo
  have hp : (∫ t in (-r)..r, h/((x-t)^2+h^2)*Real.log (2*|Real.cos (Real.pi*T t)|))/Real.pi = P x h := by
    change _ = (∫ t in (-r)..r, h/((x-t)^2+h^2)*Real.log (2*|f t|))/Real.pi
    simp_rw [← hft]
  change _ = (∫ t in (-r)..r, h/((x-t)^2+h^2)*Real.log (2*|Real.cos (Real.pi*T t)|))/Real.pi -
    (∫ t in (-r)..r, Complex.log (1+V t)/((x:ℂ)-(h:ℂ)*Complex.I-(t:ℂ))).im/Real.pi at e
  rw [hp,defo] at e
  simp only [Complex.sub_im,Complex.conj_im] at e
  exact e.trans (by change _ = P x h + (J' x).im/Real.pi + (J' (-x)).im/Real.pi; ring)
