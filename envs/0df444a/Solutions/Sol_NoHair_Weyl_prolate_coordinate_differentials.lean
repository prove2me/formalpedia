-- Prove2me | solution 1 for NoHair.Weyl.prolate_coordinate_differentials
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:16:53.202087+00:00
-- url     : https://prove2.me/submissions/49bec4dd-a14b-4b7e-ab1f-be3987622aa1

import Definitions.Def_NoHair_kerrWeylModel

noncomputable section

open NoHair.Weyl

private theorem prolate_gt_abs (ℓ : ℝ) (p : OrbitPoint) : |p.2| < prolateRadius ℓ p := by
  have side (x : ℝ) : |x| < Real.sqrt (Real.exp (2*p.1)+x^2) := by
    rw [← Real.sqrt_sq_eq_abs x]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith [Real.exp_pos (2*p.1)])
  have h := abs_add_le (p.2-ℓ) (p.2+ℓ)
  rw [show p.2-ℓ+(p.2+ℓ) = 2*p.2 by ring, abs_mul, abs_of_pos (by norm_num : 0 < (2:ℝ))] at h
  unfold prolateRadius
  linarith [side (p.2-ℓ), side (p.2+ℓ)]

private def direction (i : OrbitPoint) (f : OrbitPoint → ℝ) (p : OrbitPoint) : ℝ :=
  fderiv ℝ f p i

private theorem diff_direction (i : OrbitPoint) {f : OrbitPoint → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (direction i f) :=
  ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
    (show ContDiff ℝ 1 (fun _ : OrbitPoint => i) from contDiff_const)).differentiable_one

private theorem dir_add (i : OrbitPoint) {f g : OrbitPoint → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    direction i (fun q => f q + g q) = fun q => direction i f q + direction i g q := by
  funext q
  simp [direction, fderiv_fun_add (hf q) (hg q)]

private theorem dir_sub (i : OrbitPoint) {f g : OrbitPoint → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    direction i (fun q => f q - g q) = fun q => direction i f q - direction i g q := by
  funext q
  simp [direction, fderiv_fun_sub (hf q) (hg q)]

private theorem dir_mul (i : OrbitPoint) {f g : OrbitPoint → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    direction i (fun q => f q * g q) = fun q => direction i f q * g q + f q * direction i g q := by
  funext q
  simp only [direction, fderiv_fun_mul (hf q) (hg q), add_apply,
    smul_apply, smul_eq_mul]
  ring

private def weight (p : OrbitPoint) := Real.exp (2 * p.1)

/-- A value, its two first partials, and its scaled Laplacian at one point. -/
@[ext] private structure Jet where
  value : ℝ
  s : ℝ
  z : ℝ
  lap : ℝ

private def jetAt (p : OrbitPoint) (f : OrbitPoint → ℝ) : Jet :=
  ⟨f p, direction (1,0) f p, direction (0,1) f p,
    direction (1,0) (direction (1,0) f) p + weight p * direction (0,1) (direction (0,1) f) p⟩

private def addJ (a b : Jet) : Jet := ⟨a.value+b.value, a.s+b.s, a.z+b.z, a.lap+b.lap⟩

private def subJ (a b : Jet) : Jet := ⟨a.value-b.value, a.s-b.s, a.z-b.z, a.lap-b.lap⟩

private def mulJ (w : ℝ) (a b : Jet) : Jet :=
  ⟨a.value*b.value, a.s*b.value+a.value*b.s, a.z*b.value+a.value*b.z,
    a.lap*b.value+a.value*b.lap+2*(a.s*b.s+w*a.z*b.z)⟩

private def divJ (w : ℝ) (a b : Jet) : Jet :=
  let v := a.value/b.value
  let s := (a.s-v*b.s)/b.value
  let z := (a.z-v*b.z)/b.value
  ⟨v,s,z,(a.lap-v*b.lap-2*(s*b.s+w*z*b.z))/b.value⟩

private theorem jet_add {f g : OrbitPoint → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (p : OrbitPoint) : jetAt p (fun q => f q + g q) = addJ (jetAt p f) (jetAt p g) := by
  have fd := hf.differentiable (by norm_num)
  have gd := hg.differentiable (by norm_num)
  have twice (i : OrbitPoint) : direction i (direction i (fun q => f q + g q)) p =
      direction i (direction i f) p + direction i (direction i g) p := by
    rw [dir_add i fd gd, dir_add i (diff_direction i hf) (diff_direction i hg)]
  apply Jet.ext
  · rfl
  · exact congrFun (dir_add _ fd gd) p
  · exact congrFun (dir_add _ fd gd) p
  · dsimp only [jetAt, addJ]
    simp only [twice]
    ring

private theorem jet_sub {f g : OrbitPoint → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (p : OrbitPoint) : jetAt p (fun q => f q - g q) = subJ (jetAt p f) (jetAt p g) := by
  have fd := hf.differentiable (by norm_num)
  have gd := hg.differentiable (by norm_num)
  have twice (i : OrbitPoint) : direction i (direction i (fun q => f q - g q)) p =
      direction i (direction i f) p - direction i (direction i g) p := by
    rw [dir_sub i fd gd, dir_sub i (diff_direction i hf) (diff_direction i hg)]
  apply Jet.ext
  · rfl
  · exact congrFun (dir_sub _ fd gd) p
  · exact congrFun (dir_sub _ fd gd) p
  · dsimp only [jetAt, subJ]
    simp only [twice]
    ring

private theorem jet_mul {f g : OrbitPoint → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (p : OrbitPoint) : jetAt p (fun q => f q * g q) = mulJ (weight p) (jetAt p f) (jetAt p g) := by
  have fd := hf.differentiable (by norm_num)
  have gd := hg.differentiable (by norm_num)
  have twice (i : OrbitPoint) : direction i (direction i (fun q => f q * g q)) p =
      direction i (direction i f) p * g p + f p * direction i (direction i g) p +
      2 * direction i f p * direction i g p := by
    rw [dir_mul i fd gd, dir_add i ((diff_direction i hf).fun_mul gd) (fd.fun_mul (diff_direction i hg)),
      dir_mul i (diff_direction i hf) gd, dir_mul i fd (diff_direction i hg)]
    ring
  apply Jet.ext
  · rfl
  · exact congrFun (dir_mul _ fd gd) p
  · exact congrFun (dir_mul _ fd gd) p
  · dsimp only [jetAt, mulJ]
    simp only [twice]
    ring

private theorem quotient_of_product {w : ℝ} {a b q : Jet} (hb : b.value ≠ 0)
    (hm : mulJ w q b = a) : q = divJ w a b := by
  subst a
  cases q
  cases b
  dsimp at hb
  apply Jet.ext <;> dsimp [divJ, mulJ] <;> field_simp [hb] <;> ring

private theorem jet_div {f g : OrbitPoint → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hn : ∀ q, g q ≠ 0) (p : OrbitPoint) :
    jetAt p (fun q => f q / g q) = divJ (weight p) (jetAt p f) (jetAt p g) := by
  have he : (fun q => f q / g q * g q) = f := funext fun q => div_mul_cancel₀ _ (hn q)
  apply quotient_of_product (hn p)
  exact (jet_mul (hf.div hg hn) hg p).symm.trans (congrArg (jetAt p) he)

private theorem slice_s {f : OrbitPoint → ℝ} (hf : Differentiable ℝ f) (s z : ℝ) :
    HasDerivAt (fun t : ℝ => f (t, z)) (ds f (s, z)) s :=
  (hf (s,z)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))

private theorem slice_z {f : OrbitPoint → ℝ} (hf : Differentiable ℝ f) (s z : ℝ) :
    HasDerivAt (fun t : ℝ => f (s, t)) (dz f (s, z)) z :=
  (hf (s,z)).hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z s).prodMk (hasDerivAt_id z))
/-- Basic jets for the logarithmic Weyl radius and height. -/
private def constJ (v : ℝ) : Jet := ⟨v,0,0,0⟩

private theorem dir_const (v : OrbitPoint) (b : ℝ) :
    direction v (fun _ => b) = fun _ => 0 := by
  funext q
  simp [direction]

private theorem dir_height (v : OrbitPoint) :
    direction v (fun q => q.2) = fun _ => v.2 := by
  funext q
  change (fderiv ℝ (@Prod.snd ℝ ℝ) q) v = v.2
  rw [fderiv_snd]
  rfl

private theorem jet_const (b : ℝ) (p : OrbitPoint) : jetAt p (fun _ => b) = constJ b := by
  apply Jet.ext <;> simp [jetAt, constJ, dir_const]

private theorem jet_height (p : OrbitPoint) :
    jetAt p (fun q => q.2) = ⟨p.2,0,1,0⟩ := by
  apply Jet.ext <;> simp [jetAt, dir_height, dir_const]

private theorem jet_weight (p : OrbitPoint) :
    jetAt p weight = ⟨weight p,2*weight p,0,4*weight p⟩ := by
  have hw : Differentiable ℝ weight := by unfold weight; fun_prop
  have de (s : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (2*t)) (2*Real.exp (2*s)) s := by
    convert ((hasDerivAt_id' s).const_mul 2).exp using 1
    simp
    ring
  have hs : direction (1,0) weight = fun q => 2*weight q := by
    funext q
    exact (slice_s hw q.1 q.2).unique (de q.1)
  have hz : direction (0,1) weight = fun _ => 0 := by
    funext q
    exact (slice_z hw q.1 q.2).unique (hasDerivAt_const q.2 (Real.exp (2*q.1)))
  apply Jet.ext
  · rfl
  · exact congrFun hs p
  · exact congrFun hz p
  · change direction (1,0) (direction (1,0) weight) p +
      weight p * direction (0,1) (direction (0,1) weight) p = _
    rw [hs,hz]
    have h := (slice_s (f:=fun q => 2*weight q) (hw.const_mul 2) p.1 p.2).unique ((de p.1).const_mul 2)
    change direction (1,0) (fun q => 2*weight q) p = 2*(2*weight p) at h
    rw [h]
    simp [dir_const]
    ring

/-- The distance to one Weyl endpoint has axisymmetric Laplacian 2/d away from that endpoint. -/
private def endpoint (h : ℝ) (p : OrbitPoint) := Real.sqrt (weight p+(p.2-h)^2)

private theorem endpoint_pos (h : ℝ) (p : OrbitPoint) : 0 < endpoint h p := by
  unfold endpoint weight
  positivity

private theorem endpoint_smooth (h : ℝ) : ContDiff ℝ 2 (endpoint h) := by
  unfold endpoint weight
  fun_prop (disch := first | positivity | intro q; positivity)

private theorem jet_endpoint (h : ℝ) (p : OrbitPoint) :
    jetAt p (endpoint h) =
      ⟨endpoint h p,weight p/endpoint h p,(p.2-h)/endpoint h p,2*weight p/endpoint h p⟩ := by
  let d := endpoint h p
  have hd : 0 < d := endpoint_pos h p
  have sqr (q : OrbitPoint) : endpoint h q * endpoint h q = weight q + (q.2-h)*(q.2-h) := by
    unfold endpoint
    rw [Real.mul_self_sqrt (by unfold weight; positivity), sq]
  have hf := funext sqr
  have he := endpoint_smooth h
  have hw : ContDiff ℝ 2 weight := by unfold weight; fun_prop
  have hh : ContDiff ℝ 2 (fun q : OrbitPoint => q.2-h) := contDiff_snd.sub contDiff_const
  have hjet := congrArg (jetAt p) hf
  rw [jet_mul he he p,jet_add hw (hh.mul hh) p, jet_mul hh hh p,
    jet_sub contDiff_snd contDiff_const p,jet_height, jet_const, jet_weight] at hjet
  let j := jetAt p (endpoint h)
  have hd₂ : d^2 = weight p+(p.2-h)^2 := by simpa only [sq] using sqr p
  have h₁ := congrArg Jet.s hjet
  have h₂ := congrArg Jet.z hjet
  have h₃ := congrArg Jet.lap hjet
  change j.s*d+d*j.s = _ at h₁
  change j.z*d+d*j.z = _ at h₂
  change j.lap*d+d*j.lap+2*(j.s*j.s+weight p*j.z*j.z) = _ at h₃
  dsimp [addJ,mulJ,subJ,constJ] at h₁ h₂ h₃
  have hs : j.s = weight p/d := (eq_div_iff hd.ne').2 (by linarith)
  have hz : j.z = (p.2-h)/d := (eq_div_iff hd.ne').2 (by linarith)
  have hgrad : j.s*j.s+weight p*j.z*j.z = weight p := by
    rw [hs,hz]
    field_simp [hd.ne']
    nlinarith only [congrArg (fun x => weight p*x) hd₂]
  have hl : j.lap = 2*weight p/d := (eq_div_iff hd.ne').2 (by rw [hgrad] at h₃; linarith)
  exact Jet.ext rfl hs hz hl
/-- First derivatives and the scaled Laplacian in prolate spheroidal coordinates.
The formulas use no division by the horizon length and also cover a point horizon. -/
private def radialJ (w u c k : ℝ) : Jet :=
  let d := u^2-k^2*c^2
  ⟨u,w*u/d,c*(u^2-k^2)/d,2*w*u/d⟩

private def polarJ (w u c k : ℝ) : Jet :=
  let d := u^2-k^2*c^2
  ⟨c,-w*c/d,u*(1-c^2)/d,-2*w*c/d⟩

private theorem radial_smooth (k : ℝ) : ContDiff ℝ 2 (prolateRadius k) := by
  unfold prolateRadius
  fun_prop (disch := first | positivity | intro q; positivity)

private theorem polar_smooth (k : ℝ) :
    ContDiff ℝ 2 (fun q : OrbitPoint => q.2/prolateRadius k q) :=
  contDiff_snd.div (radial_smooth k) fun q => ((abs_nonneg _).trans_lt (prolate_gt_abs k q)).ne'

private theorem prolate_jets (k : ℝ) (p : OrbitPoint) :
    let u := prolateRadius k p
    let c := p.2/u
    0 < u ∧ 0 < u^2-k^2*c^2 ∧ weight p = (u^2-k^2)*(1-c^2) ∧
    jetAt p (prolateRadius k) = radialJ (weight p) u c k ∧
    jetAt p (fun q => q.2/prolateRadius k q) = polarJ (weight p) u c k := by
  let u := prolateRadius k p
  let c := p.2/u
  let n := endpoint k p
  let b := endpoint (-k) p
  have hu : 0 < u := (abs_nonneg _).trans_lt (prolate_gt_abs k p)
  have hheight : p.2 = u*c := by dsimp [c]; field_simp
  have radial : prolateRadius k = fun q => (endpoint k q+endpoint (-k) q)/2 := by
    funext q
    simp [prolateRadius,endpoint,weight]
  have havg : u = (n+b)/2 := congrFun radial p
  have sqn : n^2 = weight p+(p.2-k)^2 := Real.sq_sqrt (by unfold weight; positivity)
  have sqb : b^2 = weight p+(p.2+k)^2 := by
    dsimp [b,endpoint]
    rw [sub_neg_eq_add,Real.sq_sqrt (by unfold weight; positivity)]
  have hdiff : b-n = 2*c*k := by
    apply mul_right_cancel₀ hu.ne'
    calc
      (b-n)*u = 2*p.2*k := by rw [havg]; nlinarith only [sqb,sqn]
      _ = 2*c*k*u := by rw [hheight]; ring
  have hn : n = u-k*c := by linarith
  have hb : b = u+k*c := by linarith
  have hnp : 0 < u-k*c := hn ▸ endpoint_pos k p
  have hbp : 0 < u+k*c := hb ▸ endpoint_pos (-k) p
  have hden : 0 < u^2-k^2*c^2 := by nlinarith [mul_pos hnp hbp]
  have hw : weight p = (u^2-k^2)*(1-c^2) := by
    rw [hn,hheight] at sqn
    nlinarith only [sqn]
  have jR : jetAt p (prolateRadius k) = radialJ (weight p) u c k := by
    rw [radial,jet_div ((endpoint_smooth k).add (endpoint_smooth (-k))) contDiff_const
      (fun _ => (by norm_num : (2:ℝ) ≠ 0)) p,jet_const,
      jet_add (endpoint_smooth k) (endpoint_smooth (-k)) p,jet_endpoint,jet_endpoint]
    change endpoint k p = u-k*c at hn
    change endpoint (-k) p = u+k*c at hb
    rw [hn,hb,hheight]
    apply Jet.ext <;> dsimp [divJ,addJ,constJ,radialJ]
    all_goals try simp only [mul_zero,sub_zero,add_zero,sub_neg_eq_add]
    all_goals try rw [show u^2-k^2*c^2 = (u-k*c)*(u+k*c) by ring]
    all_goals field_simp (disch := first | positivity | grind)
    all_goals ring
  refine ⟨hu,hden,hw,jR,?_⟩
  change jetAt p (fun q => q.2/prolateRadius k q) = polarJ (weight p) u c k
  rw [jet_div contDiff_snd (radial_smooth k)
    (fun q => ((abs_nonneg _).trans_lt (prolate_gt_abs k q)).ne') p,jet_height,jR,hheight]
  apply Jet.ext <;> dsimp [divJ,radialJ,polarJ]
  all_goals try rw [hw]
  all_goals try rw [show u*c/u = c by field_simp]
  all_goals field_simp (disch := first | positivity | grind)
  all_goals ring

theorem solution (k : ℝ) :
    let U := prolateRadius k
    let C := fun p : OrbitPoint => p.2/U p
    ContDiff ℝ 2 U ∧ ContDiff ℝ 2 C ∧ ∀ p,
      let u := U p
      let c := C p
      let w := Real.exp (2*p.1)
      let A := u^2-k^2
      let B := 1-c^2
      let D := u^2-k^2*c^2
      0 < u ∧ 0 < B ∧ 0 < D ∧ w = A*B ∧
      ds U p = w*u/D ∧ dz U p = c*A/D ∧ ds C p = -w*c/D ∧ dz C p = u*B/D := by
  refine ⟨radial_smooth k,polar_smooth k,?_⟩
  intro p
  let u := prolateRadius k p
  let c := p.2/u
  obtain ⟨hu,hd,hw,hr,hc⟩ := prolate_jets k p
  have hb : |c| < 1 := by
    change |p.2/u| < 1
    rw [abs_div,abs_of_pos hu,div_lt_iff₀ hu,one_mul]
    exact prolate_gt_abs k p
  obtain ⟨hl,hh⟩ := abs_lt.mp hb
  have hB : 0 < 1-c^2 := by nlinarith [mul_pos (sub_pos.mpr hh) (show 0 < 1+c by linarith)]
  exact ⟨hu,hB,hd,hw,congrArg Jet.s hr,congrArg Jet.z hr,congrArg Jet.s hc,congrArg Jet.z hc⟩
