-- Prove2me | solution 1 for NoHair.Weyl.kerr_reduced_field_equations
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:39:07.025876+00:00
-- url     : https://prove2.me/submissions/06d90f3d-e19b-4b8c-aeb1-e9f96ecf21bb

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
/-- A jet in the radial and polar variables. The bilinear form has diagonal
coefficients A=Δ and B=1-c² in these variables. -/
private def pairing (A B : ℝ) (x y : Jet) := A*x.s*y.s+B*x.z*y.z

private def redMul (A B : ℝ) (x y : Jet) : Jet :=
  ⟨x.value*y.value,x.s*y.value+x.value*y.s,x.z*y.value+x.value*y.z,
    x.lap*y.value+x.value*y.lap+2*pairing A B x y⟩

private def redDiv (A B : ℝ) (x y : Jet) : Jet :=
  let v := x.value/y.value
  let u := (x.s-v*y.s)/y.value
  let b := (x.z-v*y.z)/y.value
  ⟨v,u,b,(x.lap-v*y.lap-2*(A*u*y.s+B*b*y.z))/y.value⟩

private def toWeyl (r c : Jet) (scale : ℝ) (x : Jet) : Jet :=
  ⟨x.value,x.s*r.s+x.z*c.s,x.s*r.z+x.z*c.z,scale*x.lap⟩

private def PreservesPairing (w A B : ℝ) (r c : Jet) (scale : ℝ) : Prop :=
  ∀ x y, pairing 1 w (toWeyl r c scale x) (toWeyl r c scale y) = scale*pairing A B x y

private theorem lift_const (r c : Jet) (t b : ℝ) : toWeyl r c t (constJ b) = constJ b := by
  apply Jet.ext <;> simp [toWeyl,constJ]

private theorem lift_add (r c : Jet) (t : ℝ) (x y : Jet) :
    addJ (toWeyl r c t x) (toWeyl r c t y) = toWeyl r c t (addJ x y) := by
  apply Jet.ext <;> dsimp [toWeyl,addJ] <;> ring

private theorem lift_sub (r c : Jet) (t : ℝ) (x y : Jet) :
    subJ (toWeyl r c t x) (toWeyl r c t y) = toWeyl r c t (subJ x y) := by
  apply Jet.ext <;> dsimp [toWeyl,subJ] <;> ring

private theorem lift_mul {w A B t : ℝ} {r c : Jet} (h : PreservesPairing w A B r c t) (x y : Jet) :
    mulJ w (toWeyl r c t x) (toWeyl r c t y) = toWeyl r c t (redMul A B x y) := by
  have hb := h x y
  dsimp [pairing,toWeyl] at hb
  apply Jet.ext <;> dsimp [mulJ,redMul,pairing,toWeyl]
  · ring
  · ring
  · linarith only [hb]

private theorem lift_div {w A B t : ℝ} {r c : Jet} (h : PreservesPairing w A B r c t)
    (x y : Jet) (hn : y.value ≠ 0) :
    divJ w (toWeyl r c t x) (toWeyl r c t y) = toWeyl r c t (redDiv A B x y) := by
  symm
  apply quotient_of_product (show (toWeyl r c t y).value ≠ 0 from hn)
  rw [lift_mul h]
  apply congrArg (toWeyl r c t)
  apply Jet.ext <;> dsimp [redMul,redDiv,pairing] <;> field_simp [hn] <;> ring

/-- An arithmetic expression in the two coordinates, used to carry the same
product and quotient rules through both explicit potentials. -/
private inductive Formula
  | num (k : ℝ) | radius | polar
  | add (f g : Formula) | sub (f g : Formula) | mul (f g : Formula) | div (f g : Formula)

private def evalF (r c : ℝ) : Formula → ℝ
  | .num k => k | .radius => r | .polar => c
  | .add f g => evalF r c f + evalF r c g
  | .sub f g => evalF r c f - evalF r c g
  | .mul f g => evalF r c f * evalF r c g
  | .div f g => evalF r c f / evalF r c g

private def definedF (r c : ℝ) : Formula → Prop
  | .num _ | .radius | .polar => True
  | .add f g | .sub f g | .mul f g => definedF r c f ∧ definedF r c g
  | .div f g => definedF r c f ∧ definedF r c g ∧ evalF r c g ≠ 0

private def evalJ (A B : ℝ) (r c : Jet) : Formula → Jet
  | .num k => constJ k | .radius => r | .polar => c
  | .add f g => addJ (evalJ A B r c f) (evalJ A B r c g)
  | .sub f g => subJ (evalJ A B r c f) (evalJ A B r c g)
  | .mul f g => redMul A B (evalJ A B r c f) (evalJ A B r c g)
  | .div f g => redDiv A B (evalJ A B r c f) (evalJ A B r c g)

private theorem transfer (r c : OrbitPoint → ℝ) (hr : ContDiff ℝ 2 r) (hc : ContDiff ℝ 2 c)
    (p : OrbitPoint) (R C jr jc : Jet) (A B t : ℝ)
    (hpres : PreservesPairing (weight p) A B R C t)
    (hjr : jetAt p r = toWeyl R C t jr) (hjc : jetAt p c = toWeyl R C t jc)
    (f : Formula) (hsafe : ∀ q, definedF (r q) (c q) f) :
    ContDiff ℝ 2 (fun q => evalF (r q) (c q) f) ∧
      jetAt p (fun q => evalF (r q) (c q) f) = toWeyl R C t (evalJ A B jr jc f) := by
  induction f with
  | num k => exact ⟨contDiff_const,(jet_const k p).trans (lift_const R C t k).symm⟩
  | radius => exact ⟨hr,hjr⟩
  | polar => exact ⟨hc,hjc⟩
  | add f g ih jh =>
    obtain ⟨hf,jf⟩ := ih (fun q => (hsafe q).1)
    obtain ⟨hg,jg⟩ := jh (fun q => (hsafe q).2)
    refine ⟨hf.add hg,?_⟩
    simp only [evalF,evalJ,jet_add hf hg p,jf,jg,lift_add]
  | sub f g ih jh =>
    obtain ⟨hf,jf⟩ := ih (fun q => (hsafe q).1)
    obtain ⟨hg,jg⟩ := jh (fun q => (hsafe q).2)
    refine ⟨hf.sub hg,?_⟩
    simp only [evalF,evalJ,jet_sub hf hg p,jf,jg,lift_sub]
  | mul f g ih jh =>
    obtain ⟨hf,jf⟩ := ih (fun q => (hsafe q).1)
    obtain ⟨hg,jg⟩ := jh (fun q => (hsafe q).2)
    refine ⟨hf.mul hg,?_⟩
    simp only [evalF,evalJ,jet_mul hf hg p,jf,jg,lift_mul hpres]
  | div f g ih jh =>
    obtain ⟨hf,jf⟩ := ih (fun q => (hsafe q).1)
    obtain ⟨hg,jg⟩ := jh (fun q => (hsafe q).2.1)
    have hn := fun q => (hsafe q).2.2
    have hp : (evalJ A B jr jc g).value ≠ 0 := by
      change (toWeyl R C t (evalJ A B jr jc g)).value ≠ 0
      rw [← jg]
      exact hn p
    refine ⟨hf.div hg hn,?_⟩
    simp only [evalF,evalJ,jet_div hf hg hn p,jf,jg,lift_div hpres _ _ hp]
private instance : Add Formula := ⟨Formula.add⟩
private instance : Sub Formula := ⟨Formula.sub⟩
private instance : Mul Formula := ⟨Formula.mul⟩
private instance : Div Formula := ⟨Formula.div⟩

private theorem f_add (x y : Formula) : x+y = Formula.add x y := rfl
private theorem f_sub (x y : Formula) : x-y = Formula.sub x y := rfl
private theorem f_mul (x y : Formula) : x*y = Formula.mul x y := rfl
private theorem f_div (x y : Formula) : x/y = Formula.div x y := rfl

private def normFormula (m a : ℝ) : Formula :=
  let r := Formula.radius
  let c := Formula.polar
  let sinSq := Formula.num 1 - c*c
  let sigma := r*r + Formula.num (a^2)*(c*c)
  sinSq*(r*r + Formula.num (a^2) + Formula.num (2*m)*r*Formula.num (a^2)*sinSq/sigma)

private def twistFormula (m a : ℝ) : Formula :=
  let r := Formula.radius
  let c := Formula.polar
  let sinSq := Formula.num 1 - c*c
  let sigma := r*r + Formula.num (a^2)*(c*c)
  Formula.num (2*m*a)*(Formula.num 3*c-c*c*c) +
    Formula.num (2*m*a^3)*c*(sinSq*sinSq)/sigma

private def rJet (m r : ℝ) : Jet := ⟨r,1,0,2*(r-m)⟩
private def cJet (c : ℝ) : Jet := ⟨c,0,1,-2*c⟩

private theorem formula_values (m a r c : ℝ) :
    evalF r c (normFormula m a) = kerrAxialNorm m a r c ∧
    evalF r c (twistFormula m a) = kerrAxialTwist m a r c := by
  constructor <;>
    simp only [normFormula,twistFormula,f_add,f_sub,f_mul,f_div,evalF,kerrAxialNorm,kerrAxialTwist] <;>
    simp only [pow_succ] <;> ring

private theorem formulas_defined (m a r c : ℝ) (hr : 0 < r) :
    definedF r c (normFormula m a) ∧ definedF r c (twistFormula m a) := by
  have hden : r*r+a^2*(c*c) ≠ 0 := (add_pos_of_pos_of_nonneg (mul_pos hr hr)
    (mul_nonneg (sq_nonneg a) (mul_self_nonneg c))).ne'
  constructor <;>
    simp only [normFormula,twistFormula,f_add,f_sub,f_mul,f_div,definedF,evalF] <;>
    simp [hden]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem rational_identities (m a r c : ℝ) (hr : 0 < r) :
    let A := r^2-2*m*r+a^2
    let B := 1-c^2
    let x := evalJ A B (rJet m r) (cJet c) (normFormula m a)
    let y := evalJ A B (rJet m r) (cJet c) (twistFormula m a)
    x.value*x.lap = pairing A B x x - pairing A B y y ∧
    x.value*y.lap = 2*pairing A B x y := by
  have hden : r*r+a^2*(c*c) ≠ 0 := (add_pos_of_pos_of_nonneg (mul_pos hr hr)
    (mul_nonneg (sq_nonneg a) (mul_self_nonneg c))).ne'
  constructor <;>
    simp only [normFormula,twistFormula,f_add,f_sub,f_mul,f_div,evalJ,rJet,cJet,constJ,subJ,addJ,redMul,redDiv,pairing] <;>
    simp only [zero_add,add_zero,zero_mul,mul_zero,one_mul,mul_one,sub_self] <;>
    field_simp [hden] <;> ring
private theorem prolate_pairing (w u c k : ℝ) (hd : 0 < u^2-k^2*c^2)
    (hw : w = (u^2-k^2)*(1-c^2)) :
    PreservesPairing w (u^2-k^2) (1-c^2) (radialJ w u c k) (polarJ w u c k)
      (w/(u^2-k^2*c^2)) := by
  intro x y
  subst w
  dsimp [toWeyl,pairing,radialJ,polarJ]
  field_simp (disch := first | positivity | grind)
  ring

open NoHair

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    ∀ p : OrbitPoint,
      let v := kerrErnst m a
      v.normSq p * scaledLaplacian v.normSq p =
        scaledGradientPair v.normSq v.normSq p - scaledGradientPair v.twist v.twist p ∧
      v.normSq p * scaledLaplacian v.twist p = 2*scaledGradientPair v.normSq v.twist p := by
  intro p
  let k := Real.sqrt (m^2-a^2)
  let U := prolateRadius k
  let r := fun q => m+U q
  let c := fun q : OrbitPoint => q.2/U q
  let u := U p
  let v := c p
  let w := weight p
  let A := (r p)^2-2*m*r p+a^2
  let B := 1-v^2
  let t := w/(u^2-k^2*v^2)
  let R := radialJ w u v k
  let C := polarJ w u v k
  obtain ⟨hu,hd,hw,hU,hC⟩ := prolate_jets k p
  have hk : k^2 = m^2-a^2 := Real.sq_sqrt (by nlinarith [hm.2])
  have hA : A = u^2-k^2 := by change (m+u)^2-2*m*(m+u)+a^2 = u^2-k^2; rw [hk]; ring
  have hp : PreservesPairing (weight p) A B R C t := hA ▸ prolate_pairing w u v k hd hw
  have hr : ContDiff ℝ 2 r := contDiff_const.add (radial_smooth k)
  have hpos (q) : 0 < r q := add_pos hm.1 ((abs_nonneg _).trans_lt (prolate_gt_abs k q))
  have hjr : jetAt p r = toWeyl R C t (rJet m (r p)) := by
    change jetAt p (fun q => m + prolateRadius k q) = _
    rw [jet_add contDiff_const (radial_smooth k) p,jet_const,hU]
    change addJ (constJ m) R = _
    apply Jet.ext <;> dsimp [toWeyl,R,C,t,radialJ,polarJ,rJet,addJ,constJ,r,u] <;> ring
  have hjc : jetAt p c = toWeyl R C t (cJet v) := by
    change jetAt p (fun q => q.2/prolateRadius k q) = _
    rw [hC]
    change C = _
    apply Jet.ext <;> dsimp [toWeyl,C,R,t,radialJ,polarJ,cJet] <;> ring
  let x := evalJ A B (rJet m (r p)) (cJet v) (normFormula m a)
  let y := evalJ A B (rJet m (r p)) (cJet v) (twistFormula m a)
  have jx : jetAt p (kerrErnst m a).normSq = toWeyl R C t x := by
    have h : (kerrErnst m a).normSq = fun q => evalF (r q) (c q) (normFormula m a) :=
      funext fun q => (formula_values m a (r q) (c q)).1.symm
    rw [h]
    exact (transfer r c hr (polar_smooth k) p R C _ _ A B t hp hjr hjc (normFormula m a)
      (fun q => (formulas_defined m a (r q) (c q) (hpos q)).1)).2
  have jy : jetAt p (kerrErnst m a).twist = toWeyl R C t y := by
    have h : (kerrErnst m a).twist = fun q => evalF (r q) (c q) (twistFormula m a) :=
      funext fun q => (formula_values m a (r q) (c q)).2.symm
    rw [h]
    exact (transfer r c hr (polar_smooth k) p R C _ _ A B t hp hjr hjc (twistFormula m a)
      (fun q => (formulas_defined m a (r q) (c q) (hpos q)).2)).2
  have eqs : x.value*x.lap = pairing A B x x - pairing A B y y ∧
      x.value*y.lap = 2*pairing A B x y := rational_identities m a (r p) v (hpos p)
  have grad (f g : OrbitPoint → ℝ) :
      scaledGradientPair f g p = pairing 1 (weight p) (jetAt p f) (jetAt p g) := by
    dsimp [scaledGradientPair,pairing,jetAt,ds,dz,direction,weight]
    ring
  dsimp only
  rw [grad,grad,grad]
  change (jetAt p (kerrErnst m a).normSq).value*(jetAt p (kerrErnst m a).normSq).lap = _ ∧
    (jetAt p (kerrErnst m a).normSq).value*(jetAt p (kerrErnst m a).twist).lap = _
  rw [jx,jy,hp x x,hp y y,hp x y]
  change x.value*(t*x.lap) = _ ∧ x.value*(t*y.lap) = _
  constructor
  · calc
      _ = t*(x.value*x.lap) := by ring
      _ = _ := by rw [eqs.1]; ring
  · calc
      _ = t*(x.value*y.lap) := by ring
      _ = _ := by rw [eqs.2]; ring
