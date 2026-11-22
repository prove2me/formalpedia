-- Prove2me | solution 1 for NoHair.Weyl.kerr_radial_rate_identities
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:22:34.236856+00:00
-- url     : https://prove2.me/submissions/be50f890-3e82-4e88-a5f7-3602525795f1

import Definitions.Def_NoHair_kerrWeylCoefficients
import Theorems.Thm_NoHair_Weyl_prolate_coordinate_differentials

noncomputable section

open NoHair NoHair.Weyl

/-- Polynomials in the Boyer–Lindquist radius and polar cosine. -/
private inductive OrbitPoly
  | scalar (b : ℝ) | r | c
  | add (f g : OrbitPoly) | sub (f g : OrbitPoly) | mul (f g : OrbitPoly)

private instance : Add OrbitPoly := ⟨OrbitPoly.add⟩
private instance : Sub OrbitPoly := ⟨OrbitPoly.sub⟩
private instance : Mul OrbitPoly := ⟨OrbitPoly.mul⟩
private theorem op_add (f g : OrbitPoly) : f+g = .add f g := rfl
private theorem op_sub (f g : OrbitPoly) : f-g = .sub f g := rfl
private theorem op_mul (f g : OrbitPoly) : f*g = .mul f g := rfl

private def val (r c : ℝ) : OrbitPoly → ℝ
  | .scalar b => b | .r => r | .c => c
  | .add f g => val r c f+val r c g | .sub f g => val r c f-val r c g
  | .mul f g => val r c f*val r c g

private def polySlope (r c v w : ℝ) : OrbitPoly → ℝ
  | .scalar _ => 0 | .r => v | .c => w
  | .add f g => polySlope r c v w f+polySlope r c v w g
  | .sub f g => polySlope r c v w f-polySlope r c v w g
  | .mul f g => polySlope r c v w f*val r c g+val r c f*polySlope r c v w g

private def quotientSlope (r c v w : ℝ) (f g : OrbitPoly) :=
  polySlope r c v w f*val r c g-val r c f*polySlope r c v w g

private theorem poly_path {r c : ℝ → ℝ} {p v w D : ℝ}
    (hr : HasDerivAt r (v/D) p) (hc : HasDerivAt c (w/D) p) (f : OrbitPoly) :
    HasDerivAt (fun t => val (r t) (c t) f) (polySlope (r p) (c p) v w f/D) p := by
  induction f with
  | scalar b => simpa [polySlope,val] using hasDerivAt_const p b
  | r => exact hr
  | c => exact hc
  | add f g ih jh =>
    change HasDerivAt (fun t => val (r t) (c t) f+val (r t) (c t) g) ((polySlope (r p) (c p) v w f+polySlope (r p) (c p) v w g)/D) p
    apply (ih.fun_add jh).congr_deriv
    ring
  | sub f g ih jh =>
    change HasDerivAt (fun t => val (r t) (c t) f-val (r t) (c t) g) ((polySlope (r p) (c p) v w f-polySlope (r p) (c p) v w g)/D) p
    apply (ih.fun_sub jh).congr_deriv
    ring
  | mul f g ih jh =>
    change HasDerivAt (fun t => val (r t) (c t) f*val (r t) (c t) g) ((polySlope (r p) (c p) v w f*val (r p) (c p) g+val (r p) (c p) f*polySlope (r p) (c p) v w g)/D) p
    apply (ih.fun_mul jh).congr_deriv
    ring

private theorem quotient_path {r c : ℝ → ℝ} {p v w D : ℝ}
    (hr : HasDerivAt r (v/D) p) (hc : HasDerivAt c (w/D) p) (f g : OrbitPoly)
    (hg : val (r p) (c p) g ≠ 0) :
    HasDerivAt (fun t => val (r t) (c t) f/val (r t) (c t) g)
      (quotientSlope (r p) (c p) v w f g/(D*(val (r p) (c p) g)^2)) p := by
  unfold quotientSlope
  apply ((poly_path hr hc f).fun_div (poly_path hr hc g) hg).congr_deriv
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

private def sinP := OrbitPoly.scalar 1-OrbitPoly.c*OrbitPoly.c
private def sigmaP (a : ℝ) := OrbitPoly.r*OrbitPoly.r+OrbitPoly.scalar (a^2)*(OrbitPoly.c*OrbitPoly.c)
private def axialP (m a : ℝ) :=
  (OrbitPoly.r*OrbitPoly.r+OrbitPoly.scalar (a^2))*sigmaP a+
    OrbitPoly.scalar (2*m)*OrbitPoly.r*OrbitPoly.scalar (a^2)*sinP
private def normP (m a : ℝ) := sinP*axialP m a
private def twistP (m a : ℝ) :=
  let c := OrbitPoly.c
  OrbitPoly.scalar (2*m*a)*(OrbitPoly.scalar 3*c-c*c*c)*sigmaP a+
    OrbitPoly.scalar (2*m*a^3)*c*(sinP*sinP)
private def shiftP (m a : ℝ) := OrbitPoly.scalar (-(2*m*a))*OrbitPoly.r
private def discP (m a : ℝ) :=
  let u := OrbitPoly.r-OrbitPoly.scalar m
  u*u-OrbitPoly.scalar (m^2-a^2)*(OrbitPoly.c*OrbitPoly.c)

private theorem potential_ratios (m a r c : ℝ) (hr : 0 < r) :
    kerrAxialNorm m a r c = val r c (normP m a)/val r c (sigmaP a) ∧
    kerrAxialTwist m a r c = val r c (twistP m a)/val r c (sigmaP a) := by
  have hq : r^2+a^2*c^2 ≠ 0 := by positivity
  constructor <;>
    simp only [kerrAxialNorm,kerrAxialTwist,normP,twistP,axialP,sigmaP,sinP,
      op_add,op_sub,op_mul,val,← sq] <;>
    field_simp (disch := first | positivity | grind) <;> ring

private theorem scale_ratios (m a r c : ℝ) :
    -(2*m*a*r)/kerrAxialNumerator m a r c = val r c (shiftP m a)/val r c (axialP m a) ∧
    (1-c^2)*kerrAxialNumerator m a r c/((r-m)^2-(m^2-a^2)*c^2) =
      val r c (normP m a)/val r c (discP m a) := by
  constructor <;>
    simp only [normP,axialP,shiftP,discP,sigmaP,sinP,kerrAxialNumerator,
      op_add,op_sub,op_mul,val,pow_two] <;> ring

/- Both radial rate identities after clearing their common positive denominators. -/
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 20000 in
private theorem rate_polynomials (m a r c : ℝ) :
    let u := r-m
    let A := r^2-2*m*r+a^2
    let B := 1-c^2
    let w := A*B
    let S := quotientSlope r c (w*u) (-w*c)
    let Z := quotientSlope r c (c*A) (u*B)
    let x := normP m a
    let y := twistP m a
    let q := sigmaP a
    let n := axialP m a
    S (shiftP m a) n*(val r c x)^2 = w*Z y q*(val r c n)^2 ∧
    2*val r c x*(val r c q)^2*S x (discP m a) =
      (S x q)^2+(S y q)^2-w*((Z x q)^2+(Z y q)^2) := by
  constructor <;>
    simp only [quotientSlope,shiftP,discP,normP,twistP,sigmaP,sinP,axialP,
      op_add,op_sub,op_mul,val,polySlope,zero_mul,mul_zero,one_mul,mul_one,add_zero,zero_add] <;>
    ring
private theorem restore_rates (w x q n d sw zy sx sy zx sh : ℝ)
    (hx : x ≠ 0) (hq : q ≠ 0) (hn : n ≠ 0) (hd : d ≠ 0)
    (h₁ : sw*x^2=w*zy*n^2)
    (h₂ : 2*x*q^2*sh=sx^2+sy^2-w*(zx^2+zy^2)) :
    sw/(d*n^2) = w*(zy/(d*q^2))/(x/q)^2 ∧
    (sh/(d*d^2))/(x/d)/2-1 =
      ((sx/(d*q^2))^2+(sy/(d*q^2))^2-w*((zx/(d*q^2))^2+(zy/(d*q^2))^2))/
        (4*(x/q)^2)-1 := by
  constructor
  · calc
      _ = (sw*x^2)/(d*n^2*x^2) := by field_simp [hx,hn,hd] <;> ring
      _ = _ := by rw [h₁]; field_simp [hx,hq,hn,hd] <;> ring
  · calc
      _ = (2*x*q^2*sh)/(4*d^2*q^2*x^2)-1 := by field_simp [hx,hq,hd] <;> ring
      _ = _ := by rw [h₂]; field_simp [hx,hq,hd] <;> ring

private theorem poly_diff {r c : OrbitPoint → ℝ} (hr : Differentiable ℝ r) (hc : Differentiable ℝ c)
    (f : OrbitPoly) : Differentiable ℝ (fun p => val (r p) (c p) f) := by
  induction f with
  | scalar b => exact differentiable_const b
  | r => exact hr
  | c => exact hc
  | add f g hf hg => exact hf.fun_add hg
  | sub f g hf hg => exact hf.fun_sub hg
  | mul f g hf hg => exact hf.fun_mul hg

private theorem slice_s {f : OrbitPoint → ℝ} (hf : Differentiable ℝ f) (s z : ℝ) :
    HasDerivAt (fun t : ℝ => f (t,z)) (ds f (s,z)) s :=
  (hf (s,z)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))

private theorem slice_z {f : OrbitPoint → ℝ} (hf : Differentiable ℝ f) (s z : ℝ) :
    HasDerivAt (fun t : ℝ => f (s,t)) (dz f (s,z)) z :=
  (hf (s,z)).hasFDerivAt.comp_hasDerivAt z ((hasDerivAt_const z s).prodMk (hasDerivAt_id z))

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    ∀ s z : ℝ, 0 < kerrWeylScale m a (s,z) ∧
      HasDerivAt (fun t => kerrWeylShift m a (t,z)) (shiftRate (kerrErnst m a) (s,z)) s ∧
      HasDerivAt (fun t => Real.log (kerrWeylScale m a (t,z))/2-t)
        (conformalRate (kerrErnst m a) (s,z)) s := by
  intro s z
  let p : OrbitPoint := (s,z)
  let k := Real.sqrt (m^2-a^2)
  let U := prolateRadius k
  let r := fun q => m+U q
  let c := fun q : OrbitPoint => q.2/U q
  let u := U p
  let v := c p
  let w := Real.exp (2*s)
  let A := (r p)^2-2*m*r p+a^2
  let B := 1-v^2
  let D := u^2-k^2*v^2
  let V := fun f q => val (r q) (c q) f
  let R := fun f g q => V f q/V g q
  let S := quotientSlope (r p) v (w*u) (-w*v)
  let Z := quotientSlope (r p) v (v*A) (u*B)
  let x := normP m a
  let y := twistP m a
  let n := axialP m a
  let Q := sigmaP a
  let d := discP m a
  let g := shiftP m a
  obtain ⟨hU,hc,coord⟩ := prolate_coordinate_differentials k
  obtain ⟨hu,hB,hD,hw,hus,huz,hcs,hcz⟩ := coord p
  have hk : k^2=m^2-a^2 := Real.sq_sqrt (by nlinarith [hm.2])
  have hA : u^2-k^2=A := by change u^2-k^2=(m+u)^2-2*m*(m+u)+a^2; rw [hk]; ring
  have hdiff : r p-m=u := by change m+u-m=u; ring
  have hd : V d p = D := by
    change val (r p) v (discP m a) = _
    simp only [discP,op_sub,op_mul,val,hdiff,← sq,D,hk]
  have wAB : w=A*B := hw.trans (congrArg (fun t => t*B) hA)
  have rp (q) : 0 < r q := add_pos hm.1 (coord q).1
  have qpos (q) : 0 < V Q q := by
    change 0 < val (r q) (c q) (sigmaP a)
    simp only [sigmaP,op_add,op_mul,val,← sq]
    have := rp q
    positivity
  have np : 0 < V n p := by
    change 0 < val (r p) v (axialP m a)
    simp only [axialP,sigmaP,sinP,op_add,op_sub,op_mul,val,← sq]
    have := rp p
    have := hm.1
    change 0 < 1-v^2 at hB
    positivity
  have xp : 0 < V x p := by
    change 0 < val (r p) v (normP m a)
    exact mul_pos (by simpa only [sinP,op_sub,op_mul,val,← sq] using hB) np
  have dp : 0 < V d p := hd ▸ hD
  have Xeq : (kerrErnst m a).normSq = R x Q :=
    funext fun t => (potential_ratios m a (r t) (c t) (rp t)).1
  have Yeq : (kerrErnst m a).twist = R y Q :=
    funext fun t => (potential_ratios m a (r t) (c t) (rp t)).2
  have Weq : kerrWeylShift m a = R g n := funext fun t => (scale_ratios m a (r t) (c t)).1
  have Heq : kerrWeylScale m a = R x d := funext fun t => (scale_ratios m a (r t) (c t)).2
  have hr' : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hc' : Differentiable ℝ c := hc.differentiable (by norm_num)
  have hr : Differentiable ℝ r := (differentiable_const m).add hr'
  have drs : HasDerivAt (fun t => r (t,z)) (w*u/D) s := by
    exact (hus ▸ slice_s hr' s z).const_add m
  have drz : HasDerivAt (fun t => r (s,t)) (v*A/D) z := by
    simpa only [← hA] using (huz ▸ slice_z hr' s z).const_add m
  have dcs : HasDerivAt (fun t => c (t,z)) (-w*v/D) s := hcs ▸ slice_s hc' s z
  have dcz : HasDerivAt (fun t => c (s,t)) (u*B/D) z := hcz ▸ slice_z hc' s z
  have derS (f h) (hn : V h p ≠ 0) :
      HasDerivAt (fun t => R f h (t,z)) (S f h/(D*(V h p)^2)) s :=
    quotient_path drs dcs f h hn
  have derZ (f h) (hn : V h p ≠ 0) :
      HasDerivAt (fun t => R f h (s,t)) (Z f h/(D*(V h p)^2)) z :=
    quotient_path drz dcz f h hn
  have dif (f) : Differentiable ℝ (R f Q) := by
    change Differentiable ℝ (fun t => val (r t) (c t) f / val (r t) (c t) Q)
    simp only [div_eq_mul_inv]
    exact (poly_diff hr hc' f).fun_mul ((poly_diff hr hc' Q).inv fun q => (qpos q).ne')
  have dsQ (f) : ds (R f Q) p = S f Q/(D*(V Q p)^2) :=
    (slice_s (dif f) s z).unique (derS f Q (qpos p).ne')
  have dzQ (f) : dz (R f Q) p = Z f Q/(D*(V Q p)^2) :=
    (slice_z (dif f) s z).unique (derZ f Q (qpos p).ne')
  have eqs := rate_polynomials m a (r p) v
  change _ ∧ _ at eqs
  rw [hdiff,← wAB] at eqs
  obtain ⟨rw₁,rw₂⟩ := restore_rates w (V x p) (V Q p) (V n p) D (S g n) (Z y Q)
    (S x Q) (S y Q) (Z x Q) (S x d) xp.ne' (qpos p).ne' np.ne' hD.ne' eqs.1 eqs.2
  have hpos : 0 < R x d p := div_pos xp dp
  rw [Weq,Heq]
  refine ⟨hpos,?_,?_⟩
  · unfold shiftRate
    rw [Xeq,Yeq,dzQ y]
    exact rw₁ ▸ derS g n np.ne'
  · unfold conformalRate
    rw [Xeq,Yeq,dsQ x,dsQ y,dzQ x,dzQ y]
    have hlog := (((derS x d dp.ne').log hpos.ne').div_const 2).fun_sub (hasDerivAt_id' s)
    change HasDerivAt _ (((S x d/(D*(V d p)^2))/(V x p/V d p))/2-1) s at hlog
    rw [hd] at hlog
    exact rw₂ ▸ hlog
