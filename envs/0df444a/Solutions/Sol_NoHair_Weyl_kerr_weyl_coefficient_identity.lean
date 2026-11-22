-- Prove2me | solution 1 for NoHair.Weyl.kerr_weyl_coefficient_identity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:36:23.651456+00:00
-- url     : https://prove2.me/submissions/c0a5a9fc-7919-4306-99f5-5831600a4ecc

import Definitions.Def_NoHair_kerrWeylModel
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair NoHair.Weyl Set Filter
open scoped Topology ContDiff Manifold

noncomputable section

private theorem prolate_inverse (k x v ρ : ℝ) (hk : 0 ≤ k) (hx : k < x)
    (hv : |v| < 1) (hρ : 0 < ρ) (hsq : ρ^2 = (x^2-k^2)*(1-v^2)) :
    prolateRadius k (Real.log ρ, x*v) = x := by
  have h₁ : 0 ≤ x-k*v := by
    nlinarith [mul_nonneg hk (sub_nonneg.mpr (abs_lt.mp hv).2.le)]
  have h₂ : 0 ≤ x+k*v := by
    nlinarith [mul_nonneg hk (show 0 ≤ 1+v by linarith [(abs_lt.mp hv).1])]
  have he : Real.exp (2*Real.log ρ) = ρ^2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hρ, sq]
  have hn : ρ^2+(x*v-k)^2 = (x-k*v)^2 := by rw [hsq]; ring
  have hs : ρ^2+(x*v+k)^2 = (x+k*v)^2 := by rw [hsq]; ring
  unfold prolateRadius
  dsimp only
  rw [he, hn, hs, Real.sqrt_sq h₁, Real.sqrt_sq h₂]
  ring

private theorem plane_metric (r a v : ℝ) (hr : 0 < r) (hv : 0 < 1-v^2)
    (X Y v₁ v₂ v₃ u₁ u₂ u₃ d e f g h j : ℝ)
    (hQ : X^2+Y^2 = (r^2+a^2)*(1-v^2))
    (hL : X*v₁+Y*v₂ = r*(1-v^2)*d-(r^2+a^2)*v*f)
    (hL' : X*u₁+Y*u₂ = r*(1-v^2)*e-(r^2+a^2)*v*g)
    (hK : X*v₂-Y*v₁ = (X^2+Y^2)*h)
    (hK' : X*u₂-Y*u₁ = (X^2+Y^2)*j)
    (hZ : v₃ = v*d+r*f) (hZ' : u₃ = v*e+r*g) :
    v₁*u₁+v₂*u₂+v₃*u₃ =
      (r^2+a^2*v^2)/(r^2+a^2)*d*e + (r^2+a^2*v^2)/(1-v^2)*f*g +
      (r^2+a^2)*(1-v^2)*h*j := by
  have hs : 0 < r^2+a^2 := by positivity
  have hq : 0 < X^2+Y^2 := by rw [hQ]; exact mul_pos hs hv
  have hp : v₁*u₁+v₂*u₂ =
      ((X*v₁+Y*v₂)*(X*u₁+Y*u₂)+(X*v₂-Y*v₁)*(X*u₂-Y*u₁))/(X^2+Y^2) := by
    apply (eq_div_iff hq.ne').2
    ring
  rw [hp, hL, hL', hK, hK', hQ, hZ, hZ']
  field_simp [hs.ne', hv.ne']
  ring

private theorem orbit_metric (x k v ρ d e f g h j l n : ℝ)
    (hA : 0 < x^2-k^2) (hB : 0 < 1-v^2) (hρ : 0 < ρ)
    (hρ₂ : ρ^2 = (x^2-k^2)*(1-v^2))
    (hs : ρ*h = x*(1-v^2)*d-(x^2-k^2)*v*f)
    (hs' : ρ*j = x*(1-v^2)*e-(x^2-k^2)*v*g)
    (hz : l = v*d+x*f) (hz' : n = v*e+x*g) :
    h*j+l*n = (x^2-k^2*v^2)/(x^2-k^2)*d*e + (x^2-k^2*v^2)/(1-v^2)*f*g := by
  have hp : h*j = ((ρ*h)*(ρ*j))/ρ^2 := by field_simp <;> ring
  rw [hp, hs, hs', hρ₂, hz, hz']
  field_simp [hA.ne', hB.ne']
  ring

set_option maxHeartbeats 2400000 in
private theorem time_azimuth_metric (S M a B t u d e h j : ℝ)
    (hS : S ≠ 0) (hA : S-M ≠ 0) (hB : B ≠ 0) (hsig : S-a^2*B ≠ 0)
    (hP : S*(S-a^2*B)+M*a^2*B ≠ 0) :
    let sig := S-a^2*B
    let A := S-M
    let P := S*sig+M*a^2*B
    let X := B*P/sig
    let w := -(M*a)/P
    let t₁ := t-(M/A)*d
    let t₂ := u-(M/A)*e
    let φ₁ := h-(M*a/(A*S))*d
    let φ₂ := j-(M*a/(A*S))*e;
    -(t*u)+sig/S*d*e+S*B*h*j+
      M/sig*(t+sig/S*d-a*B*h)*(u+sig/S*e-a*B*j) =
      -(A*B/X)*t₁*t₂+X*(φ₁+w*t₁)*(φ₂+w*t₂)+sig/A*d*e := by
  dsimp only
  let sig := S-a^2*B
  let A := S-M
  let P := S*sig+M*a^2*B
  let X := B*P/sig
  let w := -(M*a)/P
  have hid (C F : ℝ) (hC : C ≠ 0) (hF : F ≠ 0)
      (hCeq : C=S-a^2*B) (hFeq : F=S*C+M*a^2*B) :
      -((S-M)*B/(B*F/C))+(B*F/C)*(-(M*a)/F)^2 = -1+M/C ∧
      (B*F/C)*(-(M*a)/F) = -(M*a*B)/C := by
    constructor <;> field_simp [hC,hF,hB] <;> simp only [hFeq,hCeq] <;> ring
  obtain ⟨h₀,h₁⟩ := hid sig P hsig hP rfl rfl
  change -(A*B/X)+X*w^2 = -1+M/sig at h₀
  change X*w = -(M*a*B)/sig at h₁
  have hexp (T T' Φ Φ' : ℝ) :
      -(A*B/X)*T*T'+X*(Φ+w*T)*(Φ'+w*T') =
        (-1+M/sig)*T*T' + (-(M*a*B)/sig)*(T*Φ'+Φ*T') + X*Φ*Φ' := by
    rw [← h₀, ← h₁]
    ring
  change _ = (-(A*B/X)*_*_+X*(_+w*_)*(_+w*_))+sig/A*d*e
  rw [hexp]
  dsimp [X,P,A,sig]
  field_simp [hsig,hA,hS]
  ring

private theorem null_coefficient (a : ℝ) (y : E4) (i : Fin 4) :
    let r := ksRadius a y
    let e := coordBasis i
    ksNull a y i = e 0 +
      (r*(y 1*e 1+y 2*e 2)-a*(y 1*e 2-y 2*e 1))/(r^2+a^2) + (y 3/r)*e 3 := by
  fin_cases i <;> simp [ksNull, coordBasis, PiLp.single_apply] <;> ring

private theorem flat_coefficient (i j : Fin 4) :
    minkowski i j = -((coordBasis i) 0*(coordBasis j) 0) +
      ((coordBasis i) 1*(coordBasis j) 1+(coordBasis i) 2*(coordBasis j) 2+
        (coordBasis i) 3*(coordBasis j) 3) := by
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [minkowski, Matrix.diagonal_apply, coordBasis, PiLp.single_apply]

private theorem orbit_differentials (m a : ℝ) (V : Set E4) (coord : E4 → E4)
    (hc : IsKerrWeylChart m a V coord) (y : E4) (hy : y ∈ V) (i : Fin 4)
    (hr : 0 < ksRadius a y) (hA : 0 < kerrDelta m a (ksRadius a y))
    (hB : 0 < 1-(y 3/ksRadius a y)^2) :
    let r := ksRadius a y
    let v := y 3/r
    let e := coordBasis i
    let dr := coordPartial (ksRadius a) i y
    let dv := (e 3-v*dr)/r
    let b := fderiv ℝ coord y e
    (coord y) 2 * b 2 = (r-m)*(1-v^2)*dr-kerrDelta m a r*v*dv ∧
    b 3 = v*dr+(r-m)*dv := by
  let r := ksRadius a y
  let v := y 3/r
  let e := coordBasis i
  let dr := coordPartial (ksRadius a) i y
  let dv := (e 3-v*dr)/r
  let line := fun t : ℝ => y+t • e
  let R := fun t => ksRadius a (line t)
  let C := fun t => (line t) 3/R t
  have hl : HasDerivAt line e 0 := by
    simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add y
  have hl₀ : line 0 = y := by simp [line]
  have hR₀ : R 0 = r := by simp [R,hl₀,r]
  have hC₀ : C 0 = v := by simp [C,hl₀,hR₀,v]
  have hR : HasDerivAt R dr 0 := by
    have h : HasFDerivAt (ksRadius a) (fderiv ℝ (ksRadius a) y) (line 0) := by
      rw [hl₀]; exact (ksRadius_differentiableAt a y hr).hasFDerivAt
    exact h.comp_hasDerivAt 0 hl
  have hZ : HasDerivAt (fun t => (line t) 3) (e 3) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (3 : Fin 4)).hasFDerivAt.comp_hasDerivAt 0 hl
  have hC : HasDerivAt C dv 0 := by
    apply (hZ.div hR (by rw [hR₀]; exact hr.ne')).congr_deriv
    rw [hl₀,hR₀]
    dsimp [dv,v]
    have hr' : r ≠ 0 := hr.ne'
    field_simp [hr'] <;> ring
  obtain ⟨_,_,_,_,_,hsmooth,_⟩ := hc.diffeo
  have hd := ((hsmooth.contDiffOn.differentiableOn (by norm_num)) y hy).differentiableAt
    (hc.source_open.mem_nhds hy)
  have hF : HasDerivAt (fun t => coord (line t)) (fderiv ℝ coord y e) 0 := by
    have h : HasFDerivAt coord (fderiv ℝ coord y) (line 0) := by
      rw [hl₀]; exact hd.hasFDerivAt
    exact h.comp_hasDerivAt 0 hl
  have hb (j : Fin 4) : HasDerivAt (fun t => (coord (line t)) j) (fderiv ℝ coord y e j) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt 0 hF
  have hA' : HasDerivAt (fun t => kerrDelta m a (R t)) ((2*r-2*m)*dr) 0 := by
    apply (((hR.pow 2).sub (hR.const_mul (2*m))).add_const (a^2)).congr_deriv
    simp [hR₀]
    <;> ring
  have hB' : HasDerivAt (fun t => 1-C t^2) (-2*v*dv) 0 := by
    apply ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hC.pow 2)).congr_deriv
    simp [hC₀] <;> ring
  have hvn : ∀ᶠ t in 𝓝 (0:ℝ), line t ∈ V := hl.continuousAt.preimage_mem_nhds
    (by rw [hl₀]; exact hc.source_open.mem_nhds hy)
  have ha0 : 0 < kerrDelta m a (R 0) := by rw [hR₀]; exact hA
  have hb0 : 0 < 1-C 0^2 := by rw [hC₀]; exact hB
  have haN := hA'.continuousAt.eventually (lt_mem_nhds ha0)
  have hbN := hB'.continuousAt.eventually (lt_mem_nhds hb0)
  have hρeq : (fun t => ((coord (line t)) 2)^2) =ᶠ[𝓝 (0:ℝ)]
      (fun t => kerrDelta m a (R t)*(1-C t^2)) := by
    filter_upwards [hvn,haN,hbN] with t ht ha hb₀
    rw [(hc.orbit _ ht).1, mul_pow, Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt (le_of_lt hb₀)]
  have hzeq : (fun t => (coord (line t)) 3) =ᶠ[𝓝 (0:ℝ)] (fun t => (R t-m)*C t) := by
    filter_upwards [hvn] with t ht using (hc.orbit _ ht).2
  have hz := (hb 3).unique (((hR.sub_const m).mul hC).congr_of_eventuallyEq hzeq)
  have hρ := ((hb 2).pow 2).unique ((hA'.mul hB').congr_of_eventuallyEq hρeq)
  simp only [hR₀,hC₀,hl₀, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hz hρ
  constructor
  · change _ = (r-m)*(1-v^2)*dr-kerrDelta m a r*v*dv
    linear_combination (1 / 2 : ℝ) * hρ
  · change _ = v*dr+(r-m)*dv
    linear_combination hz

set_option maxHeartbeats 2400000 in
theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0)
    (V : Set E4) (coord : E4 → E4) (hc : IsKerrWeylChart m a V coord) (y : E4) (hy : y ∈ V) :
    let p : OrbitPoint := (Real.log ((coord y) 2), (coord y) 3)
    let k := Real.sqrt (m^2-a^2)
    let x := prolateRadius k p
    let r := m+x
    let c := p.2/x
    let B := 1-c^2
    let P := (r^2+a^2)^2-a^2*kerrDelta m a r*B
    let D := x^2-k^2*c^2
    angularShift (kerrErnst m a) p = -(2*m*r*a)/P →
    Real.exp (2*conformalExponent (kerrErnst m a) p) = B*P/D →
    kerrNewmanMetric m a 0 y = metricInChart (kerrErnst m a) coord y := by
  dsimp only
  intro hw hh
  let r := ksRadius a y
  let x := r-m
  let v := y 3/r
  let k := Real.sqrt (m^2-a^2)
  let B := 1-v^2
  let S := r^2+a^2
  let σ := r^2+a^2*v^2
  let Q := y 1^2+y 2^2
  let A := kerrDelta m a r
  let M := 2*m*r
  let P := S^2-a^2*A*B
  let D := x^2-k^2*v^2
  let ρ := (coord y) 2
  let p : OrbitPoint := (Real.log ρ,(coord y) 3)
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hk2 : k^2 = m^2-a^2 := Real.sq_sqrt (by nlinarith [hm.2])
  have hD0 := (hc.off_axis hy).1
  change m+Real.sqrt (m^2-a^2-0^2) < r at hD0
  have hs0 : m+k < r := by simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using hD0
  have hx : k < x := by dsimp [x]; linarith
  have hx0 : 0 < x := hk.trans_lt hx
  have hr : 0 < r := (add_pos_of_pos_of_nonneg hm.1 hk).trans hs0
  have hS : 0 < S := by dsimp [S]; positivity
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hM : 0 < M := by dsimp [M]; have := hm.1; positivity
  have hvz : y 3 = r*v := by dsimp [v]; field_simp [hr.ne']
  have hQ : Q = S*B := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hr.ne')
    have e := ks_C a y hr
    change r^4-(y 1^2+y 2^2+y 3^2-a^2)*r^2-a^2*y 3^2=0 at e
    rw [hvz] at e
    dsimp only [Q,S,B]
    linear_combination -e
  have hQpos : 0 < Q := by
    rcases (hc.off_axis hy).2 with h | h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h)
  have hB : 0 < B := (mul_pos_iff_of_pos_left hS).1 (hQ ▸ hQpos)
  have habs : |v| < 1 := (sq_lt_one_iff_abs_lt_one v).1 (sub_pos.mp hB)
  have hArod : A = x^2-k^2 := by dsimp only [A,kerrDelta,x]; rw [hk2]; ring
  have hA : 0 < A := by rw [hArod]; nlinarith only [mul_pos (sub_pos.mpr hx) (add_pos_of_pos_of_nonneg hx0 hk)]
  have hD : 0 < D := by
    have hd : D=A+k^2*B := by rw [hArod]; dsimp [D,B]; ring
    rw [hd]
    positivity
  have hσid : S-a^2*B=σ := by dsimp [S,σ,B]; ring
  have hσpol : σ=r^2*B+S*v^2 := by dsimp [σ,S,B]; ring
  have hAid : S-M=A := by dsimp [M,S,A,kerrDelta]; ring
  have hPid : S*σ+M*a^2*B=P := by
    dsimp [P,S,σ,M,B,A,kerrDelta]
    ring
  have hP : 0 < P := by rw [← hPid]; positivity
  have hρ : 0 < ρ := hc.pos y hy
  obtain ⟨hρform,hzform⟩ := hc.orbit y hy
  have hρ2 : ρ^2 = A*B := by
    change (coord y 2)^2 = _
    rw [hρform,mul_pow,Real.sq_sqrt hA.le,Real.sq_sqrt hB.le]
  have hz : (coord y) 3 = x*v := hzform
  have href : prolateRadius k p=x := by
    change prolateRadius k (Real.log ρ,(coord y) 3)=x
    rw [hz]
    exact prolate_inverse k x v ρ hk hx habs hρ (by simpa only [← hArod] using hρ2)
  have hrefR : m+x=r := by dsimp [x]; ring
  have hrefC : p.2/x=v := by
    change (coord y) 3/x=v
    rw [hz]
    field_simp [hx0.ne']
  have hw' : angularShift (kerrErnst m a) p = -(M*a)/P := by
    change angularShift (kerrErnst m a) p = -(2*m*(m+prolateRadius k p)*a) /
      (((m+prolateRadius k p)^2+a^2)^2-a^2*kerrDelta m a (m+prolateRadius k p)*
       (1-(p.2/prolateRadius k p)^2)) at hw
    rw [href,hrefR,hrefC] at hw
    exact hw
  have hh' : Real.exp (2*conformalExponent (kerrErnst m a) p) = B*P/D := by
    change Real.exp (2*conformalExponent (kerrErnst m a) p) =
      (1-(p.2/prolateRadius k p)^2) * (((m+prolateRadius k p)^2+a^2)^2-
       a^2*kerrDelta m a (m+prolateRadius k p)*(1-(p.2/prolateRadius k p)^2)) /
       ((prolateRadius k p)^2-k^2*(p.2/prolateRadius k p)^2) at hh
    rw [href,hrefR,hrefC] at hh
    exact hh
  have hnorm : (kerrErnst m a).normSq p = B*P/σ := by
    change kerrAxialNorm m a (m+prolateRadius k p) (p.2/prolateRadius k p)=_
    rw [href,hrefR,hrefC]
    change B*(S+M*a^2*B/σ)=_
    rw [← hPid]
    field_simp [hσ.ne'] <;> ring
  have hden : r^4+a^2*(r*v)^2=r^2*σ := by dsimp [σ]; ring
  have hprof : ksProfile m a 0 y = M/σ := by
    change r^2*(2*m*r-0^2)/(r^4+a^2*y 3^2)=_
    rw [hvz,hden]
    dsimp [M]
    field_simp [hr.ne',hσ.ne']
    <;> ring
  let E := coordBasis
  let dr := fun i => coordPartial (ksRadius a) i y
  let dv := fun i => (E i 3-v*dr i)/r
  let az := fun i => (y 1*E i 2-y 2*E i 1)/Q
  let b := fun (j i : Fin 4) => (fderiv ℝ coord y (E i)) j
  have hZ (i) : E i 3=v*dr i+r*dv i := by dsimp [dv]; field_simp [hr.ne']; ring
  have hK (i) : y 1*E i 2-y 2*E i 1=Q*az i := by dsimp [az]; field_simp [hQpos.ne']
  have hL (i) : y 1*E i 1+y 2*E i 2=r*B*dr i-S*v*dv i := by
    have hd := fderiv_eq_of_line (ksRadius_differentiableAt a y hr)
      (hasDerivAt_ksRadius_line a y (E i) hr)
    change dr i=r*(r^2*(y 1*E i 1+y 2*E i 2)+S*y 3*E i 3)/(r^4+a^2*y 3^2) at hd
    rw [hvz,hden] at hd
    have hnum : dr i*σ=r*(y 1*E i 1+y 2*E i 2)+S*v*E i 3 := by
      rw [hd]
      field_simp [hr.ne',hσ.ne'] <;> ring
    apply mul_left_cancel₀ hr.ne'
    calc
      r*(y 1*E i 1+y 2*E i 2)=dr i*σ-S*v*E i 3 := by linear_combination -hnum
      _ = _ := by rw [hZ i,hσpol]; ring
  have hn (i) : ksNull a y i=E i 0+σ/S*dr i-a*B*az i := by
    rw [null_coefficient]
    change E i 0+(r*(_)-a*(_))/S+v*E i 3=_
    rw [hL i,hK i,hQ,hZ i,hσpol]
    field_simp [hS.ne']
    ring
  have hflat (i j) :
      E i 1*E j 1+E i 2*E j 2+E i 3*E j 3 =
      σ/S*dr i*dr j + σ/B*dv i*dv j + S*B*az i*az j :=
    plane_metric r a v hr hB _ _ _ _ _ _ _ _ _ _ _ _ _ _ hQ
      (hL i) (hL j) (hK i) (hK j) (hZ i) (hZ j)
  have ho (i) : ρ*b 2 i=x*B*dr i-A*v*dv i ∧ b 3 i=v*dr i+x*dv i :=
    orbit_differentials m a V coord hc y hy i hr hA hB
  have horb (i j) : b 2 i*b 2 j+b 3 i*b 3 j=D/A*dr i*dr j+D/B*dv i*dv j := by
    have h := orbit_metric x k v ρ (dr i) (dr j) (dv i) (dv j)
      (b 2 i) (b 2 j) (b 3 i) (b 3 j) (hArod ▸ hA) hB hρ (hArod ▸ hρ2)
      (hArod ▸ (ho i).1) (hArod ▸ (ho j).1) (ho i).2 (ho j).2
    simpa only [← hArod] using h
  have htime (i) : b 0 i=E i 0-M/A*dr i ∧ b 1 i=az i-(M*a/(A*S))*dr i :=
    hc.killing_coords y hy i
  have hconf : (B*P/D)/(B*P/σ)=σ/D := by
    field_simp [hB.ne', hP.ne', hσ.ne', hD.ne']
  ext i j
  have ht := time_azimuth_metric S M a B (E i 0) (E j 0) (dr i) (dr j) (az i) (az j)
    hS.ne' (by rw [hAid]; exact hA.ne') hB.ne' (by rw [hσid]; exact hσ.ne')
    (by rw [hσid,hPid]; exact hP.ne')
  dsimp only at ht
  rw [hσid,hAid,hPid] at ht
  have hscale : σ/D*(D/A*dr i*dr j+D/B*dv i*dv j) =
      σ/A*dr i*dr j+σ/B*dv i*dv j := by
    field_simp [hD.ne',hA.ne',hB.ne'] <;> ring
  change minkowski i j+ksProfile m a 0 y*ksNull a y i*ksNull a y j =
    -(ρ^2/(kerrErnst m a).normSq p)*b 0 i*b 0 j+
    (kerrErnst m a).normSq p*
      (b 1 i+angularShift (kerrErnst m a) p*b 0 i)*
      (b 1 j+angularShift (kerrErnst m a) p*b 0 j)+
    Real.exp (2*conformalExponent (kerrErnst m a) p)/(kerrErnst m a).normSq p*
      (b 2 i*b 2 j+b 3 i*b 3 j)
  rw [flat_coefficient,hflat,hprof,hn i,hn j,hw',hh',hnorm,hconf,horb,hscale,hρ2,
    (htime i).1,(htime i).2,(htime j).1,(htime j).2]
  linear_combination ht
