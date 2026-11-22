-- Prove2me | solution 1 for NoHair.Weyl.kerr_metric_in_weyl_chart
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:38:35.475256+00:00
-- url     : https://prove2.me/submissions/0b74295d-ac94-4c8d-ab56-61a86d7b8a0f

import Theorems.Thm_NoHair_Weyl_kerr_oblate_exterior_differential
import Definitions.Def_NoHair_kerrWeylCoefficients

noncomputable section

open NoHair NoHair.Weyl Set Filter Topology
open scoped ContDiff

private def cartBlock (m a r c t l b f t' l' b' f' : ℝ) :=
  let B := r^2+a^2
  let S := 1-c^2
  let Q := r^2+a^2*c^2
  (-(t*t'))+Q/B*l*l'+Q/S*b*b'+B*S*f*f'+
    (2*m*r/Q)*(t+Q/B*l-a*S*f)*(t'+Q/B*l'-a*S*f')

private theorem cart_spatial (r a c l b f l' b' f' : ℝ)
    (hr : 0 < r) (hs : 0 < 1-c^2) :
    let B:=r^2+a^2
    let S:=1-c^2
    let Q:=r^2+a^2*c^2
    ((r*S*l-B*c*b)*(r*S*l'-B*c*b')+(B*S*f)*(B*S*f'))/(B*S)+
      (c*l+r*b)*(c*l'+r*b') =
    Q/B*l*l'+Q/S*b*b'+B*S*f*f' := by
  dsimp only
  field_simp (disch := first | positivity | grind)
  ring

private theorem cart_null (r a c t l b f : ℝ) (hr : 0 < r) :
    let B:=r^2+a^2
    let S:=1-c^2
    let Q:=r^2+a^2*c^2
    t+(r*(r*S*l-B*c*b)-a*(B*S*f))/B+c*(c*l+r*b)=t+Q/B*l-a*S*f := by
  dsimp only
  field_simp (disch := positivity)
  ring

private theorem orbit_block (m a r c ρ l b l' b' : ℝ)
    (hr : 0 < ρ) (hΔ : 0 < kerrDelta m a r) (hS : 0 < 1-c^2)
    (hD : 0 < (r-m)^2-(m^2-a^2)*c^2) (hρ : ρ^2=kerrDelta m a r*(1-c^2)) :
    let Δ:=kerrDelta m a r
    let S:=1-c^2
    let Q:=r^2+a^2*c^2
    let D:=(r-m)^2-(m^2-a^2)*c^2
    Q/D*((((r-m)*S*l-Δ*c*b)/ρ)*(((r-m)*S*l'-Δ*c*b')/ρ)+
      (c*l+(r-m)*b)*(c*l'+(r-m)*b')) = Q/Δ*l*l'+Q/S*b*b' := by
  have divs (x y : ℝ) : (x/ρ)*(y/ρ) = x*y/(kerrDelta m a r*(1-c^2)) := by
    rw [←hρ,pow_two,div_mul_div_comm]
  dsimp only
  rw [divs]
  unfold kerrDelta at *
  field_simp (disch := first | positivity | grind)
  ring

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8000 in
private theorem bl_block (m a r c t l b f t' l' b' f' : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hΔ : 0 < kerrDelta m a r) (hS : 0 < 1-c^2) :
    let B:=r^2+a^2
    let S:=1-c^2
    let Q:=r^2+a^2*c^2
    let Δ:=kerrDelta m a r
    let N:=kerrAxialNumerator m a r c
    let X:=S*N/Q
    let W:= -(2*m*a*r)/N
    let T:= t-2*m*r/Δ*l
    let T':= t'-2*m*r/Δ*l'
    let F:= f-2*m*r*a/(Δ*B)*l
    let F':= f'-2*m*r*a/(Δ*B)*l'
    cartBlock m a r c t l b f t' l' b' f' =
      -(Δ*S/X)*T*T'+X*(F+W*T)*(F'+W*T')+(Q/Δ*l*l'+Q/S*b*b') := by
  let B:=r^2+a^2
  let S:=1-c^2
  let Q:=r^2+a^2*c^2
  let Δ:=kerrDelta m a r
  let N:=kerrAxialNumerator m a r c
  let X:=S*N/Q
  let W:= -(2*m*a*r)/N
  let K:=2*m*r/Q
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hN : 0 < N := by unfold N kerrAxialNumerator; positivity
  have xw : X*W = -K*a*S := by
    dsimp [X,W,K]
    field_simp [hQ.ne',hN.ne'] <;> ring
  have xx : X = B*S+K*a^2*S^2 := by
    dsimp [X,N,kerrAxialNumerator,B,K,Q,S]
    field_simp (disch := positivity) <;> ring
  have tt : -(Δ*S/X)+X*W^2 = -1+K := by
    dsimp [X,W,K]
    field_simp (disch := first | positivity | grind)
    dsimp [N,kerrAxialNumerator,Q,Δ,kerrDelta,S]
    ring
  have kill (T P U V : ℝ) :
      -(Δ*S/X)*T*U+X*(P+W*T)*(V+W*U)=(-1+K)*T*U+(-K*a*S)*(T*V+P*U)+X*P*V := by
    rw [←tt,←xw]
    ring
  dsimp only
  rw [kill,xx]
  clear kill tt xw xx
  unfold kerrDelta at hΔ
  dsimp [cartBlock,K,Δ,kerrDelta,B,Q,S]
  field_simp (disch := first | positivity | grind)
  ring

private theorem basis_flat (i j : Fin 4) :
    minkowski i j = -((coordBasis i) 0*(coordBasis j) 0)+
      ((coordBasis i) 1*(coordBasis j) 1+(coordBasis i) 2*(coordBasis j) 2)+
      (coordBasis i) 3*(coordBasis j) 3 := by
  fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [minkowski,coordBasis,PiLp.single_apply,Matrix.diagonal]

private theorem basis_null (a : ℝ) (y : E4) (i : Fin 4) :
    let r:=ksRadius a y
    let v:=coordBasis i
    ksNull a y i = v 0+(r*(y 1*v 1+y 2*v 2)-a*(y 1*v 2-y 2*v 1))/(r^2+a^2)+(y 3/r)*v 3 := by
  fin_cases i <;> simp (config := {decide := true}) [ksNull,coordBasis,PiLp.single_apply] <;> ring

private theorem recover_orbit (m a r c ρ : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0)
    (hr : m+Real.sqrt (m^2-a^2) < r) (hc : 0 < 1-c^2) (hρ : 0 < ρ)
    (hρsq : ρ^2=kerrDelta m a r*(1-c^2)) :
    kerrOrbitCoords m a (Real.log ρ,(r-m)*c)=(r,c) := by
  let k:=Real.sqrt (m^2-a^2)
  let u:=r-m
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hk2 : k^2=m^2-a^2 := Real.sq_sqrt (by nlinarith [hm.2])
  have hu : k < u := by dsimp [u,k]; linarith
  have hu0 := hk.trans_lt hu
  have hh : -1 < c ∧ c < 1 := by constructor <;> nlinarith [sq_nonneg (c+1),sq_nonneg (c-1)]
  have hminus : 0 ≤ u-k*c := by nlinarith [mul_nonneg hk (sub_nonneg.mpr hh.2.le)]
  have hplus : 0 ≤ u+k*c := by nlinarith [mul_nonneg hk (show 0 ≤ 1+c by linarith [hh.1])]
  have hA : kerrDelta m a r=u^2-k^2 := by dsimp [kerrDelta,u]; rw [hk2]; ring
  have he : Real.exp (2*Real.log ρ)=ρ^2 := by rw [two_mul,Real.exp_add,Real.exp_log hρ,sq]
  have hU : prolateRadius k (Real.log ρ,u*c)=u := by
    unfold prolateRadius
    dsimp only
    rw [he,hρsq,hA,show (u^2-k^2)*(1-c^2)+(u*c-k)^2=(u-k*c)^2 by ring,
      show (u^2-k^2)*(1-c^2)+(u*c+k)^2=(u+k*c)^2 by ring,
      Real.sqrt_sq hminus,Real.sqrt_sq hplus]
    ring
  change (m+prolateRadius k (Real.log ρ,u*c),u*c/prolateRadius k (Real.log ρ,u*c))=(r,c)
  rw [hU]
  apply Prod.ext
  · dsimp [u]; ring
  · dsimp only; field_simp

private def radialDiff (a : ℝ) (y v : E4) := fderiv ℝ (ksRadius a) y v
private def cosineDiff (a : ℝ) (y v : E4) :=
  (v 3-(y 3/ksRadius a y)*radialDiff a y v)/ksRadius a y

private theorem line_derivs (a : ℝ) (y v : E4) (hr : 0 < ksRadius a y)
    (hs : ContDiffAt ℝ ∞ (ksRadius a) y) :
    let γ := fun t : ℝ => y+t • v
    HasDerivAt γ v 0 ∧ HasDerivAt (fun t => ksRadius a (γ t)) (radialDiff a y v) 0 ∧
      HasDerivAt (fun t => (γ t) 3/ksRadius a (γ t)) (cosineDiff a y v) 0 := by
  let γ := fun t : ℝ => y+t • v
  have hγ : HasDerivAt γ v 0 := by simpa [γ] using ((hasDerivAt_id' (0:ℝ)).smul_const v).const_add y
  have h0 : γ 0=y := by simp [γ]
  have hF : HasFDerivAt (ksRadius a) (fderiv ℝ (ksRadius a) y) (γ 0) := by
    rw [h0]; exact (hs.differentiableAt (by norm_num)).hasFDerivAt
  have hR : HasDerivAt (fun t => ksRadius a (γ t)) (radialDiff a y v) 0 := hF.comp_hasDerivAt 0 hγ
  have coord : HasDerivAt (fun t => (γ t) 3) (v 3) 0 :=
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 4 => ℝ) 3).hasFDerivAt.comp_hasDerivAt 0 hγ
  refine ⟨hγ,hR,?_⟩
  apply (coord.fun_div hR (h0 ▸ hr.ne')).congr_deriv
  dsimp only
  rw [h0]
  unfold cosineDiff
  field_simp [hr.ne'] <;> ring

private theorem chart_orbit_tangents (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0)
    (V : Set E4) (C : E4 → E4) (hc : IsKerrWeylChart m a V C) (y : E4) (hy : y∈V) (v : E4) :
    let r:=ksRadius a y
    let c:=y 3/r
    let l:=radialDiff a y v
    let b:=cosineDiff a y v
    let u:=r-m
    let J:=fderiv ℝ C y v
    J 2=(u*(1-c^2)*l-kerrDelta m a r*c*b)/(C y) 2 ∧ J 3=c*l+u*b := by
  obtain ⟨hr,hS,hΔ,_,hs,_⟩ := kerr_oblate_exterior_differential m a hm y (hc.off_axis hy)
  let γ := fun t : ℝ => y+t • v
  let R := fun t => ksRadius a (γ t)
  let P := fun t => (γ t) 3/R t
  let l:=radialDiff a y v
  let b:=cosineDiff a y v
  have h0 : γ 0=y := by simp [γ]
  obtain ⟨hγ,hR,hP⟩ := line_derivs a y v hr hs
  change HasDerivAt γ v 0 at hγ
  change HasDerivAt R l 0 at hR
  change HasDerivAt P b 0 at hP
  obtain ⟨_,_,_,_,_,hchart,_⟩ := hc.diffeo
  have hCF : HasFDerivAt C (fderiv ℝ C y) (γ 0) := by
    rw [h0]
    exact ((hchart.contDiffOn.contDiffAt (hc.source_open.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
  have hC (i : Fin 4) : HasDerivAt (fun t => (C (γ t)) i) ((fderiv ℝ C y v) i) 0 :=
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 4 => ℝ) i).hasFDerivAt.comp_hasDerivAt 0 (hCF.comp_hasDerivAt 0 hγ)
  have hv : ∀ᶠ t in 𝓝 (0:ℝ), γ t ∈ V :=
    hγ.continuousAt (h0 ▸ hc.source_open.mem_nhds hy)
  have eq₁ : (fun t => kerrDelta m a (R t)*(1-(P t)^2)) =ᶠ[𝓝 0] fun t => ((C (γ t)) 2)^2 := by
    filter_upwards [hv] with t ht
    obtain ⟨_,hS',hΔ',_⟩ := kerr_oblate_exterior_differential m a hm (γ t) (hc.off_axis ht)
    rw [(hc.orbit _ ht).1,mul_pow,Real.sq_sqrt hΔ'.le,Real.sq_sqrt hS'.le]
  have eq₂ : (fun t => (R t-m)*P t) =ᶠ[𝓝 0] fun t => (C (γ t)) 3 :=
    hv.mono fun t ht => (hc.orbit _ ht).2.symm
  have hd := (((hR.fun_pow 2).fun_sub (hR.const_mul (2*m))).add_const (a^2)).fun_mul
    ((hP.fun_pow 2).const_sub 1)
  have h := (((hC 2).fun_pow 2).congr_of_eventuallyEq eq₁).unique hd
  have h' := ((hC 3).congr_of_eventuallyEq eq₂).unique ((hR.sub_const m).fun_mul hP)
  simp only [R,P,h0,show (2:ℕ)-1=1 by decide,Nat.cast_ofNat,pow_one] at h h'
  constructor
  · apply (eq_div_iff (hc.pos y hy).ne').2
    unfold kerrDelta
    linarith only [h]
  · linarith only [h']

set_option maxHeartbeats 1200000 in
theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0)
    (V : Set E4) (C : E4 → E4) (hc : IsKerrWeylChart m a V C) :
    ∀ y ∈ V, kerrNewmanMetric m a 0 y = kerrWeylMatrix m a C y := by
  intro y hy
  let r:=ksRadius a y
  let c:=y 3/r
  let u:=r-m
  let B:=r^2+a^2
  let S:=1-c^2
  let Q:=r^2+a^2*c^2
  let Δ:=kerrDelta m a r
  let D:=u^2-(m^2-a^2)*c^2
  let N:=kerrAxialNumerator m a r c
  let X:=S*N/Q
  let W:= -(2*m*a*r)/N
  let ρ:=(C y) 2
  let p:OrbitPoint:=(Real.log ρ,(C y) 3)
  let e:=coordBasis
  let l:=fun i => radialDiff a y (e i)
  let b:=fun i => cosineDiff a y (e i)
  let A:=fun i => y 1*(e i) 1+y 2*(e i) 2
  let P:=fun i => y 1*(e i) 2-y 2*(e i) 1
  let f:=fun i => P i/(y 1^2+y 2^2)
  let J:=fun (i j : Fin 4) => (fderiv ℝ C y (e j)) i
  have hoff:=hc.off_axis hy
  obtain ⟨hr,hs,hΔ,hxy,_,diff⟩ := kerr_oblate_exterior_differential m a hm y hoff
  change 0 < r at hr
  change 0 < S at hs
  change 0 < Δ at hΔ
  change y 1^2+y 2^2=B*S at hxy
  obtain ⟨hor,hz⟩ := hc.orbit y hy
  change (C y) 3=u*c at hz
  have hlarge : m+Real.sqrt (m^2-a^2) < r := by
    simpa [kerrNewmanDOC,kerrNewmanOuterRadius,r] using hoff.1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hN : 0 < N := by
    have hp:=hm.1
    change 0< B*Q+2*m*r*a^2*S
    positivity
  have hD : 0 < D := by
    have hn : 0 ≤ m^2-a^2 := by nlinarith [hm.2]
    have iden : D=Δ+(m^2-a^2)*S := by dsimp [D,Δ,kerrDelta,u,S]; ring
    rw [iden]; exact add_pos_of_pos_of_nonneg hΔ (mul_nonneg hn hs.le)
  have hρ:=hc.pos y hy
  have hρsq : ρ^2=Δ*S := by
    change ((C y) 2)^2 = Δ*S
    rw [hor,mul_pow,Real.sq_sqrt hΔ.le,Real.sq_sqrt hs.le]
  have hpair : kerrOrbitCoords m a p=(r,c) := by
    change kerrOrbitCoords m a (Real.log ρ,(C y) 3)=(r,c)
    rw [hz]
    exact recover_orbit m a r c ρ hm hlarge hs hρ hρsq
  have xval : (kerrErnst m a).normSq p=X := by
    change kerrAxialNorm m a (kerrOrbitCoords m a p).1 (kerrOrbitCoords m a p).2 = X
    rw [hpair]
    change S*(B+2*m*r*a^2*S/Q) = S*(B*Q+2*m*r*a^2*S)/Q
    field_simp [hQ.ne'] <;> ring
  have wval : kerrWeylShift m a p=W := by unfold kerrWeylShift; rw [hpair]
  have sval : kerrWeylScale m a p=S*N/D := by unfold kerrWeylScale; rw [hpair]
  have scl : kerrWeylScale m a p / (kerrErnst m a).normSq p=Q/D := by
    rw [sval,xval]
    dsimp [X]
    field_simp [hs.ne',hN.ne',hD.ne',hQ.ne']
  have zval : y 3 = r*c := by dsimp [c]; field_simp
  have profile : ksProfile m a 0 y=2*m*r/Q := by
    change r^2*(2*m*r-0^2)/(r^4+a^2*y 3^2)=2*m*r/(r^2+a^2*c^2)
    rw [zval,show r^4+a^2*(r*c)^2=r^2*Q by dsimp [Q]; ring]
    change _=2*m*r/Q
    field_simp [hr.ne',hQ.ne'] <;> ring
  have polar (i : Fin 4) : (e i) 3=c*l i+r*b i := by
    change (e i) 3=c*l i+r*(((e i) 3-c*l i)/r)
    field_simp [hr.ne'] <;> ring
  have radial (i : Fin 4) : A i=r*S*l i-B*c*b i := by
    have h:=diff (e i)
    change (r^2+a^2*c^2)*l i=r*A i+(r^2+a^2)*c*(e i) 3 at h
    rw [polar] at h
    apply mul_left_cancel₀ hr.ne'
    dsimp only [B,S]
    linarith only [h]
  have planar (i : Fin 4) : P i=(B*S)*f i := by
    change P i=(B*S)*(P i/(y 1^2+y 2^2))
    rw [hxy]
    field_simp [hs.ne',hB.ne']
  have angular (i : Fin 4) : ksNull a y i=(e i) 0+Q/B*l i-a*S*f i := by
    calc
      _ = (e i) 0+(r*A i-a*P i)/B+c*(e i) 3 := basis_null a y i
      _ = _ := by rw [radial,planar,polar]; exact cart_null r a c _ _ _ _ hr
  have flat (i j : Fin 4) :
      minkowski i j = -((e i) 0*(e j) 0)+
        (Q/B*l i*l j+Q/S*b i*b j+B*S*f i*f j) := by
    have dot : (e i) 1*(e j) 1+(e i) 2*(e j) 2=(A i*A j+P i*P j)/(B*S) := by
      apply (eq_div_iff (mul_pos hB hs).ne').2
      rw [←hxy]; dsimp [A,P]; ring
    rw [basis_flat]
    change -((e i) 0*(e j) 0)+((e i) 1*(e j) 1+(e i) 2*(e j) 2)+(e i) 3*(e j) 3 = _
    rw [dot,radial i,radial j,planar i,planar j,polar i,polar j,add_assoc]
    exact congrArg (fun t => -((e i) 0*(e j) 0)+t) (cart_spatial r a c _ _ _ _ _ _ hr hs)
  have time (i : Fin 4) : J 0 i=(e i) 0-2*m*r/Δ*l i := (hc.killing_coords y hy i).1
  have phi (i : Fin 4) : J 1 i=f i-2*m*r*a/(Δ*B)*l i := (hc.killing_coords y hy i).2
  have orb (i : Fin 4) : J 2 i=(u*S*l i-Δ*c*b i)/ρ ∧ J 3 i=c*l i+u*b i :=
    chart_orbit_tangents m a hm V C hc y hy (e i)
  ext i j
  have ob : Q/D*(J 2 i*J 2 j+J 3 i*J 3 j)=Q/Δ*l i*l j+Q/S*b i*b j := by
    rw [(orb i).1,(orb j).1,(orb i).2,(orb j).2]
    exact orbit_block m a r c ρ _ _ _ _ hρ hΔ hs hD hρsq
  calc
    kerrNewmanMetric m a 0 y i j = cartBlock m a r c ((e i) 0) (l i) (b i) (f i)
        ((e j) 0) (l j) (b j) (f j) := by
      change minkowski i j + ksProfile m a 0 y*ksNull a y i*ksNull a y j=_
      rw [flat,profile,angular i,angular j]
      change _= -((e i) 0*(e j) 0)+Q/B*l i*l j+Q/S*b i*b j+B*S*f i*f j+
        2*m*r/Q*((e i) 0+Q/B*l i-a*S*f i)*((e j) 0+Q/B*l j-a*S*f j)
      ring
    _ = kerrWeylMatrix m a C y i j := by
      change _= -(ρ^2/(kerrErnst m a).normSq p)*J 0 i*J 0 j+
        (kerrErnst m a).normSq p*(J 1 i+kerrWeylShift m a p*J 0 i)*(J 1 j+kerrWeylShift m a p*J 0 j)+
        kerrWeylScale m a p/(kerrErnst m a).normSq p*(J 2 i*J 2 j+J 3 i*J 3 j)
      rw [scl,ob,hρsq,wval,xval,time i,time j,phi i,phi j]
      exact bl_block m a r c _ _ _ _ _ _ _ _ hm.1 hr hΔ hs

