-- Prove2me | solution 1 for NoHair.kerr_inner_horizon_normal_identity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:19:25.126992+00:00
-- url     : https://prove2.me/submissions/dede3206-4c0e-4540-94aa-f7537e1eebef

import Definitions.Def_NoHair_kerrNewmanTimeDirection
import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms

open NoHair NoHair.KNE Set Filter
open scoped Topology
open scoped BigOperators Manifold ContDiff

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private abbrev T (m a e : ℝ) := kerrNewmanTimeDirection m a e
private abbrev I4 := 𝓘(ℝ,E4)
private abbrev V3 := Fin 3 → ℝ
private def dot3 (v w : V3) := ∑ i, v i*w i
private def space (v : E4) : V3 := ![v 1,v 2,v 3]
private def axis (a : ℝ) (y : E4) : V3 := ![ksNull a y 1,ksNull a y 2,ksNull a y 3]
private def timeC (v : E4) := v 0

private theorem dot_symm (u v : V3) : dot3 u v = dot3 v u := by simp [dot3, mul_comm]
private theorem dot_add_l (u v w : V3) : dot3 (u+v) w = dot3 u w + dot3 v w := by
  simp [dot3, add_mul, Finset.sum_add_distrib]
private theorem dot_add_r (u v w : V3) : dot3 u (v+w) = dot3 u v + dot3 u w := by
  simp [dot3, mul_add, Finset.sum_add_distrib]
private theorem dot_scale_l (c : ℝ) (u v : V3) : dot3 (c • u) v = c*dot3 u v := by
  simp [dot3, Finset.mul_sum, mul_assoc]
private theorem dot_scale_r (c : ℝ) (u v : V3) : dot3 u (c • v) = c*dot3 u v := by
  simp [dot3, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc]
private theorem dot_cauchy (u v : V3) : (dot3 u v)^2 ≤ dot3 u u * dot3 v v := by
  simpa only [dot3, sq] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) u v
private theorem axis_unit (a : ℝ) (x : U a) : dot3 (axis a x.val) (axis a x.val) = 1 := by
  simpa [dot3, axis, Fin.sum_univ_three, sq] using ks_rel a x.val x.property

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(timeC v*timeC w) + dot3 (space v) (space w) +
      ksProfile m a e x.val * (timeC v + dot3 (axis a x.val) (space v)) *
        (timeC w + dot3 (axis a x.val) (space w)) := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, Fin.sum_univ_four, ksNull_zero]
  simp [minkowski, dot3, space, timeC, axis, Fin.sum_univ_three] <;> ring

private def radialNormal (a : ℝ) (y : E4) : V3 :=
  let r := ksRadius a y
  let k := axis a y
  let W := Wf a y
  ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]

private theorem normal_geometry (a : ℝ) (x : U a) :
    dot3 (radialNormal a x.val) (axis a x.val) = 1 ∧
    dot3 (radialNormal a x.val) (radialNormal a x.val) = (ksRadius a x.val^2 + a^2)*Wf a x.val := by
  let r := ksRadius a x.val
  let k := axis a x.val
  let W := Wf a x.val
  have hrel : k 0^2+k 1^2+k 2^2=1 := ks_rel a x.val x.property
  have hW : W*(r^2+a^2*k 2^2)=1 := ks_W a x.val x.property
  let n : V3 := ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]
  change dot3 n k = 1 ∧ dot3 n n = (r^2+a^2)*W
  constructor
  · calc
      dot3 n k = W*(r^2*(k 0^2+k 1^2+k 2^2)+a^2*k 2^2) := by simp [dot3, n, Fin.sum_univ_three]; ring
      _ = 1 := by rw [hrel, mul_one, hW]
  · calc
      dot3 n n = (r^2+a^2)*W*(W*(r^2*(k 0^2+k 1^2+k 2^2)+a^2*k 2^2)) := by
        simp [dot3, n, Fin.sum_univ_three]; ring
      _ = (r^2+a^2)*W := by rw [hrel, mul_one, hW, mul_one]

private theorem radial_derivative (a : ℝ) (x : U a) (v : E4) :
    fderiv ℝ (ksRadius a) x.val v = dot3 (radialNormal a x.val) (space v) := by
  have hv : ∑ i, v i • coordBasis i = v := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_four, coordBasis]
  have cp (i : Fin 4) := (hasCP_R a x.val x.property).eq i
  change ∀ (i : Fin 4), fderiv ℝ (ksRadius a) x.val (coordBasis i) = _ at cp
  calc
    _ = fderiv ℝ (ksRadius a) x.val (∑ i, v i • coordBasis i) := congrArg _ hv.symm
    _ = _ := by
      simp only [Fin.sum_univ_four, map_add, map_smul, smul_eq_mul]
      erw [cp 0, cp 1, cp 2, cp 3]
      simp [dot3, radialNormal, space, axis, dRt, Fin.sum_univ_three] <;> ring

private theorem metric_entries (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0)+v 1*w 1+v 2*w 2+v 3*w 3+
      ksProfile m a e x.val * (v 0 + ksNull a x.val 1*v 1+ksNull a x.val 2*v 2+ksNull a x.val 3*v 3) *
        (w 0 + ksNull a x.val 1*w 1+ksNull a x.val 2*w 2+ksNull a x.val 3*w 3) := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, Fin.sum_univ_four, ksNull_zero]
  simp [minkowski] <;> ring


private def spiral (y : E4) : E4 := WithLp.toLp 2 ![1,-(2/5)*y 2,(2/5)*y 1,0]
private def poly (r c : ℝ) := 64*c^4+36*c^2+(r^3+r^2)*(4-4*c^2)+r*(-16*c^4-4*c^2-5)
private def factor (y : E4) :=
  let r := ksRadius 2 y
  let c := ksNull 2 y 3
  poly r c / (25*(r^2+4*c^2))
private def normFun (y : E4) := matrixBilin (kerrNewmanMetric (5/2) 2 0 y) (spiral y) (spiral y)

private theorem norm_factored (y : E4) (hy : 0 < ksRadius 2 y) :
    normFun y=(ksRadius 2 y-1)*factor y := by
  let r := ksRadius 2 y
  let l := ksNull 2 y
  let c := l 3
  let B := 1-c^2
  let S := r^2+4*c^2
  let x : U 2 := ⟨y,hy⟩
  have hS : 0<S := by have : 0<r := hy; dsimp [S]; positivity
  have h1 : y 1=r*l 1-2*l 2 := ks_x1 2 y hy
  have h2 : y 2=r*l 2+2*l 1 := by linear_combination ks_x2 2 y hy
  have h3 : l 1^2+l 2^2+c^2=1 := ks_rel 2 y hy
  have hQ : y 1^2+y 2^2=(r^2+4)*B := by rw [h1,h2]; dsimp [B]; linear_combination (r^2+4)*h3
  have hK : 1+l 1*(-(2/5)*y 2)+l 2*((2/5)*y 1)+c*0=1-(4/5)*B := by
    rw [h1,h2]; dsimp [B]; linear_combination -(4/5:ℝ)*h3
  have hP : ksProfile (5/2) 2 0 y=5*r/S := by
    rw [profile_eq _ _ _ _ hy]; dsimp only [fA,Wf]
    change ((2*(5/2)*r-0^2)*(1/(r^2+2^2*c^2)))=_
    dsimp [S]; ring
  have hflat : -(1*1:ℝ)+(-(2/5)*y 2)*(-(2/5)*y 2)+((2/5)*y 1)*((2/5)*y 1)+0*0 =
      -1+(4/25)*(r^2+4)*B := by linear_combination (4/25:ℝ)*hQ
  change G (5/2) 2 0 x (spiral y) (spiral y)=_
  rw [metric_entries]
  change -(1*1:ℝ)+(-(2/5)*y 2)*(-(2/5)*y 2)+((2/5)*y 1)*((2/5)*y 1)+0*0+
    ksProfile (5/2) 2 0 y * (1+l 1*(-(2/5)*y 2)+l 2*((2/5)*y 1)+c*0)*
      (1+l 1*(-(2/5)*y 2)+l 2*((2/5)*y 1)+c*0) = (r-1)*(poly r c/(25*S))
  rw [hflat,hP,hK]
  field_simp [hS.ne']
  dsimp only [S,B,poly]
  ring

private theorem on_level (x : U 2) (hr : ksRadius 2 x.val=1) :
    let c := ksNull 2 x.val 3
    factor x.val = 3*(1+4*c^2)/25 ∧
      ∀ v : E4, G (5/2) 2 0 x (spiral x.val) v =
        ((1+4*c^2)/5)*fderiv ℝ (ksRadius 2) x.val v := by
  let l := ksNull 2 x.val
  let c := l 3
  let S := 1+4*c^2
  have hs : 0<S := by dsimp [S]; positivity
  have hP : ksProfile (5/2) 2 0 x.val=5/S := by
    rw [profile_eq _ _ _ _ x.property]; dsimp only [fA,Wf]; rw [hr]
    change ((2*(5/2)*1-0^2)*(1/(1^2+2^2*c^2)))=_
    dsimp [S]; ring
  have h1 := ks_x1 2 x.val x.property
  have h2 := ks_x2 2 x.val x.property
  rw [hr,one_mul] at h1 h2
  change x.val 1=l 1-2*l 2 at h1
  change x.val 2=2*l 1+l 2 at h2
  have h3 : l 1^2+l 2^2+c^2=1 := ks_rel 2 x.val x.property
  have hK : 1+l 1*(-(2/5)*x.val 2)+l 2*((2/5)*x.val 1)+c*0=S/5 := by
    rw [h1,h2]; dsimp [S]; linear_combination -(4/5:ℝ)*h3
  constructor
  · change poly (ksRadius 2 x.val) c/(25*((ksRadius 2 x.val)^2+4*c^2))=_
    rw [hr,one_pow]; change poly 1 c/(25*S)=3*S/25
    field_simp [hs.ne']; dsimp [poly,S]; ring
  · intro v
    rw [metric_entries,radial_derivative]
    have hW : Wf 2 x.val=1/S := by
      unfold Wf; rw [hr]; change 1/(1^2+2^2*c^2)=1/S
      dsimp [S]; ring
    change -(1*v 0)+(-(2/5)*x.val 2)*v 1+((2/5)*x.val 1)*v 2+0*v 3+
      ksProfile (5/2) 2 0 x.val*(1+l 1*(-(2/5)*x.val 2)+l 2*((2/5)*x.val 1)+c*0)*
      (v 0+l 1*v 1+l 2*v 2+c*v 3)=S/5*dot3 (radialNormal 2 x.val) (space v)
    rw [hK,hP,h1,h2]
    simp only [dot3,radialNormal,space,axis,Fin.sum_univ_three,Matrix.cons_val,hr,hW]
    change _=S/5*((1^2*l 1*(1/S)-1*l 2*(1/S)*2)*v 1+
      (1^2*l 2*(1/S)+1*l 1*(1/S)*2)*v 2+((1^2+2^2)*c*(1/S))*v 3)
    field_simp [hs.ne'] <;> ring

private theorem norm_deriv (x : U 2) (hr : ksRadius 2 x.val=1) (v : E4) :
    fderiv ℝ normFun x.val v=(3/5)*G (5/2) 2 0 x (spiral x.val) v := by
  have hR := ksRadius_differentiableAt 2 x.val x.property
  have hC := ksNull_differentiableAt 2 x.val x.property 3
  have hs : 0 < (ksRadius 2 x.val)^2+4*(ksNull 2 x.val 3)^2 := by rw [hr]; positivity
  have hfactor : DifferentiableAt ℝ factor x.val := by
    have hn : 25*((ksRadius 2 x.val)^2+4*(ksNull 2 x.val 3)^2) ≠ 0 := by positivity
    unfold factor poly
    fun_prop (disch := assumption)
  let line := fun t : ℝ => x.val+t • v
  have h0 : line 0=x.val := by simp [line]
  have hline : HasDerivAt line v 0 := by
    simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x.val
  have hfun : normFun =ᶠ[𝓝 x.val] (fun y => (ksRadius 2 y-1)*factor y) := by
    filter_upwards [(continuous_ksRadius 2).continuousAt.eventually (lt_mem_nhds x.property)] with y hy
    exact norm_factored y hy
  have hdiff : DifferentiableAt ℝ normFun x.val :=
    ((hR.sub_const 1).mul hfactor).congr_of_eventuallyEq hfun
  have lineD (f : E4 → ℝ) (hd : DifferentiableAt ℝ f x.val) :
      HasDerivAt (fun t => f (line t)) (fderiv ℝ f x.val v) 0 := by
    have hh : HasFDerivAt f (fderiv ℝ f x.val) (line 0) := by rw [h0]; exact hd.hasFDerivAt
    exact hh.comp_hasDerivAt 0 hline
  have heq : (fun t => normFun (line t)) =ᶠ[𝓝 0] (fun t => (ksRadius 2 (line t)-1)*factor (line t)) :=
    hfun.comp_tendsto (by simpa only [h0] using hline.continuousAt.tendsto)
  have h := (lineD normFun hdiff).unique (((((lineD _ hR).sub_const 1).mul (lineD _ hfactor))).congr_of_eventuallyEq heq)
  rw [h0,hr] at h
  obtain ⟨hfac,hflat⟩ := on_level x hr
  rw [h,hfac,hflat]
  ring

theorem solution :
    let X : VecField (kerrNewmanSpacetime 2) := fun x => WithLp.toLp 2 ![1,-(2/5)*x.val 2,(2/5)*x.val 1,0]
    let g := kerrNewmanMetricField (5/2) 2 0
    ∀ x : kerrNewmanSpacetime 2, ksRadius 2 x.val=1 → g x (X x) (X x)=0 ∧
      ∀ e ∈ atlas E4 (kerrNewmanSpacetime 2), ∀ y ∈ e.target, e.symm y=x → ∀ i : Fin 4,
        coordPartial (fun z => g (e.symm z) (X (e.symm z)) (X (e.symm z))) i y =
          (3/5)*loweredCoeffs g X e.symm y i := by
  dsimp only
  intro x hx
  constructor
  · change normFun x.val=0
    rw [norm_factored _ x.property,hx]; ring
  · intro e he y hy hyx i
    obtain ⟨p,hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨e.symm y⟩ he
    have hchart (w : U 2) : e=chartAt E4 w := hp.trans (by rfl)
    have hval (z : E4) (hz : z ∈ e.target) : (e.symm z).val=z := by
      have h (w : U 2) : e w=w.val := by rw [hchart w]; rfl
      exact (h (e.symm z)).symm.trans (e.right_inv hz)
    have hxy : x.val=y := by simpa only [hyx] using hval y hy
    have hd : (mfderiv I4 I4 e.symm y : E4 →L[ℝ] E4)=ContinuousLinearMap.id ℝ E4 := by
      rw [← hxy,hchart x]
      have hh := mfderivWithin_range_extChartAt_symm (I := I4) (x := x)
      simp only [modelWithCornersSelf_coe,range_id,mfderivWithin_univ] at hh
      exact hh
    have heq : (fun z => normFun (e.symm z).val) =ᶠ[𝓝 y] normFun := by
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      rw [hval z hz]
    change fderiv ℝ (fun z => normFun (e.symm z).val) y (coordBasis i) =
      (3/5)*G (5/2) 2 0 (e.symm y) (spiral (e.symm y).val) (mfderiv I4 I4 e.symm y (coordBasis i))
    rw [heq.fderiv_eq,hd,hyx,← hxy]
    exact norm_deriv x hx (coordBasis i)
