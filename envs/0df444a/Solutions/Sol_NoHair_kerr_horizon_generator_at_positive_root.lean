-- Prove2me | solution 1 for NoHair.kerr_horizon_generator_at_positive_root
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:12:04.653836+00:00
-- url     : https://prove2.me/submissions/310002c8-8f29-4140-8faa-d5ede1562fc5

import Theorems.Thm_NoHair_kerr_vacuum_helical_symmetry
import Definitions.Def_NoHair_kerrNewmanTimeDirection
import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms

open NoHair NoHair.KNE Set Filter
open scoped Topology
open scoped BigOperators Manifold ContDiff

noncomputable section

set_option maxHeartbeats 600000

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private abbrev T (m a e : ℝ) := kerrNewmanTimeDirection m a e
private abbrev I4 := 𝓘(ℝ,E4)
private abbrev V3 := Fin 3 → ℝ
private def dot3 (v w : V3) := ∑ i, v i*w i
private def space (v : E4) : V3 := ![v 1,v 2,v 3]
private def axis (a : ℝ) (y : E4) : V3 := ![ksNull a y 1,ksNull a y 2,ksNull a y 3]
private def radialNormal (a : ℝ) (y : E4) : V3 :=
  let r := ksRadius a y
  let k := axis a y
  let W := Wf a y
  ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]

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


private def twistVec (speed : ℝ) (y : E4) : E4 := WithLp.toLp 2 ![1,-speed*y 2,speed*y 1,0]
private def normK (m a R : ℝ) (y : E4) :=
  let X := twistVec (a/(R^2+a^2)) y
  matrixBilin (kerrNewmanMetric m a 0 y) X X

private def factorAt (m a R r c : ℝ) :=
  (a^2*(r+R)*(1-c^2) + ((R^2+a^2*c^2)/(r^2+a^2*c^2)) *
    (2*m*(R^2+a^2*c^2)-(R^2+a^2)*(r+R))) / (R^2+a^2)^2
private def factorK (m a R : ℝ) (y : E4) := factorAt m a R (ksRadius a y) (ksNull a y 3)

private theorem norm_factored (m a R : ℝ) (hR : 0<R) (hroot : R^2-2*m*R+a^2=0)
    (y : E4) (hy : 0<ksRadius a y) : normK m a R y = (ksRadius a y-R)*factorK m a R y := by
  let r := ksRadius a y
  let l := ksNull a y
  let c := l 3
  let speed := a/(R^2+a^2)
  let x : U a := ⟨y,hy⟩
  have hr : 0<r := hy
  have den : 0 < r^2+a^2*c^2 := by positivity
  have da : 0 < R^2+a^2 := by positivity
  have h1 : y 1=r*l 1-a*l 2 := ks_x1 a y hy
  have h2 : y 2=a*l 1+r*l 2 := ks_x2 a y hy
  have h3 : l 1^2+l 2^2+c^2=1 := ks_rel a y hy
  have hQ : y 1^2+y 2^2=(r^2+a^2)*(1-c^2) := by rw [h1,h2]; linear_combination (r^2+a^2)*h3
  have hK : 1+l 1*(-speed*y 2)+l 2*(speed*y 1)+c*0=1-speed*a*(1-c^2) := by
    rw [h1,h2]; linear_combination -(speed*a)*h3
  have hP : ksProfile m a 0 y=(2*m*r)/(r^2+a^2*c^2) := by
    rw [profile_eq _ _ _ _ hy]; dsimp only [fA,Wf]
    change (2*m*r-0^2)*(1/(r^2+a^2*c^2))=_
    ring
  have hflat : -(1*1:ℝ)+(-speed*y 2)*(-speed*y 2)+(speed*y 1)*(speed*y 1)+0*0 =
      -1+speed^2*(r^2+a^2)*(1-c^2) := by linear_combination speed^2*hQ
  change G m a 0 x (twistVec speed y) (twistVec speed y)=_
  rw [metric_entries]
  change -(1*1:ℝ)+(-speed*y 2)*(-speed*y 2)+(speed*y 1)*(speed*y 1)+0*0+
    ksProfile m a 0 y*(1+l 1*(-speed*y 2)+l 2*(speed*y 1)+c*0)*
      (1+l 1*(-speed*y 2)+l 2*(speed*y 1)+c*0)=(r-R)*factorAt m a R r c
  rw [hflat,hP,hK]
  have hm : m=(R^2+a^2)/(2*R) := (eq_div_iff (by positivity)).2 (by nlinarith only [hroot])
  rw [hm]; dsimp only [speed,factorAt]
  field_simp [da.ne',den.ne',hR.ne'] <;> ring

private theorem on_horizon (m a R : ℝ) (hR : 0<R) (hroot : R^2-2*m*R+a^2=0)
    (x : U a) (hr : ksRadius a x.val=R) :
    let c := ksNull a x.val 3
    let A := R^2+a^2
    let S := R^2+a^2*c^2
    factorK m a R x.val = (-2*((R-m)/A))*(S/A) ∧
      ∀ v : E4, G m a 0 x (twistVec (a/A) x.val) v = (S/A)*fderiv ℝ (ksRadius a) x.val v := by
  let l := ksNull a x.val
  let c := l 3
  let A := R^2+a^2
  let S := R^2+a^2*c^2
  let speed := a/A
  have ha : 0 < A := by dsimp [A]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  change factorK m a R x.val = (-2*((R-m)/A))*(S/A) ∧ _
  have hP : ksProfile m a 0 x.val=A/S := by
    rw [profile_eq _ _ _ _ x.property];dsimp only [fA,Wf];rw [hr]
    change (2*m*R-0^2)*(1/S)=A/S
    have he : 2*m*R=A := by dsimp [A]; linarith only [hroot]
    rw [he];ring
  have h1 : x.val 1=R*l 1-a*l 2 := by simpa [l,hr] using ks_x1 a x.val x.property
  have h2 : x.val 2=a*l 1+R*l 2 := by simpa [l,hr] using ks_x2 a x.val x.property
  have h3 : l 1^2+l 2^2+c^2=1 := ks_rel a x.val x.property
  have hK : 1+l 1*(-speed*x.val 2)+l 2*(speed*x.val 1)+c*0=S/A := by
    rw [h1,h2]; dsimp only [speed]; field_simp [ha.ne']; dsimp only [S,A]; linear_combination -a^2*h3
  constructor
  · change factorAt m a R (ksRadius a x.val) c = _
    rw [hr]
    change (a^2*(R+R)*(1-c^2)+(S/S)*(2*m*S-A*(R+R)))/A^2 = _
    rw [div_self hS.ne'];field_simp [ha.ne']; dsimp only [S,A]; ring
  · intro v
    change G m a 0 x (twistVec speed x.val) v=(S/A)*fderiv ℝ (ksRadius a) x.val v
    rw [metric_entries,radial_derivative]
    have hW : Wf a x.val=1/S := by unfold Wf; rw [hr]
    change -(1*v 0)+(-speed*x.val 2)*v 1+(speed*x.val 1)*v 2+0*v 3+
      ksProfile m a 0 x.val*(1+l 1*(-speed*x.val 2)+l 2*(speed*x.val 1)+c*0)*
      (v 0+l 1*v 1+l 2*v 2+c*v 3)=S/A*dot3 (radialNormal a x.val) (space v)
    rw [hK,hP,h1,h2]
    simp only [dot3,radialNormal,space,axis,Fin.sum_univ_three,Matrix.cons_val,hr,hW]
    change _=S/A*((R^2*l 1*(1/S)-R*l 2*(1/S)*a)*v 1+
      (R^2*l 2*(1/S)+R*l 1*(1/S)*a)*v 2+((R^2+a^2)*c*(1/S))*v 3)
    dsimp only [speed];field_simp [hS.ne',ha.ne'];dsimp only [A];ring

private theorem horizon_derivative (m a R : ℝ) (hR : 0<R) (hroot : R^2-2*m*R+a^2=0)
    (x : U a) (hr : ksRadius a x.val=R) (v : E4) :
    fderiv ℝ (normK m a R) x.val v = -2*((R-m)/(R^2+a^2))*G m a 0 x (twistVec (a/(R^2+a^2)) x.val) v := by
  have hrD := ksRadius_differentiableAt a x.val x.property
  have hcD := ksNull_differentiableAt a x.val x.property 3
  have hden : (ksRadius a x.val)^2+a^2*(ksNull a x.val 3)^2 ≠ 0 := by rw [hr]; positivity
  have hA : R^2+a^2 ≠ 0 := by positivity
  have hf : DifferentiableAt ℝ (factorK m a R) x.val := by
    unfold factorK factorAt
    fun_prop (disch := first | assumption | positivity)
  let line := fun t : ℝ => x.val+t • v
  have h0 : line 0=x.val := by simp [line]
  have hline : HasDerivAt line v 0 := by
    simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x.val
  have he : (normK m a R) =ᶠ[𝓝 x.val] (fun y => (ksRadius a y-R)*factorK m a R y) := by
    filter_upwards [(continuous_ksRadius a).continuousAt.eventually (lt_mem_nhds x.property)] with y hy
    exact norm_factored m a R hR hroot y hy
  have hdiff : DifferentiableAt ℝ (normK m a R) x.val := ((hrD.sub_const R).mul hf).congr_of_eventuallyEq he
  have lineD (f : E4 → ℝ) (hd : DifferentiableAt ℝ f x.val) :
      HasDerivAt (fun t => f (line t)) (fderiv ℝ f x.val v) 0 := by
    have h : HasFDerivAt f (fderiv ℝ f x.val) (line 0) := by rw [h0]; exact hd.hasFDerivAt
    exact h.comp_hasDerivAt 0 hline
  have hcomp : (fun t => normK m a R (line t)) =ᶠ[𝓝 0]
      (fun t => (ksRadius a (line t)-R)*factorK m a R (line t)) :=
    he.comp_tendsto (by simpa only [h0] using hline.continuousAt.tendsto)
  have h := (lineD _ hdiff).unique ((((lineD _ hrD).sub_const R).mul (lineD _ hf)).congr_of_eventuallyEq hcomp)
  rw [h0,hr] at h
  obtain ⟨hfac,hflat⟩ := on_horizon m a R hR hroot x hr
  rw [h,hfac,hflat]; ring

theorem solution (m a R : ℝ) (hR : 0 < R) (hroot : R^2-2*m*R+a^2 = 0) :
    let A := R^2+a^2
    let Ω := a/A
    let κ := (R-m)/A
    let g := kerrNewmanMetricField m a 0
    let F := kerrNewmanFieldField a 0
    ∃ χ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a,
      IsSymmetryFlow g F χ ∧
      (∀ x, (flowGenerator χ x : E4) = WithLp.toLp 2 ![1,-Ω*x.val 2,Ω*x.val 1,0]) ∧
      ∀ x : kerrNewmanSpacetime a, ksRadius a x.val = R →
        g x (flowGenerator χ x) (flowGenerator χ x) = 0 ∧
        ∀ e ∈ atlas E4 (kerrNewmanSpacetime a), ∀ y ∈ e.target, e.symm y = x → ∀ i : Fin 4,
          coordPartial (fun z => g (e.symm z) (flowGenerator χ (e.symm z)) (flowGenerator χ (e.symm z))) i y =
            -2*κ*loweredCoeffs g (flowGenerator χ) e.symm y i := by
  let Ω := a/(R^2+a^2)
  let κ := (R-m)/(R^2+a^2)
  let X := fun x : U a => twistVec Ω x.val
  obtain ⟨χ,hχ,hX⟩ := kerr_vacuum_helical_symmetry m a Ω
  change flowGenerator χ = X at hX
  refine ⟨χ,hχ,fun x => congrFun hX x,?_⟩
  rw [hX]
  intro x hx
  constructor
  · change normK m a R x.val=0
    rw [norm_factored m a R hR hroot _ x.property,hx];ring
  · intro e he y hy hyx i
    obtain ⟨p,hp⟩ := TopologicalSpace.Opens.chart_eq (H := E4) ⟨e.symm y⟩ he
    have hchart (w : U a) : e=chartAt E4 w := hp.trans (by rfl)
    have hval (z : E4) (hz : z ∈ e.target) : (e.symm z).val=z := by
      have h (w : U a) : e w=w.val := by rw [hchart w]; rfl
      exact (h (e.symm z)).symm.trans (e.right_inv hz)
    have hxy : x.val=y := by simpa only [hyx] using hval y hy
    have hd : (mfderiv I4 I4 e.symm y : E4 →L[ℝ] E4)=ContinuousLinearMap.id ℝ E4 := by
      rw [← hxy,hchart x]
      have hh := mfderivWithin_range_extChartAt_symm (I := I4) (x := x)
      simp only [modelWithCornersSelf_coe,range_id,mfderivWithin_univ] at hh
      exact hh
    have heq : (fun z => normK m a R (e.symm z).val) =ᶠ[𝓝 y] normK m a R := by
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      rw [hval z hz]
    change fderiv ℝ (fun z => normK m a R (e.symm z).val) y (coordBasis i) =
      (-2*κ)*G m a 0 (e.symm y) (twistVec Ω (e.symm y).val) (mfderiv I4 I4 e.symm y (coordBasis i))
    rw [heq.fderiv_eq,hd,hyx,← hxy]
    exact horizon_derivative m a R hR hroot x hx (coordBasis i)
