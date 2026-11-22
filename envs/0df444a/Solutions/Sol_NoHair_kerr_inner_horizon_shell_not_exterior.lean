-- Prove2me | solution 1 for NoHair.kerr_inner_horizon_shell_not_exterior
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:16:11.36467+00:00
-- url     : https://prove2.me/submissions/5544276a-7d09-4920-8972-553a498b0865

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

private def four (t x y z : ℝ) : E4 := WithLp.toLp 2 ![t,x,y,z]
private def oblate (a r t X Y Z : ℝ) := four t (r*X-a*Y) (a*X+r*Y) (r*Z)
private def sigma (a Z r : ℝ) := r^2+a^2*Z^2
private def bigP (a r : ℝ) := r^2+a^2
private def massTerm (m e r : ℝ) := 2*m*r-e^2

private theorem oblate_data (a r t X Y Z : ℝ) (hr : 0 < r) (hk : X^2+Y^2+Z^2=1) :
    let y := oblate a r t X Y Z
    ksRadius a y = r ∧ ksNull a y = ![1,X,Y,Z] ∧ r  ≤  spatialRadius y := by
  let ρ2 := (r*X-a*Y)^2+(a*X+r*Y)^2+(r*Z)^2
  have hρ : ρ2 = r^2+a^2*(1-Z^2) := by
    dsimp [ρ2]; linear_combination (r^2+a^2)*hk
  have hs : 0  ≤  r^2+a^2*Z^2 := by positivity
  have hc : ρ2-a^2 = r^2-a^2*Z^2 := by rw [hρ]; ring
  have hD : (ρ2-a^2)^2+4*a^2*(r*Z)^2 = (r^2+a^2*Z^2)^2 := by rw [hc]; ring
  have hrad : ksRadius a (oblate a r t X Y Z) = r := by
    change Real.sqrt ((ρ2-a^2+Real.sqrt ((ρ2-a^2)^2+4*a^2*(r*Z)^2))/2)=r
    rw [hD, Real.sqrt_sq hs, hc]
    convert Real.sqrt_sq hr.le using 2 <;> ring
  refine ⟨hrad, ?_, ?_⟩
  · unfold ksNull
    rw [hrad]
    have hden : r^2+a^2  ≠  0 := by positivity
    funext i
    fin_cases i <;> simp [four,oblate, hden, hr.ne'] <;> field_simp [hden,hr.ne'] <;> ring
  · change r  ≤  Real.sqrt ρ2
    have hxy : 0  ≤  1-Z^2 := by nlinarith only [hk,sq_nonneg X,sq_nonneg Y]
    apply Real.le_sqrt_of_sq_le
    rw [hρ]; linarith [mul_nonneg (sq_nonneg a) hxy]

private def velocityShape (a r X Y Z u : ℝ) : E4 :=
  four (bigP a r) (-a*(a*X+r*Y)+u*X) (a*(r*X-a*Y)+u*Y) (u*Z)

private theorem metric_entries (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0)+v 1*w 1+v 2*w 2+v 3*w 3+
      ksProfile m a e x.val * (v 0 + ksNull a x.val 1*v 1+ksNull a x.val 2*v 2+ksNull a x.val 3*v 3) *
        (w 0 + ksNull a x.val 1*w 1+ksNull a x.val 2*w 2+ksNull a x.val 3*w 3) := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, Fin.sum_univ_four, ksNull_zero]
  simp [minkowski] <;> ring

private theorem four_deriv {t x y z : ℝ → ℝ} {dt dx dy dz s : ℝ}
    (ht : HasDerivAt t dt s) (hx : HasDerivAt x dx s) (hy : HasDerivAt y dy s) (hz : HasDerivAt z dz s) :
    HasDerivAt (fun s => four (t s) (x s) (y s) (z s)) (four dt dx dy dz) s := by
  have h : HasDerivAt (fun s => (![t s,x s,y s,z s] : Fin 4 → ℝ)) ![dt,dx,dy,dz] s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ht
    · exact hx
    · exact hy
    · exact hz
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt s h

private theorem ambient_velocity (a : ℝ) (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ)
    (s : ℝ) (v : E4) (hd : HasDerivAt (fun t => (γ t).val) v s) : (velocity γ s : E4) = v := by
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.mdifferentiableAt (by simp))
  have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ s) : E4 →L[ℝ] E4) =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
  rw [hinc] at hcomp
  have h : fderiv ℝ (fun t => (γ t).val) s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
    rw [← mfderiv_eq_fderiv]
    exact hcomp
  exact (congrArg (fun A : ℝ →L[ℝ] E4 => A 1) h).symm.trans hd.deriv


private theorem reverse_sq (c tau q B j : ℝ) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (ht : tau^2=q+1) (hj : j^2≤B*q) : c^2-B ≤ (j-c*tau)^2 := by
  rcases hq.eq_or_lt with hz|hp
  · subst q
    have hj' : j=0 := by nlinarith only [hj,sq_nonneg j]
    rw [hj']
    nlinarith only [hB,show c^2*tau^2=c^2 by rw [ht]; ring]
  · apply (le_of_mul_le_mul_left (a := q) ?_ hp)
    have he : q*((j-c*tau)^2-(c^2-B)) = (tau*j-c*q)^2+(B*q-j^2) := by
      linear_combination (q*c^2-j^2)*ht
    nlinarith only [he,hj,sq_nonneg (tau*j-c*q)]

private theorem radial_unit (z : U 2) (v : E4) (hv : G (5/2) 2 0 z v v = -1)
    (hr1 : 1 < ksRadius 2 z.val) (hr2 : ksRadius 2 z.val ≤ 2) :
    ksRadius 2 z.val-1 ≤ 4*(fderiv ℝ (ksRadius 2) z.val v)^2 := by
  let r := ksRadius 2 z.val
  let k := axis 2 z.val
  let n := radialNormal 2 z.val
  let s := space v
  let t := timeC v
  let W := Wf 2 z.val
  let f := ksProfile (5/2) 2 0 z.val
  let c := f/2
  let l := t+dot3 k s
  let tau := t-c*l
  let u := s+(c*l) • k
  let b := n+(-c) • k
  have hk : dot3 k k=1 := axis_unit 2 z
  obtain ⟨hnk,hn⟩ := normal_geometry 2 z
  change dot3 n k=1 at hnk
  change dot3 n n=(r^2+2^2)*W at hn
  have ff : f=2*c := by dsimp only [c]; ring
  have ht : tau^2=dot3 u u+1 := by
    have he : dot3 u u-tau^2= -t*t+dot3 s s+f*l*l := by
      simp only [u,tau,l,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hk,dot_symm s k]
      rw [ff]; ring
    rw [metric_formula] at hv
    change -(t*t)+dot3 s s+f*l*l= -1 at hv
    linarith
  have hb : dot3 b b=dot3 n n-f+c^2 := by
    simp only [b,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hnk,dot_symm k n,hk]
    rw [ff]; ring
  have he : dot3 n s = dot3 b u-c*tau := by
    simp only [b,u,tau,l,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hnk,hk]; ring
  have self (w : V3) : 0 ≤ dot3 w w := by
    unfold dot3; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hcs := reverse_sq c tau (dot3 u u) (dot3 b b) (dot3 b u) (self u) (self b) ht (dot_cauchy b u)
  rw [← he,hb,hn] at hcs
  have hf : f=(5*r)*W := by
    change ksProfile (5/2) 2 0 z.val=_
    rw [profile_eq _ _ _ _ z.property]
    dsimp only [fA]; ring
  have hW : W*(r^2+2^2*(k 2)^2)=1 := ks_W 2 z.val z.property
  have hW0 : 0 < W := by dsimp only [W,Wf]; have := z.property; positivity
  have hrel : k 0^2+k 1^2+k 2^2=1 := ks_rel 2 z.val z.property
  have hZ : (k 2)^2 ≤ 1 := by nlinarith only [hrel,sq_nonneg (k 0),sq_nonneg (k 1)]
  have hs : r^2+2^2*(k 2)^2≤8 := by
    have hr : r≤2 := hr2
    have hz : 0≤r := z.property.le
    nlinarith only [hZ,mul_nonneg (sub_nonneg.mpr hr) (show 0≤2+r by linarith)]
  have hw8 : 1≤8*W := by nlinarith only [hW,mul_nonneg hW0.le (sub_nonneg.mpr hs)]
  have hr1' : 0≤r-1 := (sub_pos.mpr hr1).le
  have hmul : (r-1)*2≤(r-1)*(4-r) := by
    have hr : r≤2 := hr2
    exact mul_le_mul_of_nonneg_left (by linarith) hr1'
  rw [hf] at hcs
  rw [radial_derivative]
  change r-1≤4*(dot3 n s)^2
  nlinarith only [hcs,mul_nonneg hr1' (sub_nonneg.mpr hw8),
    mul_le_mul_of_nonneg_right hmul hW0.le]

/-- A positive function with the trapped-region radial rate cannot exist for all proper times. -/
private theorem no_trapped_line (r : ℝ → ℝ) (d : ℝ → ℝ) (h : ∀ t, HasDerivAt r (d t) t)
    (hp : ∀ t, 1 < r t) (h0 : r 0=2) (hrate : ∀ t, r t≤2 → r t-1 ≤ 4*(d t)^2) : False := by
  let f := fun t : ℝ => Real.sqrt (r t-1)+t^2/256
  have hs (t : ℝ) : HasDerivAt (fun t => Real.sqrt (r t-1)) (d t/(2*Real.sqrt (r t-1))) t :=
    ((h t).sub_const 1).sqrt (sub_pos.mpr (hp t)).ne'
  have hf (t : ℝ) : HasDerivAt f (d t/(2*Real.sqrt (r t-1))+t/128) t := by
    apply ((hs t).add (((hasDerivAt_id' t).pow 2).div_const 256)).congr_deriv
    simp <;> ring
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  obtain ⟨t,ht,hm⟩ := isCompact_Icc.exists_isMinOn (f := f)
    (nonempty_Icc.mpr (by norm_num : (-16:ℝ) ≤ 16)) hfc.continuousOn
  have hmin : f t≤1 := by
    have h' := hm (show (0:ℝ) ∈ Icc (-16) 16 by constructor <;> norm_num)
    norm_num [f,h0] at h' ⊢
    exact h'
  have hsp (w : ℝ) : 0 < Real.sqrt (r w-1) := Real.sqrt_pos.mpr (sub_pos.mpr (hp w))
  have hi : t ∈ Ioo (-16:ℝ) 16 := by
    have hpos := hsp t
    change Real.sqrt (r t-1)+t^2/256≤1 at hmin
    constructor
    · rcases ht.1.eq_or_lt with eq|lt
      · rw [← eq] at hpos hmin; norm_num at hmin; linarith
      · exact lt
    · rcases ht.2.eq_or_lt with eq|lt
      · rw [eq] at hpos hmin; norm_num at hmin; linarith
      · exact lt
  have hminlocal := hm.isLocalMin (Icc_mem_nhds hi.1 hi.2)
  have hvan := hminlocal.hasDerivAt_eq_zero (hf t)
  let v := Real.sqrt (r t-1)
  have hv : 0<v := hsp t
  have hv2 : v^2=r t-1 := Real.sq_sqrt (sub_pos.mpr (hp t)).le
  have hv1 : v≤1 := by
    change v+t^2/256≤1 at hmin
    nlinarith only [hmin,sq_nonneg t]
  have hrt : r t≤2 := by nlinarith only [hv2,mul_nonneg (sub_nonneg.mpr hv1) (show 0≤1+v by linarith)]
  have hd := hrate t hrt
  change d t/(2*v)+t/128=0 at hvan
  have he : d t= -(t*v)/64 := by
    field_simp [hv.ne'] at hvan
    linarith
  rw [he,← hv2] at hd
  have ht2 : t^2<256 := by nlinarith only [mul_pos (sub_pos.mpr hi.2) (show 0<t+16 by linarith [hi.1])]
  nlinarith only [hd,mul_lt_mul_of_pos_right ht2 (sq_pos_of_pos hv),sq_pos_of_pos hv]

private theorem orbit_norm (m a r t X Y Z : ℝ) (hr : 0<r) (hk : X^2+Y^2+Z^2=1) :
    let y := oblate a r t X Y Z
    let v := velocityShape a r X Y Z 0
    matrixBilin (kerrNewmanMetric m a 0 y) v v =
      -((r^2+a^2-2*m*r)*(r^2+a^2*Z^2)) := by
  let y := oblate a r t X Y Z
  let v := velocityShape a r X Y Z 0
  obtain ⟨hR,hK,_⟩ := oblate_data a r t X Y Z hr hk
  have hs : 0 < r^2+a^2*Z^2 := by positivity
  let x : U a := ⟨y,show 0<ksRadius a y by rw [hR]; exact hr⟩
  have hp : ksProfile m a 0 y*(r^2+a^2*Z^2)=2*m*r := by
    rw [profile_eq m a 0 y x.property]
    dsimp only [fA,Wf]
    rw [hR,hK]
    change ((2*m*r-0^2)*(1/(r^2+a^2*Z^2)))*(r^2+a^2*Z^2)=_
    field_simp [hs.ne'] <;> ring
  have hvk : v 0+X*v 1+Y*v 2+Z*v 3=r^2+a^2*Z^2 := by
    change r^2+a^2+X*(-a*(a*X+r*Y)+0*X)+Y*(a*(r*X-a*Y)+0*Y)+Z*(0*Z)=_
    linear_combination -a^2*hk
  have hη : -(v 0*v 0)+v 1*v 1+v 2*v 2+v 3*v 3= -(r^2+a^2)*(r^2+a^2*Z^2) := by
    change -((r^2+a^2)*(r^2+a^2))+(-a*(a*X+r*Y)+0*X)*(-a*(a*X+r*Y)+0*X)+
      (a*(r*X-a*Y)+0*Y)*(a*(r*X-a*Y)+0*Y)+(0*Z)*(0*Z)=_
    linear_combination (a^2*(r^2+a^2))*hk
  change G m a 0 x v v=_
  rw [metric_entries]; change _+ksProfile m a 0 y*_ * _=_
  rw [hη]
  change _+ksProfile m a 0 y*(v 0+ksNull a y 1*v 1+ksNull a y 2*v 2+ksNull a y 3*v 3)*
    (v 0+ksNull a y 1*v 1+ksNull a y 2*v 2+ksNull a y 3*v 3)=_
  rw [hK]; simp only [Matrix.cons_val]; rw [hvk,hp]; ring

private theorem exterior_orbit (m a : ℝ) (hp : IsKerrNewmanBlackHoleParams m a 0)
    (p : E4) (hpD : p ∈ kerrNewmanDOC m a 0) :
    ∃ z : ℝ → E4, ContDiff ℝ 1 z ∧ z 0=p ∧
      ∀ t, z t ∈ kerrNewmanDOC m a 0 ∧
        matrixBilin (kerrNewmanMetric m a 0 (z t)) (deriv z t) (deriv z t) = -1 := by
  let r := ksRadius a p
  let X₀ := ksNull a p 1
  let Y₀ := ksNull a p 2
  let Z := ksNull a p 3
  let k := Real.sqrt (m^2-a^2-0^2)
  change m+k<r at hpD
  have hk0 : 0≤k := Real.sqrt_nonneg _
  have hk : k^2=m^2-a^2-0^2 := Real.sq_sqrt (by nlinarith [hp.2])
  have hr : 0<r := (add_pos_of_pos_of_nonneg hp.1 hk0).trans hpD
  have hΔ : 0<r^2+a^2-2*m*r := by
    nlinarith only [hk,mul_pos (show 0<r-m-k by linarith) (show 0<r-m+k by linarith)]
  let C := (r^2+a^2-2*m*r)*(r^2+a^2*Z^2)
  let N := 1/Real.sqrt C
  have hC : 0<C := mul_pos hΔ (by positivity)
  have hN : N^2*C=1 := by
    dsimp only [N]
    rw [div_pow, Real.sq_sqrt hC.le]; field_simp [hC.ne']
  let X := fun s : ℝ => X₀*Real.cos (a*N*s)-Y₀*Real.sin (a*N*s)
  let Y := fun s : ℝ => X₀*Real.sin (a*N*s)+Y₀*Real.cos (a*N*s)
  let tm := fun s : ℝ => p 0+(N*(r^2+a^2))*s
  let z := fun s : ℝ => oblate a r (tm s) (X s) (Y s) Z
  have hk' (s) : X s^2+Y s^2+Z^2=1 := by
    have h0 : X₀^2+Y₀^2+Z^2=1 := ks_rel a p hr
    dsimp only [X,Y]
    linear_combination (X₀^2+Y₀^2)*Real.sin_sq_add_cos_sq (a*N*s)+h0
  have hdiff : ContDiff ℝ 1 z := by
    unfold z oblate four
    apply PiLp.contDiff_toLp.comp
    apply contDiff_pi.mpr
    intro i; fin_cases i
    · change ContDiff ℝ 1 tm; dsimp [tm]; fun_prop
    · change ContDiff ℝ 1 (fun s => r*X s-a*Y s); dsimp [X,Y]; fun_prop
    · change ContDiff ℝ 1 (fun s => a*X s+r*Y s); dsimp [X,Y]; fun_prop
    · exact contDiff_const
  have h0 : z 0=p := by
    have hh : z 0=oblate a r (p 0) X₀ Y₀ Z := by simp [z,tm,X,Y]
    rw [hh]; ext i; fin_cases i
    · rfl
    · exact (ks_x1 a p hr).symm
    · exact (ks_x2 a p hr).symm
    · exact (ks_x3 a p hr).symm
  refine ⟨z,hdiff,h0,?_⟩
  intro s
  have hR := (oblate_data a r (tm s) (X s) (Y s) Z hr (hk' s)).1
  refine ⟨?_,?_⟩
  · change m+k<ksRadius a (z s)
    rw [show ksRadius a (z s)=r from hR]; exact hpD
  · let V := velocityShape a r (X s) (Y s) Z 0
    have hl : HasDerivAt (fun w : ℝ => a*N*w) (a*N) s := by
      simpa using (hasDerivAt_id' s).const_mul (a*N)
    have hx : HasDerivAt X (-(a*N)*Y s) s := by
      apply ((hl.cos.const_mul X₀).sub (hl.sin.const_mul Y₀)).congr_deriv
      dsimp [Y]; ring
    have hy : HasDerivAt Y (a*N*X s) s := by
      apply ((hl.sin.const_mul X₀).add (hl.cos.const_mul Y₀)).congr_deriv
      dsimp [X]; ring
    have ht : HasDerivAt tm (N*(r^2+a^2)) s := by
      simpa only [tm,mul_one] using (((hasDerivAt_id' s).const_mul (N*(r^2+a^2))).const_add (p 0))
    have hd : HasDerivAt z (N • V) s := by
      apply (four_deriv ht ((hx.const_mul r).sub (hy.const_mul a))
        ((hx.const_mul a).add (hy.const_mul r)) (hasDerivAt_const s (r*Z))).congr_deriv
      ext i; fin_cases i <;> simp [V,velocityShape,four,bigP,smul_eq_mul] <;> ring
    have hv : matrixBilin (kerrNewmanMetric m a 0 (z s)) V V = -C :=
      orbit_norm m a r (tm s) (X s) (Y s) Z hr (hk' s)
    rw [hd.deriv]
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,hv]
    linear_combination -hN

private theorem basis_sum (v : E4) : ∑ i, v i • coordBasis i=v := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_four,coordBasis]

private theorem evaluate_in_basis (B : E4 →L[ℝ] E4 →L[ℝ] ℝ) (L : E4 →L[ℝ] E4) (v : E4) :
    matrixBilin (fun i j => B (L (coordBasis i)) (L (coordBasis j))) v v = B (L v) (L v) := by
  have hl : L v = ∑ i, v i • L (coordBasis i) := by
    calc
      L v = L (∑ i, v i • coordBasis i) := congrArg L (basis_sum v).symm
      _ = _ := by simp only [map_sum,map_smul]
  let M : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => B (L (coordBasis i)) (L (coordBasis j))
  change Matrix.toLinearMap₂' ℝ M (WithLp.ofLp v) (WithLp.ofLp v)=B (L v) (L v)
  rw [hl,Matrix.toLinearMap₂'_apply M (WithLp.ofLp v) (WithLp.ofLp v)]
  simp only [M,Matrix.of_apply,map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pullback_value {a : ℝ} (g : BilinField (U a)) (Ψ : E4 → U a) (y v : E4) :
    matrixBilin (pullbackCoeffs g Ψ y) v v =
      g (Ψ y) (mfderiv I4 I4 Ψ y v) (mfderiv I4 I4 Ψ y v) :=
  evaluate_in_basis (g (Ψ y)) (mfderiv I4 I4 Ψ y) v

private theorem radius_along (a : ℝ) (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ) (s : ℝ) :
    HasDerivAt (fun t => ksRadius a (γ t).val)
      (fderiv ℝ (ksRadius a) (γ s).val (velocity γ s)) s := by
  let z : ℝ → E4 := Subtype.val ∘ γ
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hz : ContDiff ℝ 1 z := (hval.comp hγ).contDiff
  have hd := (hz.differentiable_one s).hasDerivAt
  have he := ambient_velocity a γ hγ s (deriv z s) hd
  rw [he]
  exact (ksRadius_differentiableAt a (z s) (γ s).property).hasFDerivAt.comp_hasDerivAt s hd

theorem solution (μ b : ℝ) (hp : IsKerrNewmanBlackHoleParams μ b 0) :
    ¬ IsKerrNewmanDOC (kerrNewmanMetricField (5/2) 2 0) (kerrNewmanFieldField 2 0)
      {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val} μ b 0 := by
  rintro ⟨_,Ψ,⟨χ,hΨ,hχ,hleft,hright,hsm,_⟩,hcoeff⟩
  let y := oblate 2 2 0 0 0 1
  have hy : ksRadius 2 y=2 := (oblate_data 2 2 0 0 0 1 (by norm_num) (by norm_num)).1
  let x : U 2 := ⟨y,by change 0<ksRadius 2 y; rw [hy]; norm_num⟩
  let A := {x : U 2 | 1 < ksRadius 2 x.val}
  have hx : x ∈ A := by change 1<ksRadius 2 y; rw [hy]; norm_num
  let p := χ x
  obtain ⟨z,hz,h0,hzD⟩ := exterior_orbit μ b hp p (hχ hx)
  let γ := Ψ ∘ z
  have hop : IsOpen (kerrNewmanDOC μ b 0) := isOpen_lt continuous_const (continuous_ksRadius b)
  have hΨs (s) : ContMDiffAt I4 I4 1 Ψ (z s) :=
    ((hsm (z s) (hzD s).1).contMDiffAt (hop.mem_nhds (hzD s).1)).of_le (by simp)
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ :=
    fun s => (hΨs s).comp s (hz.contMDiff.contMDiffAt)
  have hγ0 : γ 0=x := by change Ψ (z 0)=x; rw [h0]; exact hright hx
  have hA (t) : 1<ksRadius 2 (γ t).val := hΨ (hzD t).1
  have hunit (t) : G (5/2) 2 0 (γ t) (velocity γ t) (velocity γ t)= -1 := by
    have he : (velocity γ t : E4)=mfderiv I4 I4 Ψ (z t) (deriv z t) := by
      unfold velocity γ
      rw [mfderiv_comp t ((hΨs t).mdifferentiableAt (by simp)) (hz.differentiable_one t).mdifferentiableAt]
      have hinner : (mfderiv 𝓘(ℝ,ℝ) I4 z t : ℝ →L[ℝ] E4) 1=deriv z t := by
        rw [mfderiv_eq_fderiv]; rfl
      exact congrArg (fun w : E4 => (mfderiv I4 I4 Ψ (z t) : E4 →L[ℝ] E4) w) hinner
    rw [he]
    change G (5/2) 2 0 (Ψ (z t)) _ _=_
    calc
      _=matrixBilin (pullbackCoeffs (G (5/2) 2 0) Ψ (z t)) (deriv z t) (deriv z t) :=
        (pullback_value (G (5/2) 2 0) Ψ (z t) (deriv z t)).symm
      _=_ := by rw [(hcoeff (z t) (hzD t).1).1]; exact (hzD t).2
  apply no_trapped_line (fun t => ksRadius 2 (γ t).val)
    (fun t => fderiv ℝ (ksRadius 2) (γ t).val (velocity γ t)) (radius_along 2 γ hγ) hA
    (by rw [hγ0]; exact hy)
  exact fun t ht => radial_unit (γ t) (velocity γ t) (hunit t) (hA t) ht
