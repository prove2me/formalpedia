-- Prove2me | solution 1 for NoHair.Weyl.kerr_normalized_charts_cover
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:40:22.971959+00:00
-- url     : https://prove2.me/submissions/99722d1b-7515-41de-ad4b-643e1ccaa156

import Theorems.Thm_NoHair_Weyl_kerr_oblate_exterior_differential
import Definitions.Def_NoHair_kerrNewman

noncomputable section

open NoHair NoHair.Weyl Set Filter Topology MeasureTheory
open scoped ContDiff Manifold Interval

private theorem smooth_primitive (f : ℝ → ℝ) (L : ℝ) (hmeas : Measurable f)
    (hf : ∀ x, L < x → ContDiffAt ℝ ∞ f x) :
    let P := fun t => ∫ s in (L+1)..t, f s
    ∀ x, L < x → ContDiffAt ℝ ∞ P x ∧ HasDerivAt P (f x) x := by
  let P := fun t => ∫ s in (L+1)..t, f s
  have hc : ContinuousOn f (Ioi L) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hd (x : ℝ) (hx : L < x) : HasDerivAt P (f x) x := by
    have sub : uIcc (L+1) x ⊆ Ioi L := fun t ht => (lt_min (by linarith) hx).trans_le ht.1
    exact intervalIntegral.integral_hasDerivAt_right ((hc.mono sub).intervalIntegrable)
      hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter (hf x hx).continuousAt
  have hs : ContDiffOn ℝ ∞ P (Ioi L) := by
    apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).2
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,?_⟩
    exact (show ContDiffOn ℝ ∞ f (Ioi L) from fun x hx => (hf x hx).contDiffWithinAt).congr
      fun x hx => (hd x hx).deriv
  exact fun x hx => ⟨hs.contDiffAt (Ioi_mem_nhds hx),hd x hx⟩

private theorem local_diffeo {U : Set E4} (hU : IsOpen U) (C : E4 → E4)
    (smooth : ∀ x∈U, ContDiffAt ℝ ∞ C x) (inj : ∀ x∈U, Function.Injective (fderiv ℝ C x))
    (y : E4) (hy : y∈U) :
    ∃ V : Set E4, IsOpen V ∧ y∈V ∧ V⊆U ∧ IsOpen (C '' V) ∧ IsDiffeoOnto C V (C '' V) := by
  have equivAt (x : E4) (hx : x∈U) : ∃ A : E4 ≃L[ℝ] E4, HasFDerivAt C (A : E4 →L[ℝ] E4) x := by
    let T := (fderiv ℝ C x).toLinearMap
    have hi : Function.Injective T := inj x hx
    let A := (LinearEquiv.ofBijective T ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
    exact ⟨A,((smooth x hx).differentiableAt (by norm_num)).hasFDerivAt⟩
  obtain ⟨A,ha⟩ := equivAt y hy
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by norm_num
  let e := (smooth y hy).toOpenPartialHomeomorph C ha hn
  have he : (e : E4 → E4)=C := (smooth y hy).toOpenPartialHomeomorph_coe ha hn
  let V:=e.source ∩ U
  have hv : IsOpen V := e.open_source.inter hU
  have him : IsOpen (C '' V) := he ▸ e.isOpen_image_of_subset_source hv inter_subset_left
  have hleft (x) (hx : x∈V) : e.symm (C x)=x := he ▸ e.left_inv hx.1
  refine ⟨V,hv,⟨(smooth y hy).mem_toOpenPartialHomeomorph_source ha hn,hy⟩,inter_subset_right,him,?_⟩
  refine ⟨e.symm, mapsTo_image _ _, ?_,hleft,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    rwa [hleft x hx]
  · rintro _ ⟨x,hx,rfl⟩
    rw [hleft x hx]
  · exact (show ContDiffOn ℝ ∞ C V from fun x hx => (smooth x hx.2).contDiffWithinAt).contMDiffOn
  · apply ContDiffOn.contMDiffOn
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨B,hb⟩:=equivAt x hx.2
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm (f₀':=B)
    · rw [←he]; exact e.map_source hx.1
    · rw [hleft x hx,he]; exact hb
    · rw [hleft x hx,he]; exact smooth x hx.2

private def angle (X Y : ℝ) (y : E4) :=
  Real.arctan ((X*y 2-Y*y 1)/(X*y 1+Y*y 2))

private theorem angle_linear (X Y : ℝ) (y v : E4) (hxy : 0 < X^2+Y^2)
    (hn : X*y 1+Y*y 2≠0) (hp : 0 < y 1^2+y 2^2) :
    HasDerivAt (fun t : ℝ => angle X Y (y+t • v))
      ((y 1*v 2-y 2*v 1)/(y 1^2+y 2^2)) 0 := by
  let g:=fun t : ℝ => y+t • v
  have h0 : g 0=y := by simp [g]
  have hg : HasDerivAt g v 0 := by simpa [g] using ((hasDerivAt_id' (0:ℝ)).smul_const v).const_add y
  have h (i : Fin 4) : HasDerivAt (fun t => (g t) i) (v i) 0 :=
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 4 => ℝ) i).hasFDerivAt.comp_hasDerivAt 0 hg
  have hN := ((h 2).const_mul X).fun_sub ((h 1).const_mul Y)
  have hD := ((h 1).const_mul X).fun_add ((h 2).const_mul Y)
  apply ((hN.fun_div hD (by simpa only [h0] using hn)).arctan).congr_deriv
  dsimp only
  rw [h0]
  have fraction (n d b e : ℝ) (hd : d≠0) :
      1/(1+(n/d)^2)*((b*d-n*e)/d^2)=(b*d-n*e)/(d^2+n^2) := by
    rw [show 1+(n/d)^2=(d^2+n^2)/d^2 by field_simp [hd] <;> ring]
    have hdn : 0 < d^2+n^2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hd) (sq_nonneg n)
    field_simp [hd,hdn.ne']
  rw [fraction _ _ _ _ hn,show (X*y 1+Y*y 2)^2+(X*y 2-Y*y 1)^2=
      (X^2+Y^2)*(y 1^2+y 2^2) by ring,
    show (X*v 2-Y*v 1)*(X*y 1+Y*y 2)-(X*y 2-Y*y 1)*(X*v 1+Y*v 2)=
      (X^2+Y^2)*(y 1*v 2-y 2*v 1) by ring,mul_div_mul_left _ _ hxy.ne']

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


private def admissible (m a X Y : ℝ) : Set E4 :=
  offAxisExterior m a ∩ {y | X*y 1+Y*y 2≠0}

private theorem admissible_open (m a X Y : ℝ) : IsOpen (admissible m a X Y) := by
  have hD : IsOpen (kerrNewmanDOC m a 0) := isOpen_lt continuous_const (continuous_ksRadius a)
  have h (i : Fin 4) : IsOpen {y : E4 | y i≠0} := isOpen_ne.preimage (show Continuous (fun y : E4 => y i) by fun_prop)
  exact (hD.inter ((h 1).union (h 2))).inter (isOpen_ne.preimage (show Continuous (fun y : E4 => X*y 1+Y*y 2) by fun_prop))

private def normalized (m a X Y : ℝ) (T F : ℝ → ℝ) (y : E4) : E4 :=
  let r:=ksRadius a y
  let c:=y 3/r
  WithLp.toLp 2 ![y 0-T r,angle X Y y-F r,Real.sqrt (kerrDelta m a r)*Real.sqrt (1-c^2),(r-m)*c]

private theorem map_smooth (m a X Y : ℝ) (T F : ℝ → ℝ)
    (hm : IsKerrNewmanBlackHoleParams m a 0) (y : E4) (hy : y∈admissible m a X Y)
    (hT : ContDiffAt ℝ ∞ T (ksRadius a y)) (hF : ContDiffAt ℝ ∞ F (ksRadius a y)) :
    ContDiffAt ℝ ∞ (normalized m a X Y T F) y := by
  obtain ⟨hr,hS,hΔ,_,hs,_⟩ := kerr_oblate_exterior_differential m a hm y hy.1
  have hc : ContDiffAt ℝ ∞ (fun q : E4 => q 3/ksRadius a q) y := by fun_prop (disch := exact hr.ne')
  have hd : ContDiffAt ℝ ∞ (fun q => kerrDelta m a (ksRadius a q)) y := by unfold kerrDelta; fun_prop
  have hang : ContDiffAt ℝ ∞ (angle X Y) y := by
    unfold angle
    apply Real.contDiff_arctan.contDiffAt.comp y
    exact ContDiffAt.div (by fun_prop) (by fun_prop) hy.2
  apply (contDiffAt_piLp 2).2
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun q : E4 => q 0-T (ksRadius a q)) y
    exact (contDiffAt_piLp_apply 2).sub (hT.comp y hs)
  · change ContDiffAt ℝ ∞ (fun q : E4 => angle X Y q-F (ksRadius a q)) y
    exact hang.sub (hF.comp y hs)
  · change ContDiffAt ℝ ∞ (fun q : E4 =>
      Real.sqrt (kerrDelta m a (ksRadius a q))*Real.sqrt (1-(q 3/ksRadius a q)^2)) y
    exact (hd.sqrt hΔ.ne').mul ((contDiffAt_const.sub (hc.pow 2)).sqrt hS.ne')
  · change ContDiffAt ℝ ∞ (fun q : E4 => (ksRadius a q-m)*(q 3/ksRadius a q)) y
    exact (hs.sub contDiffAt_const).mul hc

private theorem map_diff (m a X Y : ℝ) (T F : ℝ → ℝ)
    (hm : IsKerrNewmanBlackHoleParams m a 0) (hXY : 0 < X^2+Y^2)
    (y v : E4) (hy : y∈admissible m a X Y)
    (smooth : ContDiffAt ℝ ∞ (normalized m a X Y T F) y)
    (hT : HasDerivAt T (2*m*ksRadius a y/kerrDelta m a (ksRadius a y)) (ksRadius a y))
    (hF : HasDerivAt F (2*m*ksRadius a y*a/(kerrDelta m a (ksRadius a y)*((ksRadius a y)^2+a^2))) (ksRadius a y)) :
    let C:=normalized m a X Y T F
    let r:=ksRadius a y
    let c:=y 3/r
    let l:=radialDiff a y v
    let b:=cosineDiff a y v
    let J:=fderiv ℝ C y v
    J 0=v 0-2*m*r/kerrDelta m a r*l ∧
    J 1=(y 1*v 2-y 2*v 1)/(y 1^2+y 2^2)-2*m*r*a/(kerrDelta m a r*(r^2+a^2))*l ∧
    (C y) 2*J 2=(r-m)*(1-c^2)*l-kerrDelta m a r*c*b ∧ J 3=c*l+(r-m)*b := by
  let C:=normalized m a X Y T F
  let γ:=fun t : ℝ => y+t • v
  let R:=fun t => ksRadius a (γ t)
  let P:=fun t => (γ t) 3/R t
  let l:=radialDiff a y v
  let b:=cosineDiff a y v
  have h0 : γ 0=y := by simp [γ]
  obtain ⟨hr,hS,hΔ,hL,hs,_⟩ := kerr_oblate_exterior_differential m a hm y hy.1
  have hxy : 0 < y 1^2+y 2^2 := hL ▸ mul_pos (add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (sq_nonneg a)) hS
  obtain ⟨hγ,hR,hP⟩ := line_derivs a y v hr hs
  change HasDerivAt γ v 0 at hγ
  change HasDerivAt R l 0 at hR
  change HasDerivAt P b 0 at hP
  have hC : HasFDerivAt C (fderiv ℝ C y) (γ 0) := by rw [h0]; exact (smooth.differentiableAt (by norm_num)).hasFDerivAt
  have J (i : Fin 4) : HasDerivAt (fun t => (C (γ t)) i) ((fderiv ℝ C y v) i) 0 :=
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 4 => ℝ) i).hasFDerivAt.comp_hasDerivAt 0 (hC.comp_hasDerivAt 0 hγ)
  have t0 : HasDerivAt (fun t => (γ t) 0) (v 0) 0 :=
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 4 => ℝ) 0).hasFDerivAt.comp_hasDerivAt 0 hγ
  have hR0 : ksRadius a y=R 0 := by simp [R,h0]
  have tP := hT.comp_of_eq 0 hR hR0
  have fP := hF.comp_of_eq 0 hR hR0
  refine ⟨(J 0).unique (t0.fun_sub tP), (J 1).unique ((angle_linear X Y y v hXY hy.2 hxy).fun_sub fP),?_,?_⟩
  · have hv : ∀ᶠ t in 𝓝 (0:ℝ), γ t ∈ admissible m a X Y :=
      hγ.continuousAt (h0 ▸ (admissible_open m a X Y).mem_nhds hy)
    have eq₁ : (fun t => kerrDelta m a (R t)*(1-(P t)^2)) =ᶠ[𝓝 0] fun t => ((C (γ t)) 2)^2 := by
      filter_upwards [hv] with t ht
      obtain ⟨_,hS',hΔ',_⟩ := kerr_oblate_exterior_differential m a hm (γ t) ht.1
      change _=(Real.sqrt (kerrDelta m a (R t))*Real.sqrt (1-(P t)^2))^2
      rw [mul_pow,Real.sq_sqrt hΔ'.le,Real.sq_sqrt hS'.le]
    have h := (((J 2).fun_pow 2).congr_of_eventuallyEq eq₁).unique
      ((((hR.fun_pow 2).fun_sub (hR.const_mul (2*m))).add_const (a^2)).fun_mul ((hP.fun_pow 2).const_sub 1))
    simp only [R,P,h0,show (2:ℕ)-1=1 by decide,Nat.cast_ofNat,pow_one] at h
    change (C y) 2*(fderiv ℝ C y v) 2=_
    unfold kerrDelta
    linarith only [h]
  · have h := (J 3).unique ((hR.sub_const m).fun_mul hP)
    simp only [R,P,h0] at h
    linarith only [h]

private theorem map_injective (m a X Y : ℝ) (T F : ℝ → ℝ)
    (hm : IsKerrNewmanBlackHoleParams m a 0) (hXY : 0 < X^2+Y^2)
    (y : E4) (hy : y∈admissible m a X Y)
    (smooth : ContDiffAt ℝ ∞ (normalized m a X Y T F) y)
    (hT : HasDerivAt T (2*m*ksRadius a y/kerrDelta m a (ksRadius a y)) (ksRadius a y))
    (hF : HasDerivAt F (2*m*ksRadius a y*a/(kerrDelta m a (ksRadius a y)*((ksRadius a y)^2+a^2))) (ksRadius a y)) :
    Function.Injective (fderiv ℝ (normalized m a X Y T F) y) := by
  let C:=normalized m a X Y T F
  let r:=ksRadius a y
  let c:=y 3/r
  let u:=r-m
  let S:=1-c^2
  let Δ:=kerrDelta m a r
  obtain ⟨hr,hS,hΔ,hxy,_,dr⟩ := kerr_oblate_exterior_differential m a hm y hy.1
  change 0 < S at hS
  change 0 < Δ at hΔ
  have hlarge : m+Real.sqrt (m^2-a^2) < r := by
    simpa [r,kerrNewmanDOC,kerrNewmanOuterRadius] using hy.1.1
  have hu : 0 < u := by dsimp [u]; linarith [Real.sqrt_nonneg (m^2-a^2)]
  have hdet : 0 < u^2*S+Δ*c^2 :=
    add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_pos hu) hS) (mul_nonneg hΔ.le (sq_nonneg c))
  have hL : 0 < y 1^2+y 2^2 :=
    hxy ▸ mul_pos (add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (sq_nonneg a)) hS
  apply (injective_iff_map_eq_zero (fderiv ℝ C y)).2
  intro v hv
  let l:=radialDiff a y v
  let b:=cosineDiff a y v
  have zero (i : Fin 4) : (fderiv ℝ C y v) i=0 := by rw [hv]; rfl
  obtain ⟨ht,hf,hρ,hz⟩ := map_diff m a X Y T F hm hXY y v hy smooth hT hF
  change (C y) 2*(fderiv ℝ C y v) 2=u*S*l-Δ*c*b at hρ
  change (fderiv ℝ C y v) 3=c*l+u*b at hz
  rw [zero,mul_zero] at hρ
  rw [zero] at hz
  have hprod : (u^2*S+Δ*c^2)*l=0 := by linear_combination -u*hρ-Δ*c*hz
  have hl : l=0 := (mul_eq_zero.mp hprod).resolve_left hdet.ne'
  rw [hl,mul_zero,zero_add] at hz
  have hb : b=0 := (mul_eq_zero.mp hz.symm).resolve_left hu.ne'
  change (v 3-c*l)/r=0 at hb
  rw [hl,mul_zero,sub_zero] at hb
  have vz := (div_eq_zero_iff.mp hb).resolve_right hr.ne'
  change (fderiv ℝ C y v) 0=v 0-2*m*r/Δ*l at ht
  change (fderiv ℝ C y v) 1=(y 1*v 2-y 2*v 1)/(y 1^2+y 2^2)-2*m*r*a/(Δ*(r^2+a^2))*l at hf
  rw [zero,hl,mul_zero,sub_zero] at ht hf
  have hP := (div_eq_zero_iff.mp hf.symm).resolve_right hL.ne'
  have hd := dr v
  change (r^2+a^2*c^2)*l=r*(y 1*v 1+y 2*v 2)+(r^2+a^2)*c*v 3 at hd
  rw [hl,vz,mul_zero,mul_zero,add_zero] at hd
  have hA := (mul_eq_zero.mp hd.symm).resolve_left hr.ne'
  have hx : (y 1^2+y 2^2)*v 1=0 := by linear_combination y 1*hA-y 2*hP
  have hq : (y 1^2+y 2^2)*v 2=0 := by linear_combination y 2*hA+y 1*hP
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  · exact ht.symm
  · exact (mul_eq_zero.mp hx).resolve_left hL.ne'
  · exact (mul_eq_zero.mp hq).resolve_left hL.ne'
  · exact vz

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    ∀ y ∈ offAxisExterior m a, ∃ V C, y ∈ V ∧ IsKerrWeylChart m a V C := by
  intro y hy
  let X:=y 1
  let Y:=y 2
  have hXY : 0 < X^2+Y^2 := by
    rcases hy.2 with h|h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg Y)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg X) (sq_pos_of_ne_zero h)
  let U:=admissible m a X Y
  have hyU : y∈U := ⟨hy,by
    change X*X+Y*Y≠0
    simpa only [sq] using hXY.ne'⟩
  let k:=Real.sqrt (m^2-a^2)
  let L:=m+k
  let fT:=fun r => 2*m*r/kerrDelta m a r
  let fF:=fun r => 2*m*r*a/(kerrDelta m a r*(r^2+a^2))
  let T:=fun r => ∫ s in (L+1)..r, fT s
  let F:=fun r => ∫ s in (L+1)..r, fF s
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hk2 : k^2=m^2-a^2 := Real.sq_sqrt (by nlinarith [hm.2])
  have pos (r : ℝ) (h : L < r) : 0 < kerrDelta m a r ∧ 0 < r^2+a^2 := by
    have hx : k < r-m := by dsimp [L] at h; linarith
    have hr : 0 < r := by linarith [hm.1]
    constructor
    · have hh := mul_pos (sub_pos.mpr hx) (show 0 < r-m+k by linarith)
      dsimp [kerrDelta]
      nlinarith only [hh,hk2]
    · positivity
  have ht (r : ℝ) (h : L < r) : ContDiffAt ℝ ∞ T r ∧ HasDerivAt T (fT r) r := by
    apply smooth_primitive fT L _ _ r h
    · unfold fT kerrDelta
      fun_prop
    · intro s hs
      have hd : ContDiffAt ℝ ∞ (kerrDelta m a) s := by unfold kerrDelta; fun_prop
      exact ContDiffAt.div (by fun_prop) hd (pos s hs).1.ne'
  have hf (r : ℝ) (h : L < r) : ContDiffAt ℝ ∞ F r ∧ HasDerivAt F (fF r) r := by
    apply smooth_primitive fF L _ _ r h
    · unfold fF kerrDelta
      fun_prop
    · intro s hs
      have hd : ContDiffAt ℝ ∞ (kerrDelta m a) s := by unfold kerrDelta; fun_prop
      exact ContDiffAt.div (by fun_prop) (hd.mul (by fun_prop)) (mul_ne_zero (pos s hs).1.ne' (pos s hs).2.ne')
  let C:=normalized m a X Y T F
  have rangeR (x : E4) (hx : x∈U) : L < ksRadius a x := by
    simpa [L,k,kerrNewmanDOC,kerrNewmanOuterRadius] using hx.1.1
  have smooth (x : E4) (hx : x∈U) : ContDiffAt ℝ ∞ C x :=
    map_smooth m a X Y T F hm x hx (ht _ (rangeR x hx)).1 (hf _ (rangeR x hx)).1
  have inj (x : E4) (hx : x∈U) : Function.Injective (fderiv ℝ C x) :=
    map_injective m a X Y T F hm hXY x hx (smooth x hx) (ht _ (rangeR x hx)).2 (hf _ (rangeR x hx)).2
  obtain ⟨V,hV,hyV,hVU,hI,hD⟩ := local_diffeo (admissible_open m a X Y) C smooth inj y hyU
  refine ⟨V,C,hyV,⟨hV,fun x hx => (hVU hx).1,hI,hD,?_,?_,?_⟩⟩
  · intro x hx
    obtain ⟨_,hS,hΔ,_⟩ := kerr_oblate_exterior_differential m a hm x (hVU hx).1
    exact mul_pos (Real.sqrt_pos.2 hΔ) (Real.sqrt_pos.2 hS)
  · intro x hx
    exact ⟨rfl,rfl⟩
  · intro x hx i
    have h:=map_diff m a X Y T F hm hXY x (coordBasis i) (hVU hx) (smooth x (hVU hx))
      (ht _ (rangeR x (hVU hx))).2 (hf _ (rangeR x (hVU hx))).2
    exact ⟨h.1,h.2.1⟩

