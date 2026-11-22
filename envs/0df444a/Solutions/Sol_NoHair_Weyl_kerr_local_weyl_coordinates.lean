-- Prove2me | solution 1 for NoHair.Weyl.kerr_local_weyl_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:45:40.288468+00:00
-- url     : https://prove2.me/submissions/a91b30af-38f3-46ea-b422-77c9bc205a86

import Definitions.Def_NoHair_kerrWeylModel
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

noncomputable section
open NoHair NoHair.Weyl Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

private theorem primitive_on (l : ℝ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Ioi l)) (hfm : Measurable f) :
    ∃ F : ℝ → ℝ, ContDiffOn ℝ ∞ F (Ioi l) ∧ ∀ r ∈ Ioi l, HasDerivAt F (f r) r := by
  let F := fun b : ℝ => ∫ u in l+1..b, f u
  have hder (r) (hr : r ∈ Ioi l) : HasDerivAt F (f r) r := by
    have hl : l+1 ∈ Ioi l := by change l<l+1; linarith
    exact intervalIntegral.integral_hasDerivAt_right
      ((hf.continuousOn.mono (ordConnected_Ioi.uIcc_subset hl hr)).intervalIntegrable)
      hfm.aestronglyMeasurable.stronglyMeasurableAtFilter
      (hf.continuousOn.continuousAt (Ioi_mem_nhds hr))
  exact ⟨F,(contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).2
    ⟨fun r hr => (hder r hr).differentiableAt.differentiableWithinAt,
     hf.congr (fun r hr => (hder r hr).deriv)⟩,hder⟩

private theorem local_inverse (f : E4 → E4) (U : Set E4) (hU : IsOpen U) (y : E4) (hy : y ∈ U)
    (hsm : ∀ z ∈ U, ContDiffAt ℝ ∞ f z) (hi : ∀ z ∈ U, Function.Injective (fderiv ℝ f z)) :
    ∃ V, y ∈ V ∧ V ⊆ U ∧ IsOpen V ∧ IsOpen (f '' V) ∧ IsDiffeoOnto f V (f '' V) := by
  let L (z : E4) (hz : z ∈ U) : E4 ≃L[ℝ] E4 :=
    (LinearEquiv.ofBijective (fderiv ℝ f z).toLinearMap
      ⟨hi z hz,LinearMap.injective_iff_surjective.mp (hi z hz)⟩).toContinuousLinearEquiv
  have hL (z) (hz : z ∈ U) : HasFDerivAt f (L z hz : E4 →L[ℝ] E4) z :=
    ((hsm z hz).differentiableAt (by simp)).hasFDerivAt
  let e := (hsm y hy).toOpenPartialHomeomorph f (hL y hy) (by simp)
  let V := e.source ∩ U
  have hV : IsOpen V := e.open_source.inter hU
  refine ⟨V,⟨(hsm y hy).mem_toOpenPartialHomeomorph_source (hL y hy) (by simp),hy⟩,
    inter_subset_right,hV,e.isOpen_image_of_subset_source hV inter_subset_left,
    e.symm,mapsTo_image _ _,?_,?_,?_,?_,?_⟩
  · rintro _ ⟨z,hz,rfl⟩
    change e.symm (e z) ∈ V
    rwa [e.left_inv hz.1]
  · exact fun z hz => e.left_inv hz.1
  · rintro _ ⟨z,hz,rfl⟩
    exact e.right_inv (e.map_source hz.1)
  · apply ContDiffOn.contMDiffOn
    exact fun z hz => (hsm z hz.2).contDiffWithinAt
  · apply ContDiffOn.contMDiffOn
    rintro _ ⟨z,hz,rfl⟩
    apply ContDiffAt.contDiffWithinAt
    change ContDiffAt ℝ ∞ e.symm (e z)
    apply e.contDiffAt_symm (f₀' := L z hz.2) (e.map_source hz.1)
    · rw [e.left_inv hz.1]; exact hL z hz.2
    · rw [e.left_inv hz.1]; exact hsm z hz.2

private def dotP (X Y : ℝ) (z : E4) := X*z 1+Y*z 2
private def crossP (X Y : ℝ) (z : E4) := X*z 2-Y*z 1
private def phase (X Y : ℝ) (z : E4) := Real.arctan (crossP X Y z / dotP X Y z)

private theorem phase_algebra (X Y x y u v : ℝ) (h : X*x+Y*y ≠ 0) (hQ : x^2+y^2 ≠ 0) :
    1/(1+((X*y-Y*x)/(X*x+Y*y))^2) *
      (((X*v-Y*u)*(X*x+Y*y)-(X*y-Y*x)*(X*u+Y*v))/(X*x+Y*y)^2) =
    (x*v-y*u)/(x^2+y^2) := by
  have halg (U V dU dV q j M : ℝ) (hu : U ≠ 0) (hq : q ≠ 0)
      (h₁ : U^2+V^2=M*q) (h₂ : dV*U-V*dU=M*j) :
      1/(1+(V/U)^2)*((dV*U-V*dU)/U^2)=j/q := by
    have hn : 0 < U^2+V^2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hu) (sq_nonneg _)
    have hx : 1+(V/U)^2=(U^2+V^2)/U^2 := by field_simp [hu] <;> ring
    calc
      _=(dV*U-V*dU)/(U^2+V^2) := by rw [hx]; field_simp [hu,hn.ne'] <;> ring
      _=j/q := by apply (div_eq_div_iff hn.ne' hq).2; rw [h₁,h₂]; ring
  exact halg _ _ _ _ _ _ (X^2+Y^2) h hQ (by ring) (by ring)

private theorem phase_line (X Y : ℝ) (z v : E4) (hu : 0 < dotP X Y z)
    (hq : 0 < z 1^2+z 2^2) :
    HasDerivAt (fun t : ℝ => phase X Y (z+t • v))
      ((z 1*v 2-z 2*v 1)/(z 1^2+z 2^2)) 0 := by
  let line := fun t : ℝ => z+t • v
  have h (i : Fin 4) : HasDerivAt (fun t => line t i) (v i) 0 := by
    simpa only [line,line_apply] using hasDerivAt_line_coord z v i
  have hU := ((h 1).const_mul X).add ((h 2).const_mul Y)
  have hV := ((h 2).const_mul X).sub ((h 1).const_mul Y)
  have hline : line 0 = z := by simp [line]
  have hd : HasDerivAt (fun t => crossP X Y (line t)/dotP X Y (line t))
      (((X*v 2-Y*v 1)*dotP X Y z-crossP X Y z*(X*v 1+Y*v 2))/(dotP X Y z)^2) 0 := by
    apply (hV.div hU (by change dotP X Y (line 0) ≠ 0; rw [hline]; exact hu.ne')).congr_deriv
    change _ = _
    simp only [Pi.add_apply,Pi.sub_apply,hline,dotP,crossP]
  apply hd.arctan.congr_deriv
  rw [hline]
  exact phase_algebra X Y _ _ _ _ hu.ne' hq.ne'

private def chartMap (m a X Y : ℝ) (T F : ℝ → ℝ) (z : E4) : E4 :=
  let r := ksRadius a z
  let c := z 3/r
  WithLp.toLp 2 ![z 0-T r, phase X Y z-F r,
    Real.sqrt (kerrDelta m a r)*Real.sqrt (1-c^2), (r-m)*c]

private theorem q_pos (z : E4) (h : z 1≠0 ∨ z 2≠0) : 0 < z 1^2+z 2^2 := by
  rcases h with h|h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h)

private theorem angular_pos (a : ℝ) (z : E4) (hr : 0 < ksRadius a z) (hq : 0 < z 1^2+z 2^2) :
    0 < 1-(z 3/ksRadius a z)^2 := by
  let r := ksRadius a z
  let c := z 3/r
  have hz : z 3=r*c := by
    have hr' : r ≠ 0 := hr.ne'
    dsimp [c]; field_simp [hr']
  have hs : 0 < r^2+a^2 := by have : 0 < r := hr; positivity
  have eqQ : z 1^2+z 2^2 = (r^2+a^2)*(1-c^2) := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hr.ne')
    have e := ks_C a z hr
    change r^4-(z 1^2+z 2^2+z 3^2-a^2)*r^2-a^2*z 3^2=0 at e
    rw [hz] at e
    linear_combination -e
  exact (mul_pos_iff_of_pos_left hs).1 (eqQ ▸ hq)

private theorem delta_pos (m a r : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0)
    (hr : m+Real.sqrt (m^2-a^2)<r) : 0 < kerrDelta m a r := by
  let k := Real.sqrt (m^2-a^2)
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hk2 : k^2=m^2-a^2 := Real.sq_sqrt (by nlinarith [hm.2])
  have hx : k<r-m := by change m+k<r at hr; linarith
  dsimp [kerrDelta]
  nlinarith only [hk2,mul_pos (sub_pos.mpr hx) (add_pos_of_pos_of_nonneg (hk.trans_lt hx) hk)]

private theorem chart_smooth (m a X Y : ℝ) (T F : ℝ → ℝ) (z : E4)
    (ht : ContDiffAt ℝ ∞ T (ksRadius a z)) (hf : ContDiffAt ℝ ∞ F (ksRadius a z))
    (hr : 0 < ksRadius a z) (hu : 0 < dotP X Y z)
    (hA : 0 < kerrDelta m a (ksRadius a z)) (hB : 0 < 1-(z 3/ksRadius a z)^2) :
    ContDiffAt ℝ ∞ (chartMap m a X Y T F) z := by
  have hR : ContDiffAt ℝ ∞ (ksRadius a) z := by
    have hD := (ks_D_pos a z hr).ne'
    have hQ := (ks_Q_pos a z hr).ne'
    rw [ksRadius_eq']
    fun_prop (disch := assumption)
  have hπ (i : Fin 4) : ContDiffAt ℝ ∞ (fun w : E4 => w i) z :=
    (contDiffAt_piLp 2).1 contDiffAt_id i
  have hc : ContDiffAt ℝ ∞ (fun w : E4 => w 3/ksRadius a w) z :=
    (hπ 3).div hR hr.ne'
  have hphase : ContDiffAt ℝ ∞ (phase X Y) z := by
    have hune : X*z 1+Y*z 2 ≠ 0 := hu.ne'
    unfold phase crossP dotP
    apply Real.contDiff_arctan.contDiffAt.comp z
    fun_prop (disch := assumption)
  apply (contDiffAt_piLp 2).2
  intro i
  fin_cases i
  · exact (hπ 0).sub (ht.comp z hR)
  · exact hphase.sub (hf.comp z hR)
  · have hd : ContDiffAt ℝ ∞ (fun w => kerrDelta m a (ksRadius a w)) z :=
      ((hR.pow 2).sub (contDiffAt_const.mul hR)).add contDiffAt_const
    exact (hd.sqrt hA.ne').mul ((contDiffAt_const.sub (hc.pow 2)).sqrt hB.ne')
  · exact (hR.sub contDiffAt_const).mul hc

private theorem chart_jacobian (m a X Y : ℝ) (T F : ℝ → ℝ) (z v : E4)
    (hsm : ContDiffAt ℝ ∞ (chartMap m a X Y T F) z)
    (ht : HasDerivAt T (2*m*ksRadius a z/kerrDelta m a (ksRadius a z)) (ksRadius a z))
    (hf : HasDerivAt F (2*m*ksRadius a z*a/(kerrDelta m a (ksRadius a z)*(ksRadius a z^2+a^2)))
      (ksRadius a z))
    (hr : 0 < ksRadius a z) (hu : 0 < dotP X Y z) (hq : 0 < z 1^2+z 2^2)
    (hA : 0 < kerrDelta m a (ksRadius a z)) (hB : 0 < 1-(z 3/ksRadius a z)^2) :
    let f := chartMap m a X Y T F
    let r := ksRadius a z
    let c := z 3/r
    let dr := fderiv ℝ (ksRadius a) z v
    let dc := (v 3-c*dr)/r
    let b := fderiv ℝ f z v
    b 0 = v 0-(2*m*r/kerrDelta m a r)*dr ∧
    b 1 = (z 1*v 2-z 2*v 1)/(z 1^2+z 2^2)-(2*m*r*a/(kerrDelta m a r*(r^2+a^2)))*dr ∧
    (f z) 2*b 2 = (r-m)*(1-c^2)*dr-kerrDelta m a r*c*dc ∧
    b 3 = c*dr+(r-m)*dc := by
  let f := chartMap m a X Y T F
  let r := ksRadius a z
  let c := z 3/r
  let dr := fderiv ℝ (ksRadius a) z v
  let dc := (v 3-c*dr)/r
  let line := fun t : ℝ => z+t • v
  let R := fun t => ksRadius a (line t)
  let C := fun t => line t 3 / R t
  have hl : HasDerivAt line v 0 := by
    simpa [line] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have hl₀ : line 0=z := by simp [line]
  have hR₀ : R 0=r := by simp [R,hl₀,r]
  have hC₀ : C 0=c := by simp [C,hl₀,hR₀,c]
  have hR : HasDerivAt R dr 0 := by
    have h : HasFDerivAt (ksRadius a) (fderiv ℝ (ksRadius a) z) (line 0) := by
      rw [hl₀]; exact (ksRadius_differentiableAt a z hr).hasFDerivAt
    exact h.comp_hasDerivAt 0 hl
  have hv (i : Fin 4) : HasDerivAt (fun t => line t i) (v i) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt 0 hl
  have hC : HasDerivAt C dc 0 := by
    apply ((hv 3).div hR (by rw [hR₀]; exact hr.ne')).congr_deriv
    rw [hl₀,hR₀]
    dsimp [dc,c]
    have hr' : r ≠ 0 := hr.ne'
    field_simp [hr'] <;> ring
  have hJ : HasDerivAt (fun t => f (line t)) (fderiv ℝ f z v) 0 := by
    have h : HasFDerivAt f (fderiv ℝ f z) (line 0) := by
      rw [hl₀]; exact (hsm.differentiableAt (by simp)).hasFDerivAt
    exact h.comp_hasDerivAt 0 hl
  have hb (i : Fin 4) : HasDerivAt (fun t => f (line t) i) (fderiv ℝ f z v i) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt 0 hJ
  have hT : HasDerivAt T (2*m*r/kerrDelta m a r) (R 0) := by rw [hR₀]; exact ht
  have hF : HasDerivAt F (2*m*r*a/(kerrDelta m a r*(r^2+a^2))) (R 0) := by rw [hR₀]; exact hf
  have hA' : HasDerivAt (fun t => kerrDelta m a (R t)) ((2*r-2*m)*dr) 0 := by
    apply (((hR.pow 2).sub (hR.const_mul (2*m))).add_const (a^2)).congr_deriv
    simp [hR₀] <;> ring
  have hB' : HasDerivAt (fun t => 1-C t^2) (-2*c*dc) 0 := by
    apply ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hC.pow 2)).congr_deriv
    simp [hC₀] <;> ring
  have ha0 : 0 < kerrDelta m a (R 0) := by rw [hR₀]; exact hA
  have hb0 : 0 < 1-C 0^2 := by rw [hC₀]; exact hB
  have haN := hA'.continuousAt.eventually (lt_mem_nhds ha0)
  have hbN := hB'.continuousAt.eventually (lt_mem_nhds hb0)
  have hρeq : (fun t => (f (line t) 2)^2) =ᶠ[𝓝 (0:ℝ)]
      (fun t => kerrDelta m a (R t)*(1-C t^2)) := by
    filter_upwards [haN,hbN] with t ha hc
    change (Real.sqrt (kerrDelta m a (R t))*Real.sqrt (1-C t^2))^2=_
    rw [mul_pow,Real.sq_sqrt (le_of_lt ha),Real.sq_sqrt (le_of_lt hc)]
  have hz := (hb 3).unique ((hR.sub_const m).mul hC)
  have hρ := ((hb 2).pow 2).unique ((hA'.mul hB').congr_of_eventuallyEq hρeq)
  simp only [hR₀,hC₀,hl₀, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hz hρ
  refine ⟨(hb 0).unique ((hv 0).sub (hT.comp 0 hR)),?_,?_,?_⟩
  · exact (hb 1).unique ((phase_line X Y z v hu hq).sub (hF.comp 0 hR))
  · change f z 2*_= (r-m)*(1-c^2)*dr-kerrDelta m a r*c*dc
    linear_combination (1 / 2 : ℝ)*hρ
  · change _=c*dr+(r-m)*dc
    linear_combination hz

private theorem kernel_zero (m a : ℝ) (z v : E4)
    (hr : 0 < ksRadius a z) (hx : 0 < ksRadius a z-m)
    (hq : 0 < z 1^2+z 2^2) (hA : 0 < kerrDelta m a (ksRadius a z))
    (hB : 0 < 1-(z 3/ksRadius a z)^2) :
    let r := ksRadius a z
    let c := z 3/r
    let dr := fderiv ℝ (ksRadius a) z v
    let dc := (v 3-c*dr)/r
    0 = v 0-(2*m*r/kerrDelta m a r)*dr →
    0 = (z 1*v 2-z 2*v 1)/(z 1^2+z 2^2)-(2*m*r*a/(kerrDelta m a r*(r^2+a^2)))*dr →
    0 = (r-m)*(1-c^2)*dr-kerrDelta m a r*c*dc →
    0 = c*dr+(r-m)*dc → v=0 := by
  let r := ksRadius a z
  let x := r-m
  let c := z 3/r
  let A := kerrDelta m a r
  let B := 1-c^2
  let dr := fderiv ℝ (ksRadius a) z v
  let dc := (v 3-c*dr)/r
  dsimp only
  intro ht hf hρ hz
  change 0=x*B*dr-A*c*dc at hρ
  change 0=c*dr+x*dc at hz
  have hx2 : 0 < x^2*B+A*c^2 :=
    add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_ne_zero hx.ne') hB) (mul_nonneg hA.le (sq_nonneg _))
  have hdr : dr=0 := by
    apply (mul_eq_zero.mp (show (x^2*B+A*c^2)*dr=0 by
      linear_combination -x*hρ-(A*c)*hz)).resolve_left hx2.ne'
  have hdc : dc=0 := by
    rw [hdr,mul_zero,zero_add] at hz
    exact (mul_eq_zero.mp hz.symm).resolve_left hx.ne'
  have hvz : v 3=0 := by
    change (v 3-c*dr)/r=0 at hdc
    rw [hdr,mul_zero,sub_zero] at hdc
    exact (div_eq_zero_iff.mp hdc).resolve_right hr.ne'
  have hv0 : v 0=0 := by
    change 0=v 0-_*dr at ht
    simpa only [hdr,mul_zero,sub_zero] using ht.symm
  have hK : z 1*v 2-z 2*v 1=0 := by
    change 0=(_)/(z 1^2+z 2^2)-_*dr at hf
    rw [hdr,mul_zero,sub_zero] at hf
    exact (div_eq_zero_iff.mp hf.symm).resolve_right hq.ne'
  have hd := fderiv_eq_of_line (ksRadius_differentiableAt a z hr) (hasDerivAt_ksRadius_line a z v hr)
  change dr=r*(r^2*(z 1*v 1+z 2*v 2)+(r^2+a^2)*z 3*v 3)/(r^4+a^2*z 3^2) at hd
  rw [hdr,hvz,mul_zero,add_zero] at hd
  have hL : z 1*v 1+z 2*v 2=0 := by
    have hn := (div_eq_zero_iff.mp hd.symm).resolve_right (ks_den_pos a z hr).ne'
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hn).resolve_left hr.ne')).resolve_left (pow_ne_zero 2 hr.ne')
  have h1 : v 1=0 := (mul_eq_zero.mp (show (z 1^2+z 2^2)*v 1=0 by
    linear_combination (z 1)*hL-(z 2)*hK)).resolve_left hq.ne'
  have h2 : v 2=0 := (mul_eq_zero.mp (show (z 1^2+z 2^2)*v 2=0 by
    linear_combination (z 2)*hL+(z 1)*hK)).resolve_left hq.ne'
  ext i
  fin_cases i
  · exact hv0
  · exact h1
  · exact h2
  · exact hvz

set_option maxHeartbeats 1600000 in
theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    ∀ y ∈ offAxisExterior m a, ∃ V c, y ∈ V ∧ IsKerrWeylChart m a V c := by
  let k := Real.sqrt (m^2-a^2)
  let l := m+k
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hd (r : ℝ) (hr : r ∈ Ioi l) : 0 < kerrDelta m a r := delta_pos m a r hm hr
  have hrp (r : ℝ) (hr : r ∈ Ioi l) : 0 < r := (add_pos_of_pos_of_nonneg hm.1 hk).trans hr
  let speed := fun r => 2*m*r/kerrDelta m a r
  let turn := fun r => 2*m*r*a/(kerrDelta m a r*(r^2+a^2))
  have hsmooth : ContDiffOn ℝ ∞ speed (Ioi l) := by
    intro r hr
    have hn := (hd r hr).ne'
    change ContDiffWithinAt ℝ ∞ (fun t => 2*m*t/(t^2-2*m*t+a^2)) (Ioi l) r
    unfold kerrDelta at hn
    fun_prop (disch := assumption)
  have fsmooth : ContDiffOn ℝ ∞ turn (Ioi l) := by
    intro r hr
    have hs : 0 < r^2+a^2 := by have := hrp r hr; positivity
    have hn := (mul_pos (hd r hr) hs).ne'
    change ContDiffWithinAt ℝ ∞ (fun t => 2*m*t*a/((t^2-2*m*t+a^2)*(t^2+a^2))) (Ioi l) r
    unfold kerrDelta at hn
    fun_prop (disch := assumption)
  obtain ⟨T,hT,ht⟩ := primitive_on l speed hsmooth (by unfold speed kerrDelta; fun_prop)
  obtain ⟨F,hF,hf⟩ := primitive_on l turn fsmooth (by unfold turn kerrDelta; fun_prop)
  intro y hy
  let X := y 1
  let Y := y 2
  let U := {z : E4 | l < ksRadius a z} ∩ {z | 0 < dotP X Y z}
  let f := chartMap m a X Y T F
  have houter : kerrNewmanOuterRadius m a 0=l := by simp [kerrNewmanOuterRadius,l,k]
  have hyU : y ∈ U := by
    constructor
    · have he : kerrNewmanOuterRadius m a 0 < ksRadius a y := hy.1
      exact houter ▸ he
    · change 0 < y 1*y 1+y 2*y 2
      simpa only [sq] using q_pos y hy.2
  have hop : IsOpen U := (isOpen_lt continuous_const (continuous_ksRadius a)).inter
    (isOpen_lt continuous_const (by unfold dotP; fun_prop))
  have haxis (z) (hz : z ∈ U) : z ∈ offAxisExterior m a := by
    refine ⟨?_,?_⟩
    · change kerrNewmanOuterRadius m a 0<ksRadius a z
      rw [houter]; exact hz.1
    · by_contra! h
      have : 0 < dotP X Y z := hz.2
      simp [dotP,h.1,h.2] at this
  have hsm (z) (hz : z ∈ U) : ContDiffAt ℝ ∞ f z :=
    chart_smooth m a X Y T F z (hT.contDiffAt (Ioi_mem_nhds hz.1))
      (hF.contDiffAt (Ioi_mem_nhds hz.1)) (hrp _ hz.1) hz.2 (hd _ hz.1)
      (angular_pos a z (hrp _ hz.1) (q_pos z (haxis z hz).2))
  have jac (z) (hz : z ∈ U) (v : E4) := chart_jacobian m a X Y T F z v (hsm z hz)
    (ht _ hz.1) (hf _ hz.1) (hrp _ hz.1) hz.2 (q_pos z (haxis z hz).2)
    (hd _ hz.1) (angular_pos a z (hrp _ hz.1) (q_pos z (haxis z hz).2))
  have hi (z) (hz : z ∈ U) : Function.Injective (fderiv ℝ f z) := by
    apply (injective_iff_map_eq_zero (fderiv ℝ f z)).2
    intro v hv
    obtain ⟨jt,jf,jr,jz⟩ := jac z hz v
    have hcomp (i : Fin 4) : fderiv ℝ f z v i=0 := by rw [hv]; rfl
    have hrt : l < ksRadius a z := hz.1
    have hx : 0 < ksRadius a z-m := by dsimp [l] at hrt; linarith
    apply kernel_zero m a z v (hrp _ hz.1) hx (q_pos z (haxis z hz).2) (hd _ hz.1)
      (angular_pos a z (hrp _ hz.1) (q_pos z (haxis z hz).2))
    · exact (hcomp 0).symm.trans jt
    · exact (hcomp 1).symm.trans jf
    · calc
        0=(f z) 2*fderiv ℝ f z v 2 := by rw [hcomp,mul_zero]
        _=_ := jr
    · exact (hcomp 3).symm.trans jz
  obtain ⟨V,hyV,hVU,hV,himg,hdif⟩ := local_inverse f U hop y hyU hsm hi
  refine ⟨V,f,hyV,hV,(fun _ h => haxis _ (hVU h)),himg,hdif,?_,?_,?_⟩
  · intro z hz
    exact mul_pos (Real.sqrt_pos.mpr (hd _ (hVU hz).1))
      (Real.sqrt_pos.mpr (angular_pos a z (hrp _ (hVU hz).1) (q_pos z (haxis z (hVU hz)).2)))
  · intro z hz
    exact ⟨rfl,rfl⟩
  · intro z hz i
    have h := jac z (hVU hz) (coordBasis i)
    exact ⟨h.1,h.2.1⟩
