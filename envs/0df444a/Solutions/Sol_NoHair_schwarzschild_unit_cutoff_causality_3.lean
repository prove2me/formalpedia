-- Prove2me | solution 3 for NoHair.schwarzschild_unit_cutoff_causality
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:29:51.006192+00:00
-- url     : https://prove2.me/submissions/c86721b5-6be1-4fb5-a160-e80492c406cd

import Theorems.Thm_NoHair_kerrNewman_outerHorizon_futureTrapped
import Theorems.Thm_NoHair_kerrNewman_exterior_radialVelocityBound
import Theorems.Thm_NoHair_kerrNewman_mass_shell_compact_limit
import Definitions.Def_NoHair_KerrNewmanExteriorGeodesics
import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms

open Filter Topology
set_option backward.isDefEq.respectTransparency false

open NoHair NoHair.KNE Set
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

private theorem t_coords (m a e : ℝ) (x : U a) :
    timeC (T m a e x) = 1 + ksProfile m a e x.val / 2 ∧
    space (T m a e x) = -(ksProfile m a e x.val / 2) • axis a x.val := by
  refine ⟨rfl, ?_⟩
  ext i
  fin_cases i <;> rfl

private theorem metric_T (m a e : ℝ) (x : U a) (v : E4) :
    G m a e x v (T m a e x) = -timeC v + (ksProfile m a e x.val/2) *
      (timeC v + dot3 (axis a x.val) (space v)) := by
  obtain ⟨ht, hs⟩ := t_coords m a e x
  erw [metric_formula m a e x v (T m a e x), ht, hs, dot_scale_r, dot_scale_r, axis_unit, dot_symm (space v)]
  ring

private theorem time_orientation (m a e : ℝ) : IsTimeOrientation (G m a e) (T m a e) := by
  constructor
  · have hc : Continuous (fun x : U a => (T m a e x : E4)) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      have hr : Continuous (fun y : U a => ksRadius a y.val) := (continuous_ksRadius a).comp continuous_subtype_val
      have hk (i : Fin 4) : ContinuousAt (fun y : U a => ksNull a y.val i) x :=
        (ksNull_differentiableAt a x.val x.property i).continuousAt.comp continuous_subtype_val.continuousAt
      have hd := (ks_den_pos a x.val x.property).ne'
      have hf : ContinuousAt (fun y : U a => ksProfile m a e y.val) x := by
        unfold ksProfile
        fun_prop (disch := assumption)
      unfold T kerrNewmanTimeDirection
      apply (PiLp.continuous_toLp 2 _).continuousAt.comp
      apply continuousAt_pi.mpr
      intro i
      fin_cases i <;> simp only [Matrix.cons_val] <;> fun_prop
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [FiberBundle.continuousAt_section]
    have htr (y : U a) : (trivializationAt E4 (TangentSpace I4) x ⟨y,T m a e y⟩).2 = (T m a e y : E4) := by
      change tangentCoordChange I4 y y y (T m a e y) = _
      exact tangentCoordChange_self (mem_extChartAt_source y)
    simpa only [htr] using hc.continuousAt (x := x)
  · intro x
    obtain ⟨ht,hs⟩ := t_coords m a e x
    erw [metric_T m a e x (T m a e x), ht, hs, dot_scale_r, axis_unit]
    nlinarith


private theorem radius_eq (x : E4) : ksRadius 0 x = spatialRadius x := by
  let p := x 1^2+x 2^2+x 3^2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  change Real.sqrt ((p-0^2+Real.sqrt ((p-0^2)^2+4*0^2*x 3^2))/2) = Real.sqrt p
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, sub_zero, Real.sqrt_sq hp]
  congr 1
  ring


private theorem timelike_scale (m a e : ℝ) (x : U a) (v : E4) (N : ℝ) (hN : 0<N)
    (hv : IsFutureTimelike (G m a e) (T m a e) x v) :
    IsFutureTimelike (G m a e) (T m a e) x (N • v) := by
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  let w : E4 := T m a e x
  change A v v < 0 ∧ A v w < 0 at hv
  change A (N • v) (N • v)<0 ∧ A (N • v) w<0
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact ⟨mul_neg_of_pos_of_neg hN (mul_neg_of_pos_of_neg hN hv.1),mul_neg_of_pos_of_neg hN hv.2⟩


private abbrev Space := kerrNewmanSpacetime 0
private abbrev A : Set Space := (Subtype.val : Space → E4) ⁻¹' exteriorRegion 1
private abbrev big := G 1 0 0
private abbrev small := G (1/2) 0 0
private abbrev Tbig := T 1 0 0
private abbrev Tsmall := T (1/2) 0 0
private lemma halfParams : IsKerrNewmanBlackHoleParams (1/2) 0 0 := by norm_num [IsKerrNewmanBlackHoleParams]
private lemma oneParams : IsKerrNewmanBlackHoleParams 1 0 0 := by norm_num [IsKerrNewmanBlackHoleParams]
private lemma halfOuter : kerrNewmanOuterRadius (1/2) 0 0 = 1 := by norm_num [kerrNewmanOuterRadius]
private lemma small_domain : ((Subtype.val : Space → E4) ⁻¹' kerrNewmanDOC (1/2) 0 0) = A := by
  ext x
  change (kerrNewmanOuterRadius (1/2) 0 0 < ksRadius 0 x.val) ↔ 1 < spatialRadius x.val
  rw [halfOuter,radius_eq]
private lemma massDomain : ((Subtype.val : Space → E4) ⁻¹' {z | (1:ℝ) < ksRadius 0 z}) = A := by
  ext x; change (1 < ksRadius 0 x.val) ↔ 1 < spatialRadius x.val; rw [radius_eq]
private lemma profileS (m : ℝ) (x : Space) : ksProfile m 0 0 x.val = 2*m/ksRadius 0 x.val := by
  have h : 0 < ksRadius 0 x.val := x.property
  unfold ksProfile
  field_simp [h.ne'] <;> ring

private lemma wider (x : Space) (v : E4) (hne : v ≠ 0) (hg : big x v v ≤ 0) (ht : big x v (Tbig x) < 0) :
    small x v v ≤ big x v v ∧ small x v (Tsmall x) ≤ big x v (Tbig x) := by
  let f := ksProfile 1 0 0 x.val
  let l := timeC v + dot3 (axis 0 x.val) (space v)
  have fpos : 0 < f := by dsimp only [f]; rw [profileS]; exact div_pos (by norm_num) x.property
  have half : ksProfile (1/2) 0 0 x.val = f/2 := by dsimp only [f]; rw [profileS,profileS]; ring
  have tc := (NoHair.ExteriorGeodesics.cone_estimates 1 0 0 x fpos.le v (Tbig x) hne hg ht
    ((time_orientation 1 0 0).2 x)).2
  change 0 < timeC v * timeC (Tbig x) at tc
  rw [(t_coords 1 0 0 x).1] at tc
  have tv : 0 < timeC v := pos_of_mul_pos_left tc (by linarith [fpos] : 0 ≤ 1+f/2)
  have hh := hg
  rw [metric_formula] at hh
  have bound : dot3 (space v) (space v) ≤ (timeC v)^2 := by
    change -(timeC v * timeC v) + dot3 (space v) (space v) + f*l*l ≤ 0 at hh
    nlinarith only [hh, mul_nonneg fpos.le (sq_nonneg l)]
  have cs := dot_cauchy (axis 0 x.val) (space v)
  rw [axis_unit,one_mul] at cs
  have hl : 0 ≤ l := by
    have cmp := (sq_le_sq.mp (cs.trans bound)).trans_eq (abs_of_pos tv)
    dsimp only [l]; linarith [neg_abs_le (dot3 (axis 0 x.val) (space v))]
  constructor
  · rw [metric_formula,metric_formula,half]
    change -(timeC v*timeC v) + dot3 (space v) (space v) + (f/2)*l*l ≤ -(timeC v*timeC v) + dot3 (space v) (space v) + f*l*l
    nlinarith only [mul_nonneg fpos.le (sq_nonneg l)]
  · rw [metric_T, metric_T,half]
    change -timeC v+(f/2/2)*l ≤ -timeC v+(f/2)*l
    nlinarith only [mul_nonneg fpos.le hl]

private lemma widen_arc (S : Set Space) (γ : ℝ → Space) (hg : IsFutureCausalCurveIn big Tbig S γ) :
    IsFutureCausalCurveIn small Tsmall S γ := by
  refine ⟨hg.1, fun t ht => ?_⟩
  obtain ⟨hx,hn,hv,hw⟩ := hg.2 t ht
  obtain ⟨he,he'⟩ := wider _ _ hn hv hw
  exact ⟨hx,hn,he.trans hv,he'.trans_lt hw⟩

private lemma widen_timelike (γ : ℝ → Space) (hg : IsFutureTimelikeCurveIn big Tbig univ γ) :
    IsFutureTimelikeCurveIn small Tsmall univ γ := by
  refine ⟨hg.1,fun t ht => ?_⟩
  obtain ⟨hx,hv,hw⟩ := hg.2 t ht
  have hn : (velocity γ t : E4) ≠ 0 := by intro hn; change (big (γ t)) (velocity γ t) (velocity γ t) < 0 at hv; simp [hn] at hv
  obtain ⟨he,he'⟩ := wider _ _ hn hv.le hw
  exact ⟨hx,he.trans_lt hv,he'.trans_lt hw⟩

private def fourV (a b c d : ℝ) : E4 := WithLp.toLp 2 ![a,b,c,d]
private lemma vecDer {t x y z : ℝ → ℝ} {dt dx dy dz s : ℝ}
    (ht : HasDerivAt t dt s) (hx : HasDerivAt x dx s) (hy : HasDerivAt y dy s) (hz : HasDerivAt z dz s) :
    HasDerivAt (fun s => fourV (t s) (x s) (y s) (z s)) (fourV dt dx dy dz) s := by
  have h : HasDerivAt (fun s => (![t s,x s,y s,z s] : Fin 4 → ℝ)) ![dt,dx,dy,dz] s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    exacts [ht,hx,hy,hz]
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt s h

private def dir (x : Space) := fourV 2 (-ksNull 0 x.val 1) (-ksNull 0 x.val 2) (-ksNull 0 x.val 3)
private lemma dir_future (x : Space) (hr : 1 < ksRadius 0 x.val) : IsFutureTimelike big Tbig x (dir x) := by
  have tb : timeC (dir x)=2 := rfl
  have sp : space (dir x)=(-1:ℝ) • axis 0 x.val := by
    rw [neg_one_smul]
    ext i
    fin_cases i <;> rfl
  have hl : ksProfile 1 0 0 x.val < 2 := by rw [profileS]; exact (div_lt_iff₀ x.property).mpr (by linarith)
  constructor
  · rw [metric_formula,tb,sp,dot_scale_l,dot_scale_r,axis_unit]
    linarith
  · rw [metric_T,tb,sp,dot_scale_r,axis_unit]
    linarith

private def scaleR (a b t : ℝ) := Real.exp (-a*(t-b))
private def pathY (p : Space) (a b t : ℝ) : E4 :=
  let f := scaleR a b t
  let r := ksRadius 0 p.val
  fourV (p.val 0+2*r*(1-f)) (f*p.val 1) (f*p.val 2) (f*p.val 3)
private lemma path_radius (p : Space) (a b t : ℝ) : ksRadius 0 (pathY p a b t) =
    scaleR a b t * ksRadius 0 p.val := by
  let f := scaleR a b t
  have hf : 0<f := Real.exp_pos _
  let r := ksRadius 0 p.val
  have hr : 0 < r := p.property
  have hsq : r^2=p.val 1^2+p.val 2^2+p.val 3^2 := by dsimp only [r]; rw [radius_eq,spatialRadius,Real.sq_sqrt (by positivity)]
  rw [radius_eq]
  change Real.sqrt ((f*p.val 1)^2+(f*p.val 2)^2+(f*p.val 3)^2)=f*r
  have e : (f*p.val 1)^2+(f*p.val 2)^2+(f*p.val 3)^2=(f*r)^2 := by rw [show (f*r)^2=f^2*r^2 by ring,hsq]; ring
  rw [e,Real.sqrt_sq (mul_pos hf hr).le]

private def pathS (p : Space) (a b t : ℝ) : Space :=
  ⟨pathY p a b t,by change 0<ksRadius 0 (pathY p a b t); rw [path_radius]; exact mul_pos (Real.exp_pos _) p.property⟩

private lemma path_smooth (p:Space) (a b:ℝ) : ContMDiff 𝓘(ℝ,ℝ) I4 1 (pathS p a b) := by
  apply ContMDiff.of_le (n := ∞) _ (by simp)
  apply (ContMDiff.subtypeVal_comp_iff (U 0) (pathS p a b)).mp
  apply contMDiff_iff_contDiff.mpr
  change ContDiff ℝ ∞ (pathY p a b)
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [pathY,fourV,scaleR,Matrix.cons_val] <;> fun_prop

private lemma path_velocity (p : Space) (a b t : ℝ) :
    (velocity (pathS p a b) t : E4) = (a*ksRadius 0 (pathS p a b t).val) • dir (pathS p a b t) := by
  let x := pathS p a b t
  let f := scaleR a b t
  let r := ksRadius 0 p.val
  have hh : HasDerivAt (scaleR a b) (-a*f) t := by
    apply ((((hasDerivAt_id' t).sub_const b).const_mul (-a)).exp).congr_deriv
    change Real.exp (-a*(t-b)) * (-a*1) = -a*f
    dsimp only [f,scaleR]; ring
  have hd := vecDer (((hasDerivAt_const t (1:ℝ)).fun_sub hh).const_mul (2*r) |>.const_add (p.val 0))
    (hh.mul_const (p.val 1)) (hh.mul_const (p.val 2)) (hh.mul_const (p.val 3))
  have vel := NoHair.ExteriorGeodesics.ambient_velocity 0 (pathS p a b) (path_smooth p a b) t _ hd
  rw [vel]
  have hR : ksRadius 0 x.val = f*r := path_radius p a b t
  have h1 : f*p.val 1 = ksRadius 0 x.val * ksNull 0 x.val 1 := by
    change x.val 1 = _
    simpa only [zero_mul,sub_zero] using ks_x1 0 x.val x.property
  have h2 : f*p.val 2 = ksRadius 0 x.val * ksNull 0 x.val 2 := by
    change x.val 2 = _
    simpa only [zero_mul,zero_add] using ks_x2 0 x.val x.property
  have h3 : f*p.val 3 = ksRadius 0 x.val * ksNull 0 x.val 3 := ks_x3 0 x.val x.property
  apply (show ∀ v w : E4, (∀ i : Fin 4, v i=w i) → v=w from fun v w h => by ext i; exact h i) _ _
  intro i
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by fin_cases i <;> decide) with rfl|rfl|rfl|rfl
  · change 2*r*(0- -a*f)=a*ksRadius 0 x.val*2; rw [hR]; ring
  · change -a*f*p.val 1=a*ksRadius 0 x.val*(-ksNull 0 x.val 1); linear_combination (-a)*h1
  · change -a*f*p.val 2=a*ksRadius 0 x.val*(-ksNull 0 x.val 2); linear_combination (-a)*h2
  · change -a*f*p.val 3=a*ksRadius 0 x.val*(-ksNull 0 x.val 3); linear_combination (-a)*h3

private lemma neighbors (p : Space) (hp : p ∈ A) (b : ℝ) (hb : b ∈ Icc (0:ℝ) 1) :
    ∃ γ : ℝ → Space, IsFutureTimelikeCurveIn big Tbig univ γ ∧
      (∀ s ∈ Icc (0:ℝ) 1, γ s ∈ A) ∧ γ b=p := by
  let r := ksRadius 0 p.val
  have hr : 1<r := by change 1<ksRadius 0 p.val; rw [radius_eq]; exact hp
  have hr0 : 0<r := p.property
  let a := Real.log r/2
  have logpos := Real.log_pos hr
  have ha : 0<a := by dsimp only [a]; positivity
  have within (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : 1 < ksRadius 0 (pathS p a b s).val := by
    rw [show ksRadius 0 (pathS p a b s).val=scaleR a b s*r from path_radius p a b s]
    change 1<Real.exp (-a*(s-b))*r
    rw [← Real.exp_log hr0,← Real.exp_add]
    apply Real.one_lt_exp_iff.mpr
    have cmp := mul_le_mul_of_nonneg_left (show s-b ≤ 1 by linarith only [hs.2,hb.1]) ha.le
    have e : Real.log r=2*a := by dsimp only [a]; ring
    linarith
  refine ⟨pathS p a b,⟨path_smooth p a b,?_⟩,?_,?_⟩
  · intro s hs
    refine ⟨mem_univ _,?_⟩
    rw [path_velocity]
    exact timelike_scale 1 0 0 _ _ _ (mul_pos ha (pathS p a b s).property) (dir_future _ (within s hs))
  · intro s hs
    change 1<spatialRadius (pathS p a b s).val
    rw [← radius_eq]; exact within s hs
  · apply Subtype.ext
    change pathY p a b b=p.val
    have hf : scaleR a b b=1 := by simp [scaleR]
    unfold pathY
    rw [hf]
    ext i
    rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 by fin_cases i <;> decide) with rfl|rfl|rfl|rfl
    · change p.val 0+2*ksRadius 0 p.val*(1-1)=p.val 0; ring
    · change 1*p.val 1=p.val 1; ring
    · change 1*p.val 2=p.val 2; ring
    · change 1*p.val 3=p.val 3; ring

private lemma pastA : chronoPastSet big Tbig A = A := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨x,hx'⟩ := mem_iUnion.mp hp
    obtain ⟨hx,γ,hγ,hp',hx'⟩ := mem_iUnion.mp hx'
    by_contra h
    have hlow : ksRadius 0 (γ 0).val ≤ kerrNewmanOuterRadius (1/2) 0 0 := by
      rw [hp',halfOuter,radius_eq]; exact le_of_not_gt h
    have hr := (kerrNewman_outerHorizon_futureTrapped (1/2) 0 0 halfParams).2 γ (widen_timelike γ hγ) hlow
    rw [hx',halfOuter,radius_eq] at hr
    exact (not_lt.mpr hr) hx
  · intro p hp
    obtain ⟨γ,hγ,hmem,h0⟩ := neighbors p hp 0 (left_mem_Icc.mpr zero_le_one)
    exact mem_iUnion.mpr ⟨γ 1,mem_iUnion.mpr ⟨hmem _ (right_mem_Icc.mpr zero_le_one),γ,hγ,h0,rfl⟩⟩

private lemma futureA : A ⊆ chronoFutureSet big Tbig A := by
  intro p hp
  obtain ⟨γ,hγ,hmem,h1⟩ := neighbors p hp 1 (right_mem_Icc.mpr zero_le_one)
  exact mem_iUnion.mpr ⟨γ 0,mem_iUnion.mpr ⟨hmem _ (left_mem_Icc.mpr zero_le_one),γ,hγ,rfl,h1⟩⟩

namespace SchwarzschildConfinement
open NoHair Set
open scoped ContDiff Manifold BigOperators

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' kerrNewmanDOC m a e
private abbrev I4 := 𝓘(ℝ, E4)
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private def timeComponent (v : E4) : ℝ := v 0
private def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

private theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : x ∈ D m a e) : 0 ≤ ksProfile m a e x.val := by
  obtain ⟨hm, he⟩ := hp
  change m + Real.sqrt (m^2 - a^2 - e^2) < ksRadius a x.val at hx
  have hm' : m ≤ ksRadius a x.val := by linarith [Real.sqrt_nonneg (m^2-a^2-e^2)]
  have hnum : 0 ≤ 2*m*ksRadius a x.val - e^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hm' hm.le, he, sq_nonneg a, sq_nonneg m]
  unfold ksProfile
  exact div_nonneg (mul_nonneg (sq_nonneg _) hnum) (by positivity)

private theorem spatial_squares (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (hv : G m a e x v v ≤ 0) :
    (v 1)^2 + (v 2)^2 + (v 3)^2 ≤ (v 0)^2 := by
  rw [metric_formula] at hv
  nlinarith only [hv, mul_nonneg hf (sq_nonneg (kEval a x.val v))]

private theorem spatial_kernel (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (h0 : v 0 = 0) : 0 ≤ G m a e x v v := by
  rw [metric_formula, h0]
  nlinarith only [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3),
    mul_nonneg hf (sq_nonneg (kEval a x.val v))]

private theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G m a e x v v ≤ 0) (hvw : G m a e x v w < 0)
    (hww : G m a e x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) := by
  have hs := spatial_squares m a e x hf v hvv
  have hb (i : Fin 4) : |v i| ≤ |v 0| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs, sq_abs]
    fin_cases i <;> simp <;> nlinarith only [hs, sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv0 : v 0 ≠ 0 := by
    intro h
    apply hv
    ext i
    exact abs_nonpos_iff.mp (by simpa only [h, abs_zero] using hb i)
  refine ⟨hb, ?_⟩
  by_contra! hprod
  have hkernel := spatial_kernel m a e x hf ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul, mul_comm])
  have hsym : G m a e x w v = G m a e x v w := by rw [metric_formula, metric_formula]; ring
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hkernel
  change A w v = A v w at hsym
  change A w w < 0 at hww
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvw
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hsym] at hkernel
  nlinarith only [hkernel, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hv0) hww, mul_nonneg_of_nonpos_of_nonpos hprod hvw.le]

private theorem sign_on_interval (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0) (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < f u ↔ 0 < f v := by
  have imp (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hp : 0 < f s) :
      0 < f t := by
    by_contra! h
    obtain ⟨z, hz, he⟩ := isPreconnected_Icc.intermediate_value ht hs hf.continuousOn
      (show (0:ℝ) ∈ Icc (f t) (f s) from ⟨h,hp.le⟩)
    exact hn z hz he
  exact ⟨imp u v hu hv, imp v u hv hu⟩


private abbrev J := Icc (0:ℝ) 1
private def weight (m a e : ℝ) (z : E4) :=
  (ksRadius a z-kerrNewmanOuterRadius m a e)*Real.exp (-(z 0)/m)

private theorem monotone_from_deriv (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (h : ∀ s ∈ J, 0 ≤ d s) : MonotoneOn f J := by
  have hf : Differentiable ℝ f := fun s => (hd s).differentiableAt
  exact monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1) hf.continuous.continuousOn hf.differentiableOn
    (fun s hs => (hd s).deriv.symm ▸ h s (interior_subset hs))

private theorem curve_envelope (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) :
    let w (s : ℝ) := weight m a e (γ s).val
    (∀ s ∈ J, ∀ i : Fin 4, |(γ s).val i-(γ 0).val i| ≤ |(γ 1).val 0-(γ 0).val 0|) ∧
    (∀ s ∈ J, min (w 0) (w 1) ≤ w s) ∧
    ∀ s ∈ J, 0 ≤ ((γ 1).val 0-(γ 0).val 0)*timeComponent (T (γ s)) ∧
      (w 1-w 0)*timeComponent (T (γ s)) ≤ 0 := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let v (t : ℝ) : E4 := velocity γ t
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : fderiv ℝ f t = (mfderiv 𝓘(ℝ, ℝ) I4 γ t : ℝ →L[ℝ] E4) := by
    have h := mfderiv_comp t (hval.mdifferentiableAt (by simp) (x := γ t)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ t) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ t)
    rw [hinc] at h
    rw [← mfderiv_eq_fderiv]
    exact h
  have hc (i : Fin 4) : ContDiff ℝ 1 (fun t => f t i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hf
  have hder (i : Fin 4) (t : ℝ) : HasDerivAt (fun s => f s i) (v t i) t := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t ((hf.differentiable (by simp) t).hasFDerivAt)).hasDerivAt
    rw [hd] at h
    exact h
  have hcone (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (∀ i, |v t i| ≤ |v t 0|) ∧ 0 < (v t 0) * timeComponent (T (γ t)) := by
    obtain ⟨hx,hne,hvv,hvw⟩ := hγ.2 t ht
    exact cone_estimates m a e (γ t) (exterior_profile m a e hp _ hx)
      (v t) (T (γ t)) hne hvv hvw (hT.2 _)
  have hne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : v t 0 ≠ 0 := by
    have h := (hcone t ht).2
    intro he
    rw [he, zero_mul] at h
    exact (lt_irrefl _) h
  have hcont : Continuous (fun t => v t 0) := by
    have he : (fun t => v t 0) = deriv (fun t => f t 0) := funext (fun t => (hder 0 t).deriv.symm)
    rw [he]
    exact (hc 0).continuous_deriv le_rfl
  let o : ℝ := if 0 < v 0 0 then 1 else -1
  have ho : o=1 ∨ o= -1 := by unfold o; split <;> simp
  have h₀ : (0:ℝ) ∈ J := left_mem_Icc.mpr zero_le_one
  have h₁ : (1:ℝ) ∈ J := right_mem_Icc.mpr zero_le_one
  have hsign (s : ℝ) (hs : s ∈ J) : 0 < o*v s 0 := by
    have he := sign_on_interval (fun t => v t 0) hcont hne 0 s h₀ hs
    unfold o
    split_ifs with h
    · simpa using he.mp h
    · have hh : v s 0 < 0 := lt_of_le_of_ne (le_of_not_gt (fun h' => h (he.mpr h'))) (hne s hs)
      simpa using hh
  have hTsign (s : ℝ) (hs : s ∈ J) : 0 < o*timeComponent (T (γ s)) := by
    have h1 := hsign s hs
    have h2 := (hcone s hs).2
    rcases ho with h|h <;> rw [h] at h1 ⊢
    · simpa using pos_of_mul_pos_right h2 (by linarith : 0 ≤ v s 0)
    · have ht : timeComponent (T (γ s)) < 0 := by
        by_contra! ht
        exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (show v s 0 ≤ 0 by linarith) ht)) h2
      simpa using ht
  have hmag (s : ℝ) (hs : s ∈ J) : |v s 0| = o*v s 0 := by
    have hh := abs_of_pos (hsign s hs)
    rw [abs_mul] at hh
    rcases ho with h|h <;> simpa [h] using hh
  let b := kerrNewmanOuterRadius m a e
  let w (s : ℝ) := weight m a e (f s)
  let dv (s : ℝ) := fderiv ℝ (ksRadius a) (f s) (v s)
  let dw (s : ℝ) := Real.exp (-(f s 0)/m)*(dv s-(ksRadius a (f s)-b)*(v s 0)/m)
  have hdr (s : ℝ) : HasDerivAt (fun t => ksRadius a (f t)) (dv s) s := by
    have hv := ((hf.differentiable (by simp) s).hasFDerivAt).hasDerivAt
    rw [hd] at hv
    exact (ksRadius_differentiableAt a (f s) (γ s).property).hasFDerivAt.comp_hasDerivAt s hv
  have hdw (s : ℝ) : HasDerivAt w (dw s) s := by
    apply (((hdr s).sub_const b).mul (((hder 0 s).neg.div_const m).exp)).congr_deriv
    dsimp [dw]; ring
  have hwd (s : ℝ) (hs : s ∈ J) : o*dw s ≤ 0 := by
    have hvv := (hγ.2 s hs).2.2.1
    let A := matrixBilin (kerrNewmanMetric m a e (γ s).val)
    change A (v s) (v s) ≤ 0 at hvv
    have hvs : G m a e (γ s) (o • v s) (o • v s) ≤ 0 := by
      change A (o • v s) (o • v s) ≤ 0
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg o) hvv]
    have ht : 0 ≤ (o • v s) 0 := (hsign s hs).le
    have h := kerrNewman_exterior_radialVelocityBound m a e hp (γ s) (hγ.2 s hs).1 (o • v s) ht hvs
    rw [map_smul] at h
    change m*(o*dv s) ≤ (ksRadius a (f s)-b)*(o*v s 0) at h
    have hh : o*(dv s-(ksRadius a (f s)-b)*(v s 0)/m) ≤ 0 := by
      apply le_of_mul_le_mul_left (a := m) _ hp.1
      rw [mul_zero]
      field_simp [hp.1.ne']
      nlinarith only [mul_le_mul_of_nonneg_left h hp.1.le, h]
    calc
      o*dw s = Real.exp (-(f s 0)/m)*(o*(dv s-(ksRadius a (f s)-b)*(v s 0)/m)) := by dsimp [dw]; ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hh
  have hwmono : MonotoneOn (fun s => -(o*w s)) J :=
    monotone_from_deriv _ _ (fun s => ((hdw s).const_mul o).neg) (fun s hs => neg_nonneg.mpr (hwd s hs))
  have htmono : MonotoneOn (fun s => o*f s 0) J :=
    monotone_from_deriv _ _ (fun s => (hder 0 s).const_mul o) (fun s hs => (hsign s hs).le)
  have ht01 := htmono h₀ h₁ zero_le_one
  have hw01 := hwmono h₀ h₁ zero_le_one
  change o*f 0 0 ≤ o*f 1 0 at ht01
  change -(o*w 0) ≤ -(o*w 1) at hw01
  have hclock : o*(f 1 0-f 0 0) = |f 1 0-f 0 0| := by
    rcases ho with h|h <;> rw [h] at ht01 ⊢
    · rw [abs_of_nonneg (by linarith : 0 ≤ f 1 0-f 0 0)]; ring
    · rw [abs_of_nonpos (by linarith : f 1 0-f 0 0 ≤ 0)]; ring
  refine ⟨?_,?_,?_⟩
  · intro s hs i
    have hplus : MonotoneOn (fun s => o*f s 0+f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).add (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [neg_abs_le (v s i)])
    have hminus : MonotoneOn (fun s => o*f s 0-f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).sub (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [le_abs_self (v s i)])
    have ha := hplus h₀ hs hs.1
    have hb := hminus h₀ hs hs.1
    have hc := htmono hs h₁ hs.2
    beta_reduce at ha hb hc
    change |f s i-f 0 i| ≤ |f 1 0-f 0 0|
    rw [← hclock]
    exact abs_le.mpr ⟨by nlinarith only [ha,hc],by nlinarith only [hb,hc]⟩
  · intro s hs
    have ha := hwmono h₀ hs hs.1
    have hb := hwmono hs h₁ hs.2
    beta_reduce at ha hb
    change min (w 0) (w 1) ≤ w s
    rcases ho with h|h <;> rw [h] at ha hb
    · exact (min_le_right _ _).trans (by linarith)
    · exact (min_le_left _ _).trans (by linarith)
  · intro s hs
    have hO := hTsign s hs
    change 0 ≤ (f 1 0-f 0 0)*timeComponent (T (γ s)) ∧ (w 1-w 0)*timeComponent (T (γ s)) ≤ 0
    rcases ho with h|h <;> rw [h] at hO ht01 hw01
    · exact ⟨mul_nonneg (by linarith) (by linarith),mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)⟩
    · exact ⟨mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith),
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)⟩

theorem curve_estimates (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) :
    (∀ i : Fin 4, |(γ 1).val i - (γ 0).val i| ≤ |(γ 1).val 0 - (γ 0).val 0|) ∧
    ∀ t ∈ Icc (0:ℝ) 1, 0 < ((γ 1).val 0 - (γ 0).val 0) * timeComponent (T (γ t)) := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let v (t : ℝ) : E4 := velocity γ t
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : fderiv ℝ f t = (mfderiv 𝓘(ℝ, ℝ) I4 γ t : ℝ →L[ℝ] E4) := by
    have h := mfderiv_comp t (hval.mdifferentiableAt (by simp) (x := γ t)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ t) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ t)
    rw [hinc] at h
    rw [← mfderiv_eq_fderiv]
    exact h
  have hc (i : Fin 4) : ContDiff ℝ 1 (fun t => f t i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hf
  have hder (i : Fin 4) (t : ℝ) : HasDerivAt (fun s => f s i) (v t i) t := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t ((hf.differentiable (by simp) t).hasFDerivAt)).hasDerivAt
    rw [hd] at h
    exact h
  have hcone (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (∀ i, |v t i| ≤ |v t 0|) ∧ 0 < (v t 0) * timeComponent (T (γ t)) := by
    obtain ⟨hx,hne,hvv,hvw⟩ := hγ.2 t ht
    exact cone_estimates m a e (γ t) (exterior_profile m a e hp _ hx)
      (v t) (T (γ t)) hne hvv hvw (hT.2 _)
  have hne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : v t 0 ≠ 0 := by
    have h := (hcone t ht).2
    intro he
    rw [he, zero_mul] at h
    exact (lt_irrefl _) h
  have hcont : Continuous (fun t => v t 0) := by
    have he : (fun t => v t 0) = deriv (fun t => f t 0) := funext (fun t => (hder 0 t).deriv.symm)
    rw [he]
    exact (hc 0).continuous_deriv le_rfl
  constructor
  · intro i
    obtain ⟨c, hc', he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
      (fun t => f t 0) (fun t => v t 0) zero_lt_one (hc 0).continuous.continuousOn (fun t _ => hder 0 t)
      (fun t => f t i) (fun t => v t i) (hc i).continuous.continuousOn (fun t _ => hder i t)
    have hci := Ioo_subset_Icc_self hc'
    have h := congrArg abs he
    simp only [abs_mul] at h
    apply le_of_mul_le_mul_right (a := |v c 0|) _ (abs_pos.mpr (hne c hci))
    exact h.trans_le (mul_le_mul_of_nonneg_left ((hcone c hci).1 i) (abs_nonneg _))
  · intro t ht
    obtain ⟨c,hc',he⟩ := exists_hasDerivAt_eq_slope (fun s => f s 0) (fun s => v s 0) zero_lt_one
      (hc 0).continuous.continuousOn (fun s _ => hder 0 s)
    simp only [sub_zero, div_one] at he
    change 0 < (f 1 0 - f 0 0) * _
    rw [← he]
    have hci := Ioo_subset_Icc_self hc'
    have hsign := sign_on_interval (fun s => v s 0) hcont hne c t hci ht
    rcases (mul_pos_iff.mp (hcone t ht).2) with h|h
    · exact mul_pos (hsign.mpr h.1) h.2
    · have hneg : v c 0 < 0 := lt_of_le_of_ne (le_of_not_gt (fun hh => h.1.not_gt (hsign.mp hh))) (hne c hci)
      exact mul_pos_of_neg_of_neg hneg h.2

private theorem future_envelope (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) 
    (g' : BilinField (U a)) (T' : VecField (U a))
    (widen : ∀ γ, IsFutureCausalCurveIn g' T' (D m a e) γ →
      IsFutureCausalCurveIn (G m a e) T (D m a e) γ) (p q : U a) (hpD : p ∈ D m a e)
    (hq : q ∈ causalFuture g' T' (D m a e) p) :
    let w (x : U a) := weight m a e x.val
    let dt := q.val 0-p.val 0
    q ∈ D m a e ∧ (∀ i : Fin 4, |q.val i-p.val i| ≤ |dt|) ∧
      (0 ≤ dt*timeComponent (T p) ∧ (w q-w p)*timeComponent (T p) ≤ 0) ∧
      (0 ≤ dt*timeComponent (T q) ∧ (w q-w p)*timeComponent (T q) ≤ 0) ∧
      ∀ K : Set (U a), (∀ y : U a, min (w p) (w q) ≤ w y →
        (∀ i : Fin 4, |y.val i-p.val i| ≤ |dt|) → y∈K) →
          q ∈ causalFuture g' T' K p := by
  rcases hq with he|⟨γ,hγ,hp',hq'⟩
  · rcases Set.mem_singleton_iff.mp he with rfl
    refine ⟨hpD, by simp, by simp, by simp, fun K _ => Or.inl rfl⟩
  · subst p
    subst q
    obtain ⟨hc,hw,ht⟩ := curve_envelope m a e hp T hT γ (widen γ hγ)
    have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
    have h₁ : (1:ℝ)∈J := right_mem_Icc.mpr zero_le_one
    refine ⟨(hγ.2 1 h₁).1, hc 1 h₁, ht 0 h₀, ht 1 h₁, ?_⟩
    intro K hK
    refine Or.inr ⟨γ,⟨hγ.1,?_⟩,rfl,rfl⟩
    intro s hs
    exact ⟨hK _ (hw s hs) (hc s hs),(hγ.2 s hs).2⟩

private theorem interval_length (u v w s : ℝ) (hs : s ≠ 0)
    (h1 : 0 ≤ (v-u)*s) (h2 : 0 ≤ (w-v)*s) : |v-u| ≤ |w-u| := by
  rcases lt_or_gt_of_ne hs with hn|hp
  · have hv : v-u ≤ 0 := by by_contra! h; exact (not_lt_of_ge h1) (mul_neg_of_pos_of_neg h hn)
    have hw : w-v ≤ 0 := by by_contra! h; exact (not_lt_of_ge h2) (mul_neg_of_pos_of_neg h hn)
    rw [abs_of_nonpos hv, abs_of_nonpos (by linarith : w-u ≤ 0)]
    linarith
  · have hv : 0 ≤ v-u := by by_contra! h; exact (not_lt_of_ge h1) (mul_neg_of_neg_of_pos h hp)
    have hw : 0 ≤ w-v := by by_contra! h; exact (not_lt_of_ge h2) (mul_neg_of_neg_of_pos h hp)
    rw [abs_of_nonneg hv, abs_of_nonneg (by linarith : 0 ≤ w-u)]
    linarith

theorem compact_enclosure (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T)
    (g' : BilinField (U a)) (T' : VecField (U a))
    (widen : ∀ γ, IsFutureCausalCurveIn g' T' (D m a e) γ →
      IsFutureCausalCurveIn (G m a e) T (D m a e) γ) :
    let U := kerrNewmanSpacetime a
    let g := g'
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
    ∀ p ∈ D, ∀ q ∈ D, ∃ K : Set U, IsCompact K ∧ K ⊆ D ∧ p ∈ K ∧ q ∈ K ∧
      ∀ x ∈ causalFuture g T' D p ∩ causalPast g T' D q,
        x ∈ K ∧ x ∈ causalFuture g T' K p ∧ q ∈ causalFuture g T' K x := by
  dsimp only
  intro p hpD q hqD
  let w := weight m a e
  let l := min (w p.val) (w q.val)
  let B := |q.val 0-p.val 0|
  let C (i : Fin 4) := |q.val i-p.val i|+2*B+1
  let box : Set (Fin 4 → ℝ) := Icc (fun i => p.val i-C i) (fun i => p.val i+C i)
  let H : Set E4 := (WithLp.toLp 2 '' box) ∩ {z | l ≤ w z}
  let K := (Subtype.val : U a → E4) ⁻¹' H
  have hB : 0 ≤ B := abs_nonneg _
  have hC (i : Fin 4) : 2*B ≤ C i := by dsimp [C]; linarith [abs_nonneg (q.val i-p.val i)]
  have hW : Continuous w := by
    unfold w weight
    exact ((continuous_ksRadius a).sub continuous_const).mul (by fun_prop)
  have hH : IsCompact H := ((show IsCompact box from isCompact_Icc).image (PiLp.continuous_toLp 2 _)).inter_right
    (isClosed_le continuous_const hW)
  have hweight (z : U a) (hz : z∈D m a e) : 0 < w z.val :=
    mul_pos (sub_pos.mpr hz) (Real.exp_pos _)
  have hl : 0<l := lt_min (hweight p hpD) (hweight q hqD)
  have hreg (z : E4) (hz : z ∈ H) : kerrNewmanOuterRadius m a e < ksRadius a z := by
    have hw := hl.trans_le hz.2
    change 0 < (ksRadius a z-kerrNewmanOuterRadius m a e)*Real.exp (-(z 0)/m) at hw
    by_contra! h
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (Real.exp_pos _).le)) hw
  have hb : 0<kerrNewmanOuterRadius m a e := hp.1.trans_le (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hcompact : IsCompact K := by
    apply Subtype.isCompact_iff.mpr
    have himg : (Subtype.val : U a → E4) '' K = H := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩; exact hx
      · intro hz
        exact ⟨⟨z,hb.trans (hreg z hz)⟩,hz,rfl⟩
    rwa [himg]
  have put (x : U a) (hw : l ≤ w x.val) (h : ∀ i : Fin 4, |x.val i-p.val i| ≤ C i) : x∈K := by
    refine ⟨⟨WithLp.ofLp x.val,⟨?_,?_⟩,rfl⟩,hw⟩
    · intro i; have ha := (abs_le.mp (h i)).1; change p.val i-C i ≤ x.val i; linarith
    · intro i; have ha := (abs_le.mp (h i)).2; change x.val i ≤ p.val i+C i; linarith
  have hpK := put p (min_le_left _ _) (fun i => by simp only [sub_self,abs_zero]; linarith [hC i])
  have hqK := put q (min_le_right _ _) (fun i => by dsimp [C]; linarith)
  refine ⟨K,hcompact,fun x hx => hreg x.val hx,hpK,hqK,?_⟩
  intro x hx
  obtain ⟨hxD,hxp,_,h1,hleg1⟩ := future_envelope m a e hp T hT g' T' widen p x hpD hx.1
  obtain ⟨_,_,h2,_,hleg2⟩ := future_envelope m a e hp T hT g' T' widen x q hxD hx.2
  let s := timeComponent (T x)
  have hs : s ≠ 0 := fun h =>
    (not_lt_of_ge (spatial_kernel m a e x (exterior_profile m a e hp x hxD) (T x) h)) (hT.2 x)
  have hxpT : |x.val 0-p.val 0| ≤ B := interval_length _ _ _ s hs h1.1 h2.1
  have hxqT : |q.val 0-x.val 0| ≤ B := by
    rw [abs_sub_comm,show B = |p.val 0-q.val 0| from abs_sub_comm _ _]
    apply interval_length _ _ _ (-s) (neg_ne_zero.mpr hs)
    · nlinarith only [h2.1]
    · nlinarith only [h1.1]
  have hxw : l ≤ w x.val := by
    have hA : (w x.val-w p.val)*s ≤ 0 := h1.2
    have hB' : (w q.val-w x.val)*s ≤ 0 := h2.2
    rcases lt_or_gt_of_ne hs with hn|hpos
    · apply (min_le_left _ _).trans
      by_contra! he
      exact (not_lt_of_ge hA) (mul_pos_of_neg_of_neg (sub_neg.mpr he) hn)
    · apply (min_le_right _ _).trans
      by_contra! he
      exact (not_lt_of_ge hB') (mul_pos (sub_pos.mpr he) hpos)
  have hxi (i : Fin 4) : |x.val i-p.val i| ≤ B := (hxp i).trans hxpT
  refine ⟨put x hxw (fun i => (hxi i).trans (by linarith [hC i])),hleg1 K ?_,hleg2 K ?_⟩
  · intro y hwy hy
    apply put y ((le_min (min_le_left _ _) hxw).trans hwy)
    exact fun i => (hy i).trans (hxpT.trans (by linarith [hC i]))
  · intro y hwy hy
    apply put y ((le_min hxw (min_le_right _ _)).trans hwy)
    intro i
    have htri : |y.val i-p.val i| ≤ |y.val i-x.val i|+|x.val i-p.val i| := by
      simpa only [Real.dist_eq] using dist_triangle (y.val i) (x.val i) (p.val i)
    linarith only [htri,(hy i).trans hxqT,hxi i,hC i]

end
end SchwarzschildConfinement

private lemma shellGH : IsGloballyHyperbolicOn big Tbig A := by
  have orientation := time_orientation (1/2) 0 0
  constructor
  · rintro p hp ⟨γ,hγ,h0,h1⟩
    have hc := widen_arc A γ hγ
    rw [← small_domain] at hc
    have hs := (SchwarzschildConfinement.curve_estimates (1/2) 0 0 halfParams Tsmall orientation γ hc).2 0
      (left_mem_Icc.mpr zero_le_one)
    simp [h0,h1] at hs
  intro p hp q hq
  have encl := SchwarzschildConfinement.compact_enclosure (1/2) 0 0 halfParams Tsmall orientation big Tbig
    (fun γ h => widen_arc _ γ h)
  dsimp only at encl
  rw [small_domain] at encl
  obtain ⟨K,hK,hKA,hpK,hqK,conf⟩ := encl p hp q hq
  let E := causalFuture big Tbig A p ∩ causalPast big Tbig A q
  change IsCompact E
  let Rel : Set (Space × Space) := {z | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture big Tbig K z.1}
  let B : Set Space := (fun x => (p,x)) ⁻¹' closure Rel ∩ (fun x => (x,q)) ⁻¹' closure Rel
  have hB : IsClosed B := (isClosed_closure.preimage (continuous_const.prodMk continuous_id)).inter
    (isClosed_closure.preimage (continuous_id.prodMk continuous_const))
  have lim := kerrNewman_mass_shell_compact_limit 1 0 0 oneParams Tbig (time_orientation 1 0 0)
  dsimp only at lim
  rw [massDomain] at lim
  have eq : E = K ∩ B := by
    ext x
    constructor
    · intro hx
      obtain ⟨xK,px,xq⟩ := conf x hx
      exact ⟨xK,subset_closure (show (p,x) ∈ Rel from ⟨hpK,xK,px⟩),
        subset_closure (show (x,q) ∈ Rel from ⟨xK,hqK,xq⟩)⟩
    · rintro ⟨_,h1,h2⟩
      exact ⟨lim K hK hKA (show (p,x) ∈ closure Rel from h1),lim K hK hKA (show (x,q) ∈ closure Rel from h2)⟩
  rw [eq]
  exact hK.inter_right hB

theorem solution :
    ∃ T : VecField (kerrNewmanSpacetime 0), IsTimeOrientation (kerrNewmanMetricField 1 0 0) T ∧
      chronoPastSet (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) = ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ∧
      ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ⊆ chronoFutureSet (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ∧
      IsGloballyHyperbolicOn (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) := ⟨Tbig,time_orientation 1 0 0,pastA,futureA,shellGH⟩
