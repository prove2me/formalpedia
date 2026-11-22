-- Prove2me | solution 1 for NoHair.schwarzschild_unit_cutoff_causality
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:25:18.373635+00:00
-- url     : https://prove2.me/submissions/646dd4cb-075d-45f4-af6e-67141f43da04

import Theorems.Thm_NoHair_kerrNewman_outerHorizon_futureTrapped
import Theorems.Thm_NoHair_kerrNewman_exterior_globallyHyperbolic
import Theorems.Thm_NoHair_kerrNewman_exterior_causalTransitivity
import Theorems.Thm_NoHair_kerrNewman_mass_shell_compact_limit
import Definitions.Def_NoHair_KerrNewmanExteriorGeodesics
import Definitions.Def_NoHair_RegularCausalJoins
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


private abbrev J := Icc (0:ℝ) 1

private theorem restrict_arc (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T K γ) (l h : ℝ) (hl : 0≤l) (hh : 0<h) (hlh : l+h≤1) :
    IsFutureCausalCurveIn (G m a e) T K (fun s => γ (l+h*s)) := by
  let φ (s : ℝ) := l+h*s
  have hφ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) 1 φ := contMDiff_iff_contDiff.mpr (by dsimp [φ]; fun_prop)
  refine ⟨hγ.1.comp hφ,?_⟩
  intro s hs
  have hi : φ s ∈ J := ⟨by dsimp [φ]; linarith [mul_nonneg hh.le hs.1],by dsimp [φ]; nlinarith only [hlh,mul_le_mul_of_nonneg_left hs.2 hh.le]⟩
  obtain ⟨hK,hn,hvv,hvT⟩ := hγ.2 (φ s) hi
  have dφ : HasDerivAt φ h s := by simpa [φ] using (((hasDerivAt_id s).const_mul h).const_add l)
  have hvel : (velocity (γ ∘ φ) s : E4) = h • (velocity γ (φ s) : E4) := by
    unfold velocity
    rw [mfderiv_comp s (hγ.1.mdifferentiableAt (by simp)) (hφ.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
    change mfderiv 𝓘(ℝ,ℝ) I4 γ (φ s) (fderiv ℝ φ s 1) = _
    rw [show fderiv ℝ φ s 1 = h from dφ.deriv]
    let L : ℝ →L[ℝ] E4 := mfderiv 𝓘(ℝ,ℝ) I4 γ (φ s)
    change L h = h • L 1
    simpa only [smul_eq_mul,mul_one] using L.map_smul h (1:ℝ)
  let A := matrixBilin (kerrNewmanMetric m a e (γ (φ s)).val)
  let v : E4 := velocity γ (φ s)
  let w : E4 := T (γ (φ s))
  change v ≠ 0 at hn
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvT
  refine ⟨hK,?_⟩
  change (velocity (γ ∘ φ) s : E4) ≠ 0 ∧ A (velocity (γ ∘ φ) s) (velocity (γ ∘ φ) s) ≤ 0 ∧
    A (velocity (γ ∘ φ) s) w<0
  rw [hvel]
  change (h • v : E4) ≠ 0 ∧ A (h • v) (h • v) ≤ 0 ∧ A (h • v) w < 0
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact ⟨smul_ne_zero hh.ne' hn,mul_nonpos_of_nonneg_of_nonpos hh.le (mul_nonpos_of_nonneg_of_nonpos hh.le hvv),
    mul_neg_of_pos_of_neg hh hvT⟩

private def composeRel {X : Type*} (A : Set (X × X)) : Set (X × X) := {z | ∃ x, (z.1,x)∈A ∧ (x,z.2)∈A}


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

private lemma widen_future {p q : Space} (h : q ∈ causalFuture big Tbig A p) :
    q ∈ causalFuture small Tsmall A p := by
  rcases h with he | ⟨γ,hγ,h0,h1⟩
  exacts [Or.inl he, Or.inr ⟨γ,widen_arc A γ hγ,h0,h1⟩]

private lemma arc_points {γ : ℝ → Space} (h : IsFutureCausalCurveIn small Tsmall A γ)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    γ t ∈ causalFuture small Tsmall A (γ 0) ∧ γ 1 ∈ causalFuture small Tsmall A (γ t) := by
  constructor
  · rcases ht.1.eq_or_lt with eq|pos
    · rw [← eq]; exact Or.inl rfl
    · have a := restrict_arc (1/2) 0 0 Tsmall A γ h 0 t le_rfl pos (by linarith only [ht.2])
      exact Or.inr ⟨_,a,by simp,by simp⟩
  · rcases ht.2.eq_or_lt with eq|lt
    · rw [eq]; exact Or.inl rfl
    · have a := restrict_arc (1/2) 0 0 Tsmall A γ h t (1-t) ht.1 (sub_pos.mpr lt) (by ring_nf; rfl)
      exact Or.inr ⟨_,a,by simp,by simp⟩

private lemma ends_in_A {p q : Space} (hp : p ∈ A) (h : q ∈ causalFuture small Tsmall A p) : q ∈ A := by
  rcases h with eq|⟨γ,hγ,_,h1⟩
  · exact (Set.mem_singleton_iff.mp eq) ▸ hp
  · exact h1 ▸ (hγ.2 1 (right_mem_Icc.mpr zero_le_one)).1

private lemma shellGH : IsGloballyHyperbolicOn big Tbig A := by
  have orientation := time_orientation (1/2) 0 0
  have hGH := kerrNewman_exterior_globallyHyperbolic (1/2) 0 0 halfParams Tsmall orientation
  rw [small_domain] at hGH
  have tra := kerrNewman_exterior_causalTransitivity (1/2) 0 0 halfParams Tsmall orientation
  dsimp only at tra
  rw [small_domain] at tra
  constructor
  · rintro p hp ⟨γ,hγ,h0,h1⟩
    exact hGH.1 p hp ⟨γ,widen_arc A γ hγ,h0,h1⟩
  intro p hp q hq
  let K := causalFuture small Tsmall A p ∩ causalPast small Tsmall A q
  let E := causalFuture big Tbig A p ∩ causalPast big Tbig A q
  change IsCompact E
  have hK : IsCompact K := hGH.2 p hp q hq
  have hKA : K ⊆ A := fun _ hx => ends_in_A hp hx.1
  by_cases empty : E.Nonempty
  · obtain ⟨x₀,hx₀⟩ := empty
    have hs := widen_future hx₀.1
    have hs' := widen_future hx₀.2
    have pq := tra p hp x₀ (ends_in_A hp hs) q hq hs hs'
    have hpK : p ∈ K := ⟨Or.inl rfl,pq⟩
    have hqK : q ∈ K := ⟨pq,Or.inl rfl⟩
    have conf {u v : Space} (hu : u ∈ A) (hv : v ∈ A)
        (pu : u ∈ causalFuture small Tsmall A p) (vq : q ∈ causalFuture small Tsmall A v)
        (uv : v ∈ causalFuture big Tbig A u) : v ∈ causalFuture big Tbig K u := by
      rcases uv with eq|⟨γ,hγ,h0,h1⟩
      · exact Or.inl eq
      · refine Or.inr ⟨γ,⟨hγ.1,?_⟩,h0,h1⟩
        intro t ht
        have hA := (hγ.2 t ht).1
        obtain ⟨first,last⟩ := arc_points (widen_arc A γ hγ) ht
        rw [h0] at first
        rw [h1] at last
        exact ⟨⟨tra p hp u hu _ hA pu first, tra _ hA v hv q hq last vq⟩,(hγ.2 t ht).2⟩
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
        have px := widen_future hx.1
        have xq := widen_future hx.2
        have xK : x ∈ K := ⟨px,xq⟩
        have xA := hKA xK
        exact ⟨xK,subset_closure (show (p,x) ∈ Rel from ⟨hpK,xK,conf hp xA (Or.inl rfl) xq hx.1⟩),
          subset_closure (show (x,q) ∈ Rel from ⟨xK,hqK,conf xA hq px (Or.inl rfl) hx.2⟩)⟩
      · rintro ⟨_,h1,h2⟩
        exact ⟨lim K hK hKA (show (p,x) ∈ closure Rel from h1),lim K hK hKA (show (x,q) ∈ closure Rel from h2)⟩
    rw [eq]
    exact hK.inter_right hB
  · rw [Set.not_nonempty_iff_eq_empty.mp empty]
    exact isCompact_empty

theorem solution :
    ∃ T : VecField (kerrNewmanSpacetime 0), IsTimeOrientation (kerrNewmanMetricField 1 0 0) T ∧
      chronoPastSet (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) = ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ∧
      ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ⊆ chronoFutureSet (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) ∧
      IsGloballyHyperbolicOn (kerrNewmanMetricField 1 0 0) T ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) := ⟨Tbig,time_orientation 1 0 0,pastA,futureA,shellGH⟩
