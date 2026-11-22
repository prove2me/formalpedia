-- Prove2me | solution 1 for NoHair.kerrNewman_exterior_timelikeAccess
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:45:03.059918+00:00
-- url     : https://prove2.me/submissions/5139cc8e-c1d1-441a-a804-78d01cd5ab6a

import Definitions.Def_NoHair_kerrNewmanTimeDirection
import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms

open NoHair NoHair.KNE Set
open scoped BigOperators Manifold ContDiff Topology

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private abbrev T (m a e : ℝ) := kerrNewmanTimeDirection m a e
private abbrev I4 := 𝓘(ℝ,E4)
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

private def coneOK (m a e Z u r : ℝ) : Prop :=
  sigma a Z r * (-(bigP a r)*sigma a Z r-2*u*a^2*(1-Z^2)+u^2) +
      massTerm m e r * (sigma a Z r+u)^2 < 0 ∧
  -(bigP a r)*sigma a Z r + (massTerm m e r/2)*(sigma a Z r+u) < 0

private theorem cone_near_zero (m a e Z r₀ L : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (hr : kerrNewmanOuterRadius m a e < r₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Icc r₀ L, ∀ u : ℝ, |u| < ε → coneOK m a e Z u r := by
  let V : Set (ℝ × ℝ) := {p | coneOK m a e Z p.1 p.2}
  have hV : IsOpen V := by
    let A (p : ℝ × ℝ) := sigma a Z p.2 * (-(bigP a p.2)*sigma a Z p.2-2*p.1*a^2*(1-Z^2)+p.1^2) +
      massTerm m e p.2 * (sigma a Z p.2+p.1)^2
    let B (p : ℝ × ℝ) := -(bigP a p.2)*sigma a Z p.2 + (massTerm m e p.2/2)*(sigma a Z p.2+p.1)
    change IsOpen ({p | A p < 0} ∩ {p | B p < 0})
    exact (isOpen_lt (show Continuous A by unfold A sigma bigP massTerm; fun_prop) continuous_const).inter
      (isOpen_lt (show Continuous B by unfold B sigma bigP massTerm; fun_prop) continuous_const)
  have hset : ({0}:Set ℝ) ×ˢ Icc r₀ L ⊆ V := by
    rintro ⟨u,r⟩ ⟨hu,hR⟩
    have hu0 : u=0 := hu
    subst u
    have hb := hr.trans_le hR.1
    change m+Real.sqrt (m^2-a^2-e^2)<r at hb
    have hsq := Real.sq_sqrt (show 0 ≤ m^2-a^2-e^2 by linarith [hp.2])
    have hm : m<r := by linarith [Real.sqrt_nonneg (m^2-a^2-e^2)]
    have hrpos := hp.1.trans hm
    have hΔ : 0<bigP a r-massTerm m e r := by
      have hmul := mul_pos (show 0<r-m-Real.sqrt (m^2-a^2-e^2) by linarith)
        (show 0<r-m+Real.sqrt (m^2-a^2-e^2) by linarith [Real.sqrt_nonneg (m^2-a^2-e^2)])
      unfold bigP massTerm
      nlinarith only [hmul,hsq]
    have hP : 0<bigP a r := by unfold bigP; positivity
    have hsig : 0<sigma a Z r := by unfold sigma; positivity
    change coneOK m a e Z 0 r
    unfold coneOK
    constructor
    · nlinarith only [mul_pos hΔ (sq_pos_of_pos hsig)]
    · nlinarith only [mul_pos (show 0<bigP a r-massTerm m e r/2 by linarith) hsig]
  obtain ⟨A,B,hA,_,h0,hB,hprod⟩ := generalized_tube_lemma isCompact_singleton isCompact_Icc hV hset
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hA 0 (h0 (by simp))
  refine ⟨ε,hε,?_⟩
  intro r hr u hu
  change (u,r) ∈ V
  exact hprod (show (u,r) ∈ A ×ˢ B from ⟨hball (by simpa [Metric.mem_ball,Real.dist_eq] using hu),hB hr⟩)

private def velocityShape (a r X Y Z u : ℝ) : E4 :=
  four (bigP a r) (-a*(a*X+r*Y)+u*X) (a*(r*X-a*Y)+u*Y) (u*Z)

private theorem metric_entries (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0)+v 1*w 1+v 2*w 2+v 3*w 3+
      ksProfile m a e x.val * (v 0 + ksNull a x.val 1*v 1+ksNull a x.val 2*v 2+ksNull a x.val 3*v 3) *
        (w 0 + ksNull a x.val 1*w 1+ksNull a x.val 2*w 2+ksNull a x.val 3*w 3) := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, Fin.sum_univ_four, ksNull_zero]
  simp [minkowski] <;> ring

private theorem velocity_timelike (m a e r t X Y Z u : ℝ) (hr : 0<r) (hrel : X^2+Y^2+Z^2=1)
    (hcone : coneOK m a e Z u r) (x : U a) (hx : x.val=oblate a r t X Y Z) :
    IsFutureTimelike (G m a e) (T m a e) x (velocityShape a r X Y Z u) := by
  let v := velocityShape a r X Y Z u
  obtain ⟨hR,hk,_⟩ := oblate_data a r t X Y Z hr hrel
  rw [← hx] at hR hk
  have hsig : 0 < sigma a Z r := by unfold sigma; positivity
  have hf : ksProfile m a e x.val * sigma a Z r = massTerm m e r := by
    rw [profile_eq m a e x.val x.property]
    unfold fA Wf sigma massTerm
    rw [hR,hk]
    change (2*m*r-e^2)*(1/(r^2+a^2*Z^2))*(r^2+a^2*Z^2) = _
    field_simp [show r^2+a^2*Z^2 ≠ 0 by positivity]
  have hK : v 0+X*v 1+Y*v 2+Z*v 3 = sigma a Z r + u := by
    change (r^2+a^2)+X*(-a*(a*X+r*Y)+u*X)+Y*(a*(r*X-a*Y)+u*Y)+Z*(u*Z)=r^2+a^2*Z^2+u
    linear_combination (u-a^2)*hrel
  have hη : -(v 0*v 0)+v 1*v 1+v 2*v 2+v 3*v 3 =
      -(bigP a r)*sigma a Z r-2*u*a^2*(1-Z^2)+u^2 := by
    change -((r^2+a^2)*(r^2+a^2))+(-a*(a*X+r*Y)+u*X)*(-a*(a*X+r*Y)+u*X)+
      (a*(r*X-a*Y)+u*Y)*(a*(r*X-a*Y)+u*Y)+(u*Z)*(u*Z) =
      -(r^2+a^2)*(r^2+a^2*Z^2)-2*u*a^2*(1-Z^2)+u^2
    linear_combination (a^2*(r^2+a^2)-2*u*a^2+u^2)*hrel
  have hV : G m a e x v v = -(bigP a r)*sigma a Z r-2*u*a^2*(1-Z^2)+u^2 +
      ksProfile m a e x.val*(sigma a Z r+u)^2 := by
    rw [metric_entries,hk]
    simp only [Matrix.cons_val]
    rw [hη,hK]
    ring
  let f := ksProfile m a e x.val
  have hTcoords : (T m a e x : E4) = four (1+f/2) (-(f/2)*X) (-(f/2)*Y) (-(f/2)*Z) := by
    unfold T kerrNewmanTimeDirection
    rw [hk]
    rfl
  have hKV : X*v 1+Y*v 2+Z*v 3=(sigma a Z r+u)-v 0 := by linarith
  have hKT : 1+f/2+X*(-(f/2)*X)+Y*(-(f/2)*Y)+Z*(-(f/2)*Z)=1 := by
    linear_combination -(f/2)*hrel
  have hVT : G m a e x v (T m a e x) = -(bigP a r) + f/2*(sigma a Z r+u) := by
    erw [metric_entries m a e x v (T m a e x), hTcoords,hk]
    change -(v 0*(1+f/2))+v 1*(-(f/2)*X)+v 2*(-(f/2)*Y)+v 3*(-(f/2)*Z)+
      f*(v 0+X*v 1+Y*v 2+Z*v 3)*(1+f/2+X*(-(f/2)*X)+Y*(-(f/2)*Y)+Z*(-(f/2)*Z))=_
    rw [hK,hKT]
    change _ = -(v 0)+f/2*(sigma a Z r+u)
    linear_combination -(f/2)*hKV
  obtain ⟨hg,ht⟩ := hcone
  constructor
  · change G m a e x v v < 0
    rw [hV]
    apply (mul_lt_mul_iff_right₀ hsig).mp
    rw [mul_zero]
    calc
      _ = sigma a Z r * (-(bigP a r)*sigma a Z r-2*u*a^2*(1-Z^2)+u^2) +
          massTerm m e r*(sigma a Z r+u)^2 := by rw [← hf]; ring
      _ < 0 := hg
  · change G m a e x v (T m a e x) < 0
    rw [hVT]
    apply (mul_lt_mul_iff_right₀ hsig).mp
    rw [mul_zero]
    calc
      _ = -(bigP a r)*sigma a Z r + (massTerm m e r/2)*(sigma a Z r+u) := by
        rw [← hf]; dsimp [f]; ring
      _ < 0 := ht

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

private theorem timelike_scale (m a e : ℝ) (x : U a) (v : E4) (N : ℝ) (hN : 0<N)
    (hv : IsFutureTimelike (G m a e) (T m a e) x v) :
    IsFutureTimelike (G m a e) (T m a e) x (N • v) := by
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  let w : E4 := T m a e x
  change A v v < 0 ∧ A v w < 0 at hv
  change A (N • v) (N • v)<0 ∧ A (N • v) w<0
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact ⟨mul_neg_of_pos_of_neg hN (mul_neg_of_pos_of_neg hN hv.1),mul_neg_of_pos_of_neg hN hv.2⟩

private theorem connecting_curve (m a e : ℝ) (p : U a) (L α b c N : ℝ)
    (hpR : kerrNewmanOuterRadius m a e < ksRadius a p.val)
    (hα : α ≠ 0) (hN : 0<N)
    (hfar : ksRadius a p.val * Real.exp (α*(c-b)) = L)
    (hsafe : ∀ s ∈ Icc (0:ℝ) 1, let r := ksRadius a p.val * Real.exp (α*(s-b))
      coneOK m a e (ksNull a p.val 3) (α*r/N) r) :
    ∃ γ : ℝ → U a, IsFutureTimelikeCurveIn (G m a e) (T m a e) univ γ ∧
      γ b = p ∧ L  ≤  spatialRadius (γ c).val := by
  let r₀ := ksRadius a p.val
  let X₀ := ksNull a p.val 1
  let Y₀ := ksNull a p.val 2
  let Z := ksNull a p.val 3
  let θ (s : ℝ) := a*N*(s-b)
  let X (s : ℝ) := X₀*Real.cos (θ s)-Y₀*Real.sin (θ s)
  let Y (s : ℝ) := X₀*Real.sin (θ s)+Y₀*Real.cos (θ s)
  let r (s : ℝ) := r₀*Real.exp (α*(s-b))
  let t (s : ℝ) := p.val 0 + N*(a^2*(s-b)+(r s^2-r₀^2)/(2*α))
  let z (s : ℝ) := oblate a (r s) (t s) (X s) (Y s) Z
  have hr₀ : 0<r₀ := p.property
  have hr (s : ℝ) : 0<r s := mul_pos hr₀ (Real.exp_pos _)
  have hk (s : ℝ) : X s^2+Y s^2+Z^2=1 := by
    have h0 : X₀^2+Y₀^2+Z^2=1 := ks_rel a p.val p.property
    dsimp only [X,Y]
    linear_combination (X₀^2+Y₀^2)*Real.sin_sq_add_cos_sq (θ s) + h0
  have hz (s : ℝ) : ksRadius a (z s) = r s :=
    (oblate_data a (r s) (t s) (X s) (Y s) Z (hr s) (hk s)).1
  let γ (s : ℝ) : U a := ⟨z s, show 0<ksRadius a (z s) by rw [hz]; exact hr s⟩
  have hsmoothInf : ContMDiff 𝓘(ℝ,ℝ) I4 ∞ γ := by
    apply (ContMDiff.subtypeVal_comp_iff (kerrNewmanSpacetime a) γ).mp
    apply contMDiff_iff_contDiff.mpr
    change ContDiff ℝ ∞ z
    unfold z oblate four
    apply PiLp.contDiff_toLp.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ t
      dsimp [t,r]; fun_prop
    · change ContDiff ℝ ∞ (fun s => r s*X s-a*Y s)
      dsimp [r,X,Y,θ]; fun_prop
    · change ContDiff ℝ ∞ (fun s => a*X s+r s*Y s)
      dsimp [r,X,Y,θ]; fun_prop
    · change ContDiff ℝ ∞ (fun s => r s*Z)
      dsimp [r]; fun_prop
  have hsmooth : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ := hsmoothInf.of_le (by simp)
  have hvel (s : ℝ) : (velocity γ s : E4) = N • velocityShape a (r s) (X s) (Y s) Z (α*r s/N) := by
    have hl (d : ℝ) : HasDerivAt (fun w : ℝ => d*(w-b)) d s := by
      simpa using ((hasDerivAt_id s).sub_const b).const_mul d
    have hr' : HasDerivAt r (α*r s) s := by
      apply (((hl α).exp).const_mul r₀).congr_deriv
      dsimp [r]; ring
    have hx' : HasDerivAt X (-(a*N)*Y s) s := by
      apply (((hl (a*N)).cos.const_mul X₀).sub ((hl (a*N)).sin.const_mul Y₀)).congr_deriv
      dsimp [Y,θ]; ring
    have hy' : HasDerivAt Y ((a*N)*X s) s := by
      apply (((hl (a*N)).sin.const_mul X₀).add ((hl (a*N)).cos.const_mul Y₀)).congr_deriv
      dsimp [X,θ]; ring
    have ht' : HasDerivAt t (N*bigP a (r s)) s := by
      apply ((((hl (a^2)).add (((hr'.pow 2).sub_const (r₀^2)).div_const (2*α))).const_mul N).const_add (p.val 0)).congr_deriv
      unfold bigP
      field_simp [hα] <;> ring
    have he := four_deriv ht' ((hr'.mul hx').sub (hy'.const_mul a))
      ((hx'.const_mul a).add (hr'.mul hy')) (hr'.mul_const Z)
    apply ambient_velocity a γ hsmooth s
    apply he.congr_deriv
    ext i
    fin_cases i <;> simp [four,velocityShape,smul_eq_mul] <;> field_simp [hN.ne'] <;> ring
  refine ⟨γ,⟨hsmooth,fun s hs => ⟨mem_univ _,?_⟩⟩,?_,?_⟩
  · have h := timelike_scale m a e (γ s) _ N hN
      (velocity_timelike m a e (r s) (t s) (X s) (Y s) Z _ (hr s) (hk s) (hsafe s hs) (γ s) rfl)
    exact hvel s ▸ h
  · apply Subtype.ext
    have hx₁ := ks_x1 a p.val p.property
    have hx₂ := ks_x2 a p.val p.property
    have hx₃ := ks_x3 a p.val p.property
    have hh : z b = oblate a r₀ (p.val 0) X₀ Y₀ Z := by
      simp [z,t,r,X,Y,θ]
    change z b = p.val
    rw [hh]
    ext i
    fin_cases i
    · rfl
    · exact hx₁.symm
    · exact hx₂.symm
    · exact hx₃.symm
  · have he := (oblate_data a (r c) (t c) (X c) (Y c) Z (hr c) (hk c)).2.2
    exact hfar ▸ he

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) (R : ℝ) :
    let A := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' exteriorRegion R
    let D := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a e
    let T := kerrNewmanTimeDirection m a e
    let g := kerrNewmanMetricField m a e
    D ⊆ chronoPastSet g T A ∩ chronoFutureSet g T A := by
  dsimp only
  intro p hpD
  let r₀ := ksRadius a p.val
  let Z := ksNull a p.val 3
  let L := max r₀ R+1
  let α := Real.log (L/r₀)
  have hr₀ : 0<r₀ := p.property
  have hL₀ : r₀<L := by dsimp [L]; linarith [le_max_left r₀ R]
  have hLR : R<L := by dsimp [L]; linarith [le_max_right r₀ R]
  have hL := hr₀.trans hL₀
  have hα : 0<α := Real.log_pos ((one_lt_div hr₀).mpr hL₀)
  have hexp : r₀*Real.exp α = L := by
    rw [show Real.exp α = L/r₀ from Real.exp_log (div_pos hL hr₀)]
    field_simp
  obtain ⟨ε,hε,hsafe⟩ := cone_near_zero m a e Z r₀ L hp hpD
  let N := (α*L+1)/ε
  have hN : 0<N := by dsimp [N]; positivity
  have hNε : N*ε=α*L+1 := by dsimp [N]; field_simp
  have safe (d t : ℝ) (hd : |d|=α) (ht : 0 ≤ t) (ht' : t ≤ α) :
      coneOK m a e Z (d*(r₀*Real.exp t)/N) (r₀*Real.exp t) := by
    have hrlo : r₀ ≤ r₀*Real.exp t := by
      have h1 : 1 ≤ Real.exp t := by simpa using Real.exp_le_exp.mpr ht
      nlinarith only [mul_le_mul_of_nonneg_left h1 hr₀.le]
    have hrhi : r₀*Real.exp t ≤ L := by
      rw [← hexp]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht') hr₀.le
    apply hsafe _ ⟨hrlo,hrhi⟩
    rw [abs_div, abs_mul d, hd, abs_of_pos hN, abs_of_pos (mul_pos hr₀ (Real.exp_pos _))]
    apply (div_lt_iff₀ hN).mpr
    linarith [mul_le_mul_of_nonneg_left hrhi hα.le, mul_comm N ε]
  obtain ⟨outgoing,houtgoing,h₀,hf₁⟩ := connecting_curve m a e p L α 0 1 N hpD hα.ne' hN
    (by simpa using hexp) (fun s hs => by
      apply safe α (α*(s-0)) (abs_of_pos hα)
      · exact mul_nonneg hα.le (by linarith [hs.1])
      · nlinarith only [mul_le_mul_of_nonneg_left hs.2 hα.le])
  obtain ⟨incoming,hincoming,h₁,hf₀⟩ := connecting_curve m a e p L (-α) 1 0 N hpD (neg_ne_zero.mpr hα.ne') hN
    (by simpa using hexp) (fun s hs => by
      apply safe (-α) ((-α)*(s-1)) (by simp [abs_of_pos hα])
      · nlinarith only [mul_le_mul_of_nonneg_left hs.2 hα.le]
      · nlinarith only [mul_nonneg hα.le hs.1])
  exact ⟨mem_iUnion₂.mpr ⟨outgoing 1,hLR.trans_le hf₁,outgoing,houtgoing,h₀,rfl⟩,
    mem_iUnion₂.mpr ⟨incoming 0,hLR.trans_le hf₀,incoming,hincoming,rfl,h₁⟩⟩
