-- Prove2me | solution 1 for NoHair.chronoFuture_transitive
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:30:06.916914+00:00
-- url     : https://prove2.me/submissions/2fd437cd-1173-4261-a0de-859701a396e7

import Theorems.Thm_NoHair_future_timelike_cones_in_chart

open NoHair Set Filter
open scoped ContDiff Manifold BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
private abbrev I1 := 𝓘(ℝ,ℝ)
private abbrev I4 := 𝓘(ℝ,E4)
private def ramp (t : ℝ) := (max t 0)^2
private def before (d t : ℝ) := 1-d^2*ramp (1-t)
private def after (d t : ℝ) := d^2*ramp t

private theorem ramp_jet (t : ℝ) : HasDerivAt ramp (2*max t 0) t := by
  rcases lt_trichotomy t 0 with h|rfl|h
  · rw [max_eq_right h.le,mul_zero]
    apply (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds h] with z hz
    simp [ramp,max_eq_right hz.le]
  · simp only [max_self,mul_zero]
    apply hasDerivWithinAt_univ.mp
    rw [←Iic_union_Ici (a := (0:ℝ))]
    apply HasDerivWithinAt.union
    · apply (hasDerivAt_const (0:ℝ) (0:ℝ)).hasDerivWithinAt.congr_of_mem _ (show (0:ℝ) ∈ Iic 0 by simp)
      intro z hz
      change z ≤ 0 at hz
      simp [ramp,max_eq_right hz]
    · have hp : HasDerivAt (fun z : ℝ => z^2) 0 0 := by simpa using hasDerivAt_pow 2 (0:ℝ)
      apply hp.hasDerivWithinAt.congr_of_mem _ (show (0:ℝ) ∈ Ici 0 by simp)
      intro z hz
      change 0 ≤ z at hz
      simp [ramp,max_eq_left hz]
  · rw [max_eq_left h.le]
    have hp : HasDerivAt (fun z : ℝ => z^2) (2*t) t := by simpa using hasDerivAt_pow 2 t
    apply hp.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds h] with z hz
    simp [ramp,max_eq_left hz.le]

private theorem ramp_c1 : ContDiff ℝ 1 ramp := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (ramp_jet t).differentiableAt,?_⟩
  simp_rw [show deriv ramp = fun t => 2*max t 0 from funext (fun t => (ramp_jet t).deriv)]
  fun_prop

private theorem before_jet (d t : ℝ) : HasDerivAt (before d) (2*d^2*max (1-t) 0) t := by
  have h : HasDerivAt (fun z : ℝ => 1-z) (-1) t := by simpa using (hasDerivAt_id t).const_sub 1
  exact ((((ramp_jet (1-t)).comp t h).const_mul (d^2)).const_sub 1).congr_deriv (by ring)
private theorem after_jet (d t : ℝ) : HasDerivAt (after d) (2*d^2*max t 0) t :=
  ((ramp_jet t).const_mul (d^2)).congr_deriv (by ring)
private theorem before_c1 (d : ℝ) : ContDiff ℝ 1 (before d) := by
  unfold before
  have hr := ramp_c1
  fun_prop
private theorem after_c1 (d : ℝ) : ContDiff ℝ 1 (after d) := by
  unfold after
  have hr := ramp_c1
  fun_prop

private def middlePos (P Q : ℝ → E4) (p : E4) (d t : ℝ) :=
  P (before d t) + Q (after d t) - p
private def middleDir (P Q : ℝ → E4) (d t : ℝ) :=
  (1-t) • deriv P (before d t) + t • deriv Q (after d t)
private abbrev J := Icc (0:ℝ) 1

private theorem choose_window (P Q : ℝ → E4) (p : E4) (hP : ContDiffAt ℝ 1 P 1)
    (hQ : ContDiffAt ℝ 1 Q 0) (h1 : P 1 = p) (h0 : Q 0 = p)
    (U V : Set ℝ) (hU : U ∈ 𝓝 (1:ℝ)) (hV : V ∈ 𝓝 (0:ℝ))
    (K : Set (E4 × E4)) (op : IsOpen K) (cv : Convex ℝ {w : E4 | (p,w) ∈ K})
    (hPK : (p,deriv P 1) ∈ K) (hQK : (p,deriv Q 0) ∈ K) :
    ∃ d : ℝ, 0<d ∧ d<1/2 ∧ ∀ u ∈ J, before d u ∈ U ∧ after d u ∈ V ∧
      (middlePos P Q p d u,middleDir P Q d u) ∈ K := by
  have small : ∀ᶠ d : ℝ in 𝓝 0, ∀ u ∈ J, before d u ∈ U ∧ after d u ∈ V ∧
      (middlePos P Q p d u,middleDir P Q d u) ∈ K := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    let z : ℝ × ℝ := (0,u)
    have cb : ContinuousAt (fun v : ℝ × ℝ => before v.1 v.2) z := by unfold before ramp; fun_prop
    have ca : ContinuousAt (fun v : ℝ × ℝ => after v.1 v.2) z := by unfold after ramp; fun_prop
    have hb : before z.1 z.2 = 1 := by simp [before,z]
    have ha : after z.1 z.2 = 0 := by simp [after,z]
    have pcont : ContinuousAt P (before z.1 z.2) := hb.symm ▸ hP.continuousAt
    have qcont : ContinuousAt Q (after z.1 z.2) := ha.symm ▸ hQ.continuousAt
    have pdcont : ContinuousAt (deriv P) (before z.1 z.2) := by
      rw [hb]
      exact (hP.derivWithin (m := 0) (by norm_num)).continuousAt
    have qdcont : ContinuousAt (deriv Q) (after z.1 z.2) := by
      rw [ha]
      exact (hQ.derivWithin (m := 0) (by norm_num)).continuousAt
    have cxy : ContinuousAt (fun v : ℝ × ℝ => (middlePos P Q p v.1 v.2,middleDir P Q v.1 v.2)) z := by
      apply ContinuousAt.prodMk
      · exact ((pcont.comp (f := fun v : ℝ × ℝ => before v.1 v.2) cb).add
          (qcont.comp (f := fun v : ℝ × ℝ => after v.1 v.2) ca)).sub continuousAt_const
      · exact ((continuousAt_const.sub continuous_snd.continuousAt).smul
          (pdcont.comp (f := fun v : ℝ × ℝ => before v.1 v.2) cb)).add
          (continuous_snd.continuousAt.smul (qdcont.comp (f := fun v : ℝ × ℝ => after v.1 v.2) ca))
    have hm := cv hPK hQK (sub_nonneg.mpr hu.2) hu.1 (show 1-u+u=1 by ring)
    change (p,(1-u) • deriv P 1 + u • deriv Q 0) ∈ K at hm
    have hk : (middlePos P Q p z.1 z.2,middleDir P Q z.1 z.2) ∈ K := by
      simpa [middlePos,middleDir,z,before,after,h1,h0] using hm
    have eu : ∀ᶠ s : ℝ × ℝ in 𝓝 z, before s.1 s.2 ∈ U := cb (show U ∈ 𝓝 (before z.1 z.2) by rwa [hb])
    have ev : ∀ᶠ s : ℝ × ℝ in 𝓝 z, after s.1 s.2 ∈ V := ca (show V ∈ 𝓝 (after z.1 z.2) by rwa [ha])
    have ek : ∀ᶠ s : ℝ × ℝ in 𝓝 z, (middlePos P Q p s.1 s.2,middleDir P Q s.1 s.2) ∈ K :=
      cxy (op.mem_nhds hk)
    exact eu.and (ev.and ek)
  obtain ⟨ε,hε,hs⟩ := Metric.eventually_nhds_iff.mp small
  let d := min (ε/2) (1/4)
  have hd : 0<d := lt_min (by linarith) (by norm_num)
  have he : dist d 0 < ε := by
    rw [Real.dist_eq,sub_zero,abs_of_pos hd]
    have hh : d ≤ ε/2 := min_le_left _ _
    linarith
  exact ⟨d,hd,lt_of_le_of_lt (min_le_right _ _) (by norm_num),hs he⟩

private theorem middle_jet (P Q : ℝ → E4) (p : E4) (d u : ℝ) (hu : u ∈ J)
    (hP : DifferentiableAt ℝ P (before d u)) (hQ : DifferentiableAt ℝ Q (after d u)) :
    HasDerivAt (middlePos P Q p d) ((2*d^2) • middleDir P Q d u) u := by
  have left := hP.hasDerivAt.scomp u (before_jet d u)
  have right := hQ.hasDerivAt.scomp u (after_jet d u)
  apply ((left.add right).sub_const p).congr_deriv
  simp only [middleDir,max_eq_left (sub_nonneg.mpr hu.2),max_eq_left hu.1,smul_add,smul_smul]

section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M] [IsManifold I4 ∞ M]
variable {g : BilinField M} {T : VecField M}

private theorem scale_future {x : M} {v : TangentSpace I4 x} {a : ℝ}
    (ha : 0 < a) (hv : IsFutureTimelike g T x v) : IsFutureTimelike g T x (a • v) := by
  let G : E4 →L[ℝ] E4 →L[ℝ] ℝ := g x
  change G (a • v) (a • v) < 0 ∧ G (a • v) (T x) < 0
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact ⟨mul_neg_of_pos_of_neg ha (mul_neg_of_pos_of_neg ha hv.1),mul_neg_of_pos_of_neg ha hv.2⟩

private theorem velocity_reparam {γ : ℝ → M} {f : ℝ → ℝ} {t d : ℝ}
    (hγ : MDifferentiableAt I1 I4 γ (f t)) (hf : HasDerivAt f d t) :
    velocity (γ ∘ f) t = d • velocity γ (f t) := by
  have hd : (mfderiv I1 I1 f t : ℝ →L[ℝ] ℝ) 1 = d := by rw [mfderiv_eq_fderiv]; exact hf.deriv
  unfold velocity
  rw [mfderiv_comp (I' := I1) t hγ hf.differentiableAt.mdifferentiableAt]
  change (mfderiv I1 I4 γ (f t) : ℝ →L[ℝ] E4) ((mfderiv I1 I1 f t) 1) = _
  rw [hd]
  simpa only [smul_eq_mul,mul_one] using (mfderiv I1 I4 γ (f t)).map_smul d (1:ℝ)

private theorem velocity_chart {ψ : E4 → M} {c : ℝ → E4} {u : ℝ}
    (hψ : MDifferentiableAt I4 I4 ψ (c u)) (hc : DifferentiableAt ℝ c u) :
    velocity (ψ ∘ c) u = (mfderiv I4 I4 ψ (c u) : E4 →L[ℝ] E4) (deriv c u) := by
  unfold velocity
  rw [mfderiv_comp (I' := I4) u hψ hc.mdifferentiableAt]
  change (mfderiv I4 I4 ψ (c u) : E4 →L[ℝ] E4) ((mfderiv I1 I4 c u) 1) = _
  rw [mfderiv_eq_fderiv]
  rfl

private theorem oriented_window (γ : ℝ → M) (hγ : ContMDiff I1 I4 1 γ) (l r : ℝ) (hlr : l<r)
    (h : ∀ t ∈ Icc l r, IsFutureTimelike g T (γ t) (velocity γ t)) : γ r ∈ chronoFuture g T univ (γ l) := by
  let f := fun t : ℝ => l+(r-l)*t
  have hd (t : ℝ) : HasDerivAt f (r-l) t := by simpa [f] using (((hasDerivAt_id t).const_mul (r-l)).const_add l)
  have hf : ContMDiff I1 I1 1 f := (show ContDiff ℝ 1 f by dsimp [f]; fun_prop).contMDiff
  refine ⟨γ ∘ f,⟨hγ.comp hf,?_⟩,by simp [f],by simp [f]⟩
  intro t ht
  have hft : f t ∈ Icc l r := by
    change l ≤ l+(r-l)*t ∧ l+(r-l)*t ≤ r
    constructor <;> nlinarith only [mul_nonneg (sub_nonneg.mpr hlr.le) ht.1,
      mul_nonneg (sub_nonneg.mpr hlr.le) (sub_nonneg.mpr ht.2)]
  refine ⟨mem_univ _,?_⟩
  rw [velocity_reparam ((hγ (f t)).mdifferentiableAt (by simp)) (hd t)]
  exact scale_future (sub_pos.mpr hlr) (h _ hft)

private theorem coord_facts (e : OpenPartialHomeomorph M E4) (de : ContMDiffOn I4 I4 ∞ e e.source)
    (ds : ContMDiffOn I4 I4 ∞ e.symm e.target) (γ : ℝ → M) (hγ : ContMDiff I1 I4 1 γ)
    (s : ℝ) (hy : γ s ∈ e.source) :
    ContDiffAt ℝ 1 (e ∘ γ) s ∧
    velocity γ s = (mfderiv I4 I4 e.symm (e (γ s)) : E4 →L[ℝ] E4) (deriv (e ∘ γ) s) := by
  have hc : ContDiffAt ℝ 1 (e ∘ γ) s :=
    (((de _ hy).contMDiffAt (e.open_source.mem_nhds hy)).of_le (by simp) |>.comp s (hγ s)).contDiffAt
  have hgerm : e.symm ∘ (e ∘ γ) =ᶠ[𝓝 s] γ := by
    filter_upwards [hγ.continuous.continuousAt (e.open_source.mem_nhds hy)] with t ht
    exact e.left_inv ht
  have he := velocity_chart
    (((ds _ (e.map_source hy)).contMDiffAt (e.open_target.mem_nhds (e.map_source hy))).mdifferentiableAt (by simp))
    (hc.differentiableAt (by simp))
  refine ⟨hc,?_⟩
  unfold velocity at he ⊢
  rwa [hgerm.mfderiv_eq] at he
end Manifold

theorem solution {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ,E4) ∞ M] (g : BilinField M) (T : VecField M)
    (hg : IsLorentzian g) (hs : IsSmoothBilinField g) (hT : IsTimeOrientation g T)
    {x y z : M} (hxy : y ∈ chronoFuture g T univ x) (hyz : z ∈ chronoFuture g T univ y) :
    z ∈ chronoFuture g T univ x := by
  obtain ⟨α,hα,hx,hy⟩ := hxy
  obtain ⟨β,hβ,hy',hz⟩ := hyz
  let e := chartAt E4 y
  let P := e ∘ α
  let Q := e ∘ β
  let p := e y
  let L : E4 → E4 →L[ℝ] E4 := fun z => mfderiv I4 I4 e.symm z
  let K := {z : E4 × E4 | z.1 ∈ e.target ∧ IsFutureTimelike g T (e.symm z.1) (L z.1 z.2)}
  have de : ContMDiffOn I4 I4 ∞ e e.source := contMDiffOn_chart
  have ds : ContMDiffOn I4 I4 ∞ e.symm e.target := contMDiffOn_chart_symm
  have hys : y ∈ e.source := mem_chart_source _ _
  have hp : p ∈ e.target := e.map_source hys
  have hP1 : P 1 = p := congrArg e hy
  have hQ0 : Q 0 = p := congrArg e hy'
  have hα1 : α 1 ∈ e.source := hy.symm ▸ hys
  have hβ0 : β 0 ∈ e.source := hy'.symm ▸ hys
  have hcfP := coord_facts e de ds α hα.1 1 hα1
  have hcfQ := coord_facts e de ds β hβ.1 0 hβ0
  obtain ⟨hK,hconv⟩ := future_timelike_cones_in_chart g T hg hs hT y
  have endP : (p,deriv P 1) ∈ K := by
    refine ⟨hp,?_⟩
    change IsFutureTimelike g T (e.symm p) (L p (deriv P 1))
    have he : velocity α 1 = L (P 1) (deriv P 1) := hcfP.2
    rw [← hP1,show e.symm (P 1) = α 1 from e.left_inv hα1,←he]
    exact (hα.2 1 (by simp)).2
  have endQ : (p,deriv Q 0) ∈ K := by
    refine ⟨hp,?_⟩
    change IsFutureTimelike g T (e.symm p) (L p (deriv Q 0))
    have he : velocity β 0 = L (Q 0) (deriv Q 0) := hcfQ.2
    rw [←hQ0,show e.symm (Q 0) = β 0 from e.left_inv hβ0,←he]
    exact (hβ.2 0 (by simp)).2
  obtain ⟨d,hd,hhalf,H⟩ := choose_window P Q p hcfP.1 hcfQ.1 hP1 hQ0
    (α ⁻¹' e.source) (β ⁻¹' e.source)
    (hα.1.continuous.continuousAt (e.open_source.mem_nhds hα1))
    (hβ.1.continuous.continuousAt (e.open_source.mem_nhds hβ0)) K hK (hconv p hp) endP endQ
  let Z := middlePos P Q p d
  let η := fun t : ℝ => if t < 0 then α (before d t) else if 1 < t then β (after d t) else e.symm (Z t)
  have left_eq (t : ℝ) (ht : t<0) : η =ᶠ[𝓝 t] α ∘ before d := by
    filter_upwards [eventually_lt_nhds ht] with s hs using if_pos hs
  have right_eq (t : ℝ) (ht : 1<t) : η =ᶠ[𝓝 t] β ∘ after d := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    simp [η,show ¬ s<0 by linarith,hs]
  have mid_eq (t : ℝ) (ht : t ∈ J) : η =ᶠ[𝓝 t] e.symm ∘ Z := by
    have ha : Continuous (α ∘ before d) := hα.1.continuous.comp (before_c1 d).continuous
    have hb : Continuous (β ∘ after d) := hβ.1.continuous.comp (after_c1 d).continuous
    filter_upwards [ha.continuousAt (e.open_source.mem_nhds (H t ht).1),
      hb.continuousAt (e.open_source.mem_nhds (H t ht).2.1)] with s has hbs
    by_cases hl : s<0
    · have hpost : after d s = 0 := by simp [after,ramp,max_eq_right hl.le]
      simpa [η,hl,Z,middlePos,hpost,hQ0,P] using (e.left_inv has).symm
    by_cases hr : 1<s
    · have hpre : before d s = 1 := by simp [before,ramp,max_eq_right (sub_nonpos.mpr hr.le)]
      simpa [η,hl,hr,Z,middlePos,hpre,hP1,Q,add_sub_cancel_left] using (e.left_inv hbs).symm
    · simp [η,hl,hr]
  have middle_c1 (t : ℝ) (ht : t ∈ J) : ContDiffAt ℝ 1 Z t := by
    have hP := (coord_facts e de ds α hα.1 (before d t) (H t ht).1).1
    have hQ := (coord_facts e de ds β hβ.1 (after d t) (H t ht).2.1).1
    exact ((hP.comp t (before_c1 d).contDiffAt).add (hQ.comp t (after_c1 d).contDiffAt)).sub contDiffAt_const
  have hη : ContMDiff I1 I4 1 η := by
    intro t
    by_cases hl : t<0
    · exact ((hα.1.comp (before_c1 d).contMDiff) t).congr_of_eventuallyEq (left_eq t hl)
    by_cases hr : 1<t
    · exact ((hβ.1.comp (after_c1 d).contMDiff) t).congr_of_eventuallyEq (right_eq t hr)
    have ht : t∈J := ⟨le_of_not_gt hl,le_of_not_gt hr⟩
    have hzT : Z t ∈ e.target := (H t ht).2.2.1
    exact (((ds _ hzT).contMDiffAt (e.open_target.mem_nhds hzT)).of_le (by simp)
      |>.comp t (middle_c1 t ht).contMDiffAt).congr_of_eventuallyEq (mid_eq t ht)
  let r := d⁻¹
  let l := 1-r
  have hr : 1<r := by
    change 1<d⁻¹
    rw [inv_eq_one_div,lt_div_iff₀ hd]
    linarith
  have hl : l<0 := sub_neg.mpr hr
  have hlr : l<r := by linarith
  have hbl : before d l = 0 := by
    have he : 1-l=r := by dsimp [l]; ring
    rw [before,he,ramp,max_eq_left (by linarith : 0≤r)]
    dsimp [r]; field_simp [hd.ne'] <;> ring
  have har : after d r = 1 := by
    rw [after,ramp,max_eq_left (by linarith : 0≤r)]
    dsimp [r]; field_simp [hd.ne']
  have hbmono : Monotone (before d) := monotone_of_deriv_nonneg
    (fun t => (before_jet d t).differentiableAt) (fun t => by rw [(before_jet d t).deriv]; positivity)
  have hamono : Monotone (after d) := monotone_of_deriv_nonneg
    (fun t => (after_jet d t).differentiableAt) (fun t => by rw [(after_jet d t).deriv]; positivity)
  have hgood (t : ℝ) (ht : t∈Icc l r) : IsFutureTimelike g T (η t) (velocity η t) := by
    by_cases hleft : t<0
    · have he := left_eq t hleft
      have hpar : before d t ∈ J := by
        constructor
        · rw [←hbl]; exact hbmono ht.1
        · unfold before ramp
          exact sub_le_self _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have hpos : 0<2*d^2*max (1-t) 0 := by
        rw [max_eq_left (by linarith : 0≤1-t)]
        exact mul_pos (by positivity) (by linarith)
      have he' : velocity η t = velocity (α ∘ before d) t := congrArg (fun A : ℝ →L[ℝ] E4 => A 1) he.mfderiv_eq
      rw [he',velocity_reparam ((hα.1 _).mdifferentiableAt (by simp)) (before_jet d t),he.eq_of_nhds]
      exact scale_future hpos (hα.2 _ hpar).2
    by_cases hright : 1<t
    · have he := right_eq t hright
      have hpar : after d t ∈ J := by
        constructor
        · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
        · rw [←har]; exact hamono ht.2
      have hpos : 0<2*d^2*max t 0 := by
        rw [max_eq_left (by linarith : 0≤t)]
        exact mul_pos (by positivity) (by linarith)
      have he' : velocity η t = velocity (β ∘ after d) t := congrArg (fun A : ℝ →L[ℝ] E4 => A 1) he.mfderiv_eq
      rw [he',velocity_reparam ((hβ.1 _).mdifferentiableAt (by simp)) (after_jet d t),he.eq_of_nhds]
      exact scale_future hpos (hβ.2 _ hpar).2
    have hj : t∈J := ⟨le_of_not_gt hleft,le_of_not_gt hright⟩
    have hm : (Z t,middleDir P Q d t) ∈ K := (H t hj).2.2
    have hP := (coord_facts e de ds α hα.1 (before d t) (H t hj).1).1
    have hQ := (coord_facts e de ds β hβ.1 (after d t) (H t hj).2.1).1
    have hjet := middle_jet P Q p d t hj (hP.differentiableAt (by simp)) (hQ.differentiableAt (by simp))
    have he := mid_eq t hj
    have he' : velocity η t = velocity (e.symm ∘ Z) t := congrArg (fun A : ℝ →L[ℝ] E4 => A 1) he.mfderiv_eq
    have hds := ((ds _ hm.1).contMDiffAt (e.open_target.mem_nhds hm.1)).mdifferentiableAt (by simp)
    rw [he',velocity_chart hds hjet.differentiableAt,he.eq_of_nhds]
    change IsFutureTimelike g T (e.symm (Z t)) (L (Z t) (deriv (middlePos P Q p d) t))
    rw [hjet.deriv,map_smul]
    exact scale_future (by positivity) hm.2
  have path := oriented_window η hη l r hlr hgood
  have hηl : η l=x := by simpa [η,hl,hbl] using hx
  have hηr : η r=z := by simpa [η,hr,show ¬r<0 by linarith,har] using hz
  rwa [hηl,hηr] at path
