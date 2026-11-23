-- Prove2me | solution 1 for NoHair.smooth_static_point_chart_is_topological_chart_of_completion
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:24:49.223188+00:00
-- url     : https://prove2.me/submissions/68c96a2e-136c-419a-89c8-2a9d6b744634

import Theorems.Thm_NoHair_reflected_negative_static_tails_are_completion_neighborhoods
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open Metric Manifold UniformSpace
private abbrev X := ADMPoint
theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h) (a : StaticMinusPointChart Ω N h)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0)) :
    ∃ (p : UniformSpace.Completion d.carrier) (e : OpenPartialHomeomorph ADMPoint (UniformSpace.Completion d.carrier)),
      (∀ q : d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p) ∧
      e.source = Metric.ball 0 a.radius ∧ e 0=p ∧
      (∀ y ∈ a.change.source, e y = ((d.side false).symm (a.change y) : UniformSpace.Completion d.carrier)) := by
  classical
  obtain ⟨p,np,lim,exh,tail⟩ := reflected_negative_static_tails_are_completion_neighborhoods Ω W N h c d hpositiveEnd hmass
  let inc := fun z:d.carrier => (z : Completion d.carrier)
  let B := ball (0:X) a.radius
  let τ := a.change.trans (d.side false).symm
  have comp (x:X) : τ x=(d.side false).symm (a.change x) := rfl
  have src : τ.source = B ∩ ({0}:Set X)ᶜ := by
    rw [←a.source]
    show a.change.source ∩ a.change ⁻¹' (d.side false).symm.source = a.change.source
    apply inter_eq_left.mpr
    intro x hx
    change a.change x ∈ (d.side false).target
    rw [d.target]
    exact a.inside (a.change.map_source hx)
  have ran : range inc=({p}:Set (Completion d.carrier))ᶜ := by
    ext y
    constructor
    · rintro ⟨q,rfl⟩
      exact np q
    · intro hy
      exact (exh y).resolve_left hy
  have oe : Topology.IsOpenEmbedding inc := ⟨(Completion.isUniformEmbedding_coe d.carrier).isEmbedding,by rw [ran]; exact isOpen_compl_singleton⟩
  let F := fun y : X => if y=0 then p else inc (τ y)
  have zero : F 0=p := if_pos rfl
  have off {y:X} (n:y≠0) : F y = inc (τ y) := if_neg n
  have smem {y:X} (hy:y∈B) (yn:y≠0) : y∈τ.source := by rw [src]; exact ⟨hy,yn⟩
  have cont : ContinuousOn F B := by
    intro y hy
    by_cases yn : y=0
    · subst y
      apply ContinuousAt.continuousWithinAt
      apply continuousAt_iff_punctured_nhds.mpr
      rw [zero]
      have tends : Tendsto a.change (𝓝[≠] (0:X)) (cocompact X) := by
        rw [←Metric.cobounded_eq_cocompact,←tendsto_norm_atTop_iff_cobounded]
        exact a.tendsOut
      apply (lim.comp tends).congr'
      filter_upwards [self_mem_nhdsWithin (a:=(0:X)) (s:=({0}:Set X)ᶜ)] with y hy
      exact (off hy).symm
    · have ev : F =ᶠ[𝓝 y] (fun z => inc (τ z)) := (eventually_ne_nhds yn).mono fun z hz => off hz
      exact (oe.continuous.continuousAt.comp (τ.continuousAt (smem hy yn))).congr_of_eventuallyEq ev |>.continuousWithinAt
  have inj : Set.InjOn F B := by
    intro x hx y hy eq
    by_cases xn : x=0
    · subst x
      by_contra yn
      have yn' : y≠0 := Ne.symm yn
      exact np (τ y) ((off yn').symm.trans (eq.symm.trans zero))
    · by_cases yn : y=0
      · subst y
        exact False.elim (np (τ x) ((off xn).symm.trans (eq.trans zero)))
      · rw [off xn,off yn] at eq
        exact τ.injOn (smem hx xn) (smem hy yn) (oe.isEmbedding.injective eq)
  have isOpenImage (V : Set X) (ov : IsOpen V) (vb : V⊆B) : IsOpen (F '' V) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨y,hy,rfl⟩
    by_cases yn : y=0
    · subst y
      rw [zero]
      have ev : ∀ᶠ x:X in cocompact X, a.change.symm x∈V := by
        have t := a.tendsIn (ov.mem_nhds hy)
        rwa [comap_norm_atTop,Metric.cobounded_eq_cocompact] at t
      obtain ⟨K,ck,hK⟩ := Filter.mem_cocompact.mp ev
      obtain ⟨r,hr⟩ := ck.isBounded.exists_norm_le
      obtain ⟨s,hs⟩ := a.coversInfinity
      apply Filter.mem_of_superset (tail (max r s))
      rintro z (zp|⟨x,hx,rfl⟩)
      · exact ⟨0,hy,zero.trans (show z=p from zp).symm⟩
      · have tx : x∈a.change.target := hs (show s<‖x‖ from (le_max_right r s).trans_lt hx)
        have vk := hK (show x∉K from fun k => ((le_max_left _ _).trans_lt hx).not_ge (hr x k))
        have sy := a.change.map_target tx
        rw [a.source] at sy
        refine ⟨a.change.symm x,vk,?_⟩
        rw [off sy.2,comp,a.change.right_inv tx]
    · let U := V ∩ ({0}:Set X)ᶜ
      have us : U⊆τ.source := fun x hx => smem (vb hx.1) hx.2
      have ou : IsOpen (inc '' (τ '' U)) := oe.isOpenMap _ (τ.isOpen_image_of_subset_source (ov.inter isOpen_compl_singleton) us)
      apply Filter.mem_of_superset (ou.mem_nhds (show F y∈inc '' (τ '' U) from ⟨τ y,⟨y,⟨hy,yn⟩,rfl⟩,(off yn).symm⟩))
      rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨x,hx.1,off hx.2⟩
  let pe := inj.toPartialEquiv F B
  have om : IsOpenMap (B.domRestrict F) := by
    intro U ou
    have io := isOpenImage (Subtype.val '' U) ((show IsOpen B from isOpen_ball).isOpenMap_subtype_val U ou)
      (by rintro _ ⟨⟨z,hz⟩,_,rfl⟩; exact hz)
    change IsOpen ((fun x : B => F x.val) '' U)
    simpa only [image_image,Function.comp_def] using io
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict pe cont om isOpen_ball
  refine ⟨p,e,np,rfl,zero,?_⟩
  intro y hy
  rw [a.source] at hy
  exact off hy.2
