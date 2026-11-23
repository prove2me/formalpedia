-- Prove2me | solution 1 for NoHair.compact_complement_surviving_end_of_completed_static_double
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:28:07.611968+00:00
-- url     : https://prove2.me/submissions/9e1d0769-6967-4c16-9e1a-3495ce12aec2

import Theorems.Thm_NoHair_reflected_static_double_metric_completion_one_point
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open Metric UniformSpace
private abbrev X := ADMPoint
theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0)) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R ≤ t → IsCompact
      (((fun x : ADMPoint => ((d.side true).symm x : UniformSpace.Completion d.carrier)) '' {x : ADMPoint | t < ‖x‖})ᶜ) := by
  classical
  obtain ⟨p,newp,lim,all⟩ := reflected_static_double_metric_completion_one_point Ω W N h c d hpositiveEnd hmass
  let inc := fun q : d.carrier => (q : Completion d.carrier)
  have ci : Continuous inc := Completion.continuous_coe (α:=d.carrier)
  have ran : range inc=({p}:Set (Completion d.carrier))ᶜ := by
    ext w
    constructor
    · rintro ⟨q,rfl⟩; exact newp q
    · exact (all w).resolve_left
  have oe : Topology.IsOpenEmbedding inc := ⟨(Completion.isUniformEmbedding_coe d.carrier).isEmbedding,
    by rw [ran]; exact isOpen_compl_singleton⟩
  obtain ⟨A,hA⟩ := c.compactComplement.isBounded.exists_norm_le
  have far {x:X} (hx:A<‖x‖) : x∈Ω := by by_contra hn; exact hx.not_ge (hA x hn)
  let f := fun x : ↥(closure Ω) => inc (d.inc false x)
  have cf : Continuous f := ci.comp (d.inc false).continuous
  have emb := (isClosed_closure (s:=Ω)).isClosedEmbedding_subtypeVal
  have prop : Tendsto (Subtype.val : ↥(closure Ω) → X) (cocompact _) (cocompact X) := emb.tendsto_cocompact
  have cneg : IsCompact (insert p (range f)) := by
    apply Tendsto.isCompact_insert_range_of_cocompact _ cf
    apply (lim.comp prop).congr'
    filter_upwards [((tendsto_norm_cocompact_atTop (E:=X)).comp prop).eventually_gt_atTop A] with x hx
    exact congrArg inc (d.inverseOnSide false _ (far hx))
  refine ⟨max A 1,(zero_lt_one.trans_le (le_max_right _ _)),?_⟩
  intro s hs
  let V := {x : X | s<‖x‖}
  let e := (d.side true).symm
  have ins : V⊆e.source := by
    intro x hx
    change x∈(d.side true).target
    rw [d.target]
    exact far (((le_max_left A 1).trans hs).trans_lt hx)
  have op : IsOpen ((fun x:X => inc (e x)) '' V) := by
    rw [show (fun x:X => inc (e x)) = inc ∘ e from rfl,Set.image_comp]
    exact oe.isOpenMap _ (e.isOpen_image_of_subset_source (isOpen_lt continuous_const continuous_norm) ins)
  let K := (Subtype.val : ↥(closure Ω) → X) ⁻¹' closedBall 0 s
  have cpos := (emb.isCompact_preimage (isCompact_closedBall (0:X) s)).image (ci.comp (d.inc true).continuous)
  apply (cneg.union cpos).of_isClosed_subset op.isClosed_compl
  intro w hw
  obtain rfl|⟨q,rfl⟩ := all w
  · exact Or.inl (Or.inl rfl)
  obtain ⟨b,x,rfl⟩ := d.covers q
  cases b
  · exact Or.inl (Or.inr ⟨x,rfl⟩)
  · apply Or.inr
    refine ⟨x,?_,rfl⟩
    change (x:X)∈closedBall 0 s
    rw [mem_closedBall_zero_iff]
    by_contra above
    have sx := lt_of_not_ge above
    apply hw
    have ox := far (((le_max_left A 1).trans hs).trans_lt sx)
    exact ⟨x.val,sx,congrArg inc (d.inverseOnSide true x.val ox)⟩
