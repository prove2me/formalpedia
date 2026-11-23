-- Prove2me | solution 1 for NoHair.signed_lapse_and_physical_chart_on_static_metric_completion
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:44:54.964798+00:00
-- url     : https://prove2.me/submissions/1cfa8d27-65df-4200-a491-f5902a2cdb97

import Theorems.Thm_NoHair_reflected_negative_static_tails_are_completion_neighborhoods
import Theorems.Thm_NoHair_compact_complement_surviving_end_of_completed_static_double
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
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0))
    (p : UniformSpace.Completion d.carrier) (off : ∀ q:d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p) :
    ∃ (L : C(UniformSpace.Completion d.carrier, ℝ)) (f : OpenPartialHomeomorph (UniformSpace.Completion d.carrier) ADMPoint),
      (∀ q : d.carrier, L (q : UniformSpace.Completion d.carrier) = d.lapse q) ∧
      L p = -1 ∧
      (∀ z : UniformSpace.Completion d.carrier, z ≠ p → -1 < L z) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : Set (UniformSpace.Completion d.carrier), IsCompact K ∧ ∀ z ∉ K, |L z - 1| ≤ ε) ∧
      (∃ z : UniformSpace.Completion d.carrier, z ≠ p ∧ L z = 0) ∧
      f.source = {z | z ≠ p ∧ 0 < L z} ∧
      f.target = Ω ∧
      (∀ x ∈ Ω, f.symm x = ((d.side true).symm x : UniformSpace.Completion d.carrier)) ∧
      (∀ z ∈ f.source, N (f z) = L z) := by
  classical
  obtain ⟨p',_,_,all',tail'⟩ := reflected_negative_static_tails_are_completion_neighborhoods Ω W N h c d hpositiveEnd hmass
  have same : p=p' := (all' p).resolve_right (fun ⟨q,hq⟩ => off q hq)
  rw [←same] at all' tail'
  let inc := fun z : d.carrier => (z : Completion d.carrier)
  have ran : range inc = ({p} : Set (Completion d.carrier))ᶜ := by
    ext w
    exact ⟨fun ⟨q,hq⟩ eq => off q (hq.trans eq),fun h => (all' w).resolve_left h⟩
  have oe : Topology.IsOpenEmbedding inc := ⟨(Completion.isUniformEmbedding_coe d.carrier).isEmbedding,
    by rw [ran]; exact isOpen_compl_singleton⟩
  let F := Function.extend inc d.lapse (fun _ => (-1:ℝ))
  have old (q:d.carrier) : F (inc q)=d.lapse q := oe.injective.extend_apply _ _ _
  have fp : F p = -1 := Function.extend_apply' _ _ _ (fun ⟨q,hq⟩ => off q hq)
  obtain ⟨B,hB⟩ := c.compactComplement.isBounded.exists_norm_le
  have inside {x:X} (hx:B<‖x‖) : x∈Ω := by by_contra hn; exact hx.not_ge (hB x hn)
  have cap (b:Bool) (x:X) (hx : x∈Ω) :
      F (inc ((d.side b).symm x)) = (if b then 1 else -1) * N x := by
    rw [old,d.inverseOnSide b x hx,d.signed]
  have far (ε:ℝ) (ep:0<ε) : ∃ A:ℝ, ∀ x:X, A<‖x‖ → |N x-1|<ε := by
    obtain ⟨R,C,_,_,h₀⟩ := c.falloff 0
    have decay : Tendsto (fun x:X => N x-1) (cocompact X) (𝓝 0) := by
      apply squeeze_zero_norm' (a:=fun x:X => C/‖x‖)
      · filter_upwards [(tendsto_norm_cocompact_atTop (E:=X)).eventually_gt_atTop R] with x hx
        simpa only [norm_iteratedFDeriv_zero,Nat.zero_add,pow_one] using (h₀ x hx).1
      · exact tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop
    have ev := (Metric.tendsto_nhds.mp decay) ε ep
    obtain ⟨K,ck,hK⟩ := Filter.mem_cocompact.mp ev
    obtain ⟨s,hs⟩ := ck.isBounded.exists_norm_le
    exact ⟨s, fun x hx => by simpa only [Set.mem_setOf_eq,Real.dist_eq,sub_zero] using hK (show x ∉ K from fun h => hx.not_ge (hs x h))⟩
  have cf : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro z
    obtain atP|⟨q,rfl⟩ := all' z
    · subst z
      change Tendsto F _ (𝓝 (F p))
      rw [fp]
      apply Metric.tendsto_nhds.mpr
      intro ε ep
      obtain ⟨A,est⟩ := far ε ep
      filter_upwards [tail' (max A B)] with y hy
      obtain rfl|⟨x,hx,rfl⟩ := hy
      · simpa [fp] using ep
      · have ox := inside ((le_max_right A B).trans_lt hx)
        have eq : F (inc ((d.side false).symm x)) = - N x := by simpa using cap false x ox
        change dist (F (inc ((d.side false).symm x))) (-1) < ε
        rw [eq,dist_neg_neg,Real.dist_eq]
        exact est x ((le_max_left A B).trans_lt hx)
    · apply oe.continuousAt_iff.mp
      have eq : F ∘ inc = d.lapse := funext old
      rw [eq]
      exact d.smoothLapse.continuous.continuousAt
  let L : C(Completion d.carrier,ℝ) := ⟨F,cf⟩
  let f := (d.side true).lift_openEmbedding oe
  have src : f.source = {z | z ≠ p ∧ 0 < L z} := by
    rw [show f.source=inc '' (d.side true).source from rfl,d.source]
    ext z
    constructor
    · rintro ⟨q,hq,rfl⟩
      refine ⟨off q,?_⟩
      change 0<F (inc q)
      rw [old]
      simpa using hq
    · rintro ⟨ne,gt⟩
      obtain ⟨q,rfl⟩ := (all' z).resolve_left ne
      refine ⟨q,?_,rfl⟩
      change 0<F (inc q) at gt
      rw [old] at gt
      simpa using gt
  refine ⟨L,f,old,fp,?_,?_,?_,src,d.target true,fun x hx => rfl,?_⟩
  · intro z ne
    obtain ⟨q,rfl⟩ := (all' z).resolve_left ne
    change -1<F (inc q)
    rw [old]; exact d.lower q
  · intro ε ep
    obtain ⟨A,est⟩ := far ε ep
    obtain ⟨R,_,K⟩ := compact_complement_surviving_end_of_completed_static_double Ω W N h c d hpositiveEnd hmass
    let s := max R (max A B)
    refine ⟨_,K s (le_max_left _ _),?_⟩
    intro z hz
    obtain ⟨x,hx,rfl⟩ := not_not.mp hz
    have ab := (le_max_right R (max A B)).trans_lt (show s<‖x‖ from hx)
    change |F (inc ((d.side true).symm x))-1|≤ε
    rw [cap true x (inside ((le_max_right A B).trans_lt ab))]
    simpa using (est x ((le_max_left A B).trans_lt ab)).le
  · obtain ⟨x,hx⟩ := c.hasBoundary
    let q := d.inc true ⟨x,frontier_subset_closure hx⟩
    refine ⟨inc q,off q,?_⟩
    change F (inc q)=0
    rw [old]
    simp only [q,d.signed,ite_true,Bool.true_eq,one_mul,(c.regularLevel x hx).1]
  · rintro z hz
    change z ∈ inc '' (d.side true).source at hz
    obtain ⟨q,hq,rfl⟩ := hz
    have eq : f (inc q) = (d.side true) q := (d.side true).lift_openEmbedding_apply oe
    have ox := (d.side true).map_source hq
    rw [d.target] at ox
    have rep := d.inverseOnSide true ((d.side true) q) ox
    rw [(d.side true).left_inv hq] at rep
    change N (f (inc q)) = F (inc q)
    rw [eq,old]
    calc N ((d.side true) q) = d.lapse (d.inc true ⟨(d.side true) q,subset_closure ox⟩) := by rw [d.signed]; simp
         _ = d.lapse q := congrArg d.lapse rep.symm
