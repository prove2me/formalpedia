-- Prove2me | solution 1 for OAI.CannonEmbeddedArc.Arc.DevelopedFaces.hull_geometry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:55:38.691546+00:00
-- url     : https://prove2.me/submissions/eb75c00f-e55f-4860-8647-3b9cc85b37d9

import Mathlib
import Definitions.Def_OAIQ046C000
import Definitions.Def_OAIQ046C001
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_DevelopedFaces_univalent_triangles

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_ComponentRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonFaceIncidence
open Set Topology

variable {X : Type*} [TopologicalSpace X]

lemma component_region_eq (V : Set X) (x : V) :
    region V ConnectedComponents.mk (ConnectedComponents.mk x)=connectedComponentIn V x.val := by
  rw [connectedComponentIn_eq_image x.property]
  ext y
  constructor
  · rintro ⟨hy,hye⟩
    exact ⟨⟨y,hy⟩,ConnectedComponents.coe_eq_coe'.mp hye,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,ConnectedComponents.coe_eq_coe'.mpr hy⟩

lemma component_region_connected (V : Set X) (d : ConnectedComponents V) :
    IsConnected (region V ConnectedComponents.mk d) := by
  obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe d
  rw [component_region_eq]
  exact isConnected_connectedComponentIn_iff.mpr x.property

lemma component_regions_disjoint (V : Set X) {d e : ConnectedComponents V} (hne : d≠e) :
    Disjoint (region V ConnectedComponents.mk d) (region V ConnectedComponents.mk e) := by
  apply disjoint_left.mpr
  rintro x ⟨hx,hd⟩ ⟨hx',he⟩
  exact hne (hd.symm.trans he)
end CannonFaceIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FiniteSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonEmbeddedArc.Arc.instFintypeRefinementIndex _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

namespace CannonEmbeddedArc
namespace Arc
variable {X : Type*} [TopologicalSpace X]
lemma trans_injective {x y z : X} (a : Path x y) (b : Path y z)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hmeet : ∀ s t, a s=b t → s=1 ∧ t=0) : Function.Injective (a.trans b) := by
  intro s t he
  rw [Path.trans_apply,Path.trans_apply] at he
  split_ifs at he with hs ht ht
  · have h := congrArg Subtype.val (ha he)
    apply Subtype.ext
    dsimp at h
    linarith
  · obtain ⟨h₁,h₂⟩ := hmeet _ _ he
    have h₁' := congrArg Subtype.val h₁
    have h₂' := congrArg Subtype.val h₂
    apply Subtype.ext
    dsimp at h₁' h₂'
    linarith
  · obtain ⟨h₁,h₂⟩ := hmeet _ _ he.symm
    have h₁' := congrArg Subtype.val h₁
    have h₂' := congrArg Subtype.val h₂
    apply Subtype.ext
    dsimp at h₁' h₂'
    linarith
  · have h := congrArg Subtype.val (hb he)
    apply Subtype.ext
    dsimp at h
    linarith

theorem extend_arc [T2Space X] (a b : Arc X) (hab : a 1=b 0)
    (hy : b 1∉range a) :
    ∃ c : Arc X, c 0=a 0 ∧ c 1=b 1 ∧ range c⊆range a∪range b := by
  have hc : IsCompact (b ⁻¹' range a) :=
    (a.compact_range.isClosed.preimage b.continuous).isCompact
  have hn : (b ⁻¹' range a).Nonempty := ⟨0,⟨1,hab⟩⟩
  obtain ⟨v,hv⟩ := hc.exists_isGreatest hn
  obtain ⟨u,hu⟩ := hv.1
  have hv₁ : v≠1 := fun h => hy (h ▸ hv.1)
  let d := b.subarc v 1 hv₁
  have hd₀ : d 0=a u := (subarc_zero ..).trans hu.symm
  have hd₁ : d 1=b 1 := subarc_one ..
  have hds : range d⊆range b := subarc_range_subset ..
  have hmeet : ∀ s t, a s=d t → s=u ∧ t=0 := by
    intro s t he
    have hin : Icc.convexComb v 1 t∈b ⁻¹' range a := ⟨s,he⟩
    have hle := hv.2 hin
    have hvlt : (v:ℝ)<1 := lt_of_le_of_ne v.property.2 (fun h => hv₁ (Subtype.ext h))
    have hle' : (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1≤v := by
      change (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1≤v at hle
      exact hle
    have ht : t=0 := by
      apply Subtype.ext
      dsimp
      nlinarith [t.property.1]
    refine ⟨?_,ht⟩
    apply a.injective
    simpa only [ht,hd₀] using he
  by_cases hu₀ : u=0
  · refine ⟨d,by simpa only [hu₀] using hd₀,hd₁,hds.trans subset_union_right⟩
  · let c := a.subarc 0 u (Ne.symm hu₀)
    let p : Path (a 0) (a u) := ⟨c.map,subarc_zero ..,subarc_one ..⟩
    let q : Path (a u) (b 1) := ⟨d.map,hd₀,hd₁⟩
    have hpq : ∀ s t, p s=q t → s=1 ∧ t=0 := by
      intro s t he
      obtain ⟨hs,ht⟩ := hmeet (Icc.convexComb 0 u s) t he
      refine ⟨?_,ht⟩
      have huc : (u:ℝ)≠0 := fun h => hu₀ (Subtype.ext h)
      have hh := congrArg Subtype.val hs
      simp only [Icc.coe_convexComb] at hh
      apply Subtype.ext
      dsimp at hh ⊢
      have heq : ((s:ℝ)-1)*(u:ℝ)=0 := by nlinarith [hh]
      exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right huc)
    refine ⟨⟨(p.trans q).toContinuousMap,trans_injective p q c.injective d.injective hpq⟩,
      (p.trans q).source,(p.trans q).target,?_⟩
    change range (p.trans q)⊆range a∪range b
    rw [Path.trans_range]
    exact union_subset_union (subarc_range_subset a 0 u (Ne.symm hu₀)) hds
end Arc
end CannonEmbeddedArc

namespace CannonPolygonal
open CannonEmbeddedArc CannonEmbeddedArc.Arc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma FiniteSupport.mono {S T : Set E} (hT : FiniteSupport T) (hST : S⊆T) :
    FiniteSupport S := by
  obtain ⟨P,hP⟩ := hT
  exact ⟨P,hST.trans hP⟩
lemma FiniteSupport.segment (x y : E) : FiniteSupport (segment ℝ x y) := by
  classical
  exact ⟨{(x,y)},by simp⟩
lemma FiniteSupport.union {S T : Set E} (hS : FiniteSupport S) (hT : FiniteSupport T) :
    FiniteSupport (S∪T) := by
  classical
  obtain ⟨P,hP⟩ := hS
  obtain ⟨Q,hQ⟩ := hT
  refine ⟨P∪Q,?_⟩
  intro x hx
  rcases hx with hx|hx
  · obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hP hx)
    exact mem_iUnion₂.mpr ⟨p,Finset.mem_union_left Q hp,hx⟩
  · obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hQ hx)
    exact mem_iUnion₂.mpr ⟨p,Finset.mem_union_right P hp,hx⟩

theorem polyJoined_arc {U : Set E} {x y : E} (h : PolyJoined U x y) (hne : x≠y) :
    ∃ a : Arc E, a 0=x ∧ a 1=y ∧ range a⊆U ∧ FiniteSupport (range a) := by
  have hh : x=y ∨ ∃ a : Arc E, a 0=x ∧ a 1=y ∧ range a⊆U ∧ FiniteSupport (range a) := by
    clear hne
    induction h with
    | refl => exact Or.inl rfl
    | @tail y z _ hyz ih =>
      by_cases hxz : x=z
      · exact Or.inl hxz
      · apply Or.inr
        rcases ih with rfl|⟨a,ha₀,ha₁,haU,haS⟩
        · let b : Arc E := ⟨(Path.segment x z).toContinuousMap,Path.segment_injective_of_ne hxz⟩
          refine ⟨b,(Path.segment x z).source,(Path.segment x z).target,?_,?_⟩
          · change range (Path.segment x z)⊆U
            rwa [Path.range_segment]
          · change FiniteSupport (range (Path.segment x z))
            rw [Path.range_segment]
            exact FiniteSupport.segment x z
        · by_cases hz : z∈range a
          · obtain ⟨t,ht⟩ := hz
            have ht₀ : (0:I)≠t := fun h => hxz (ha₀.symm.trans ((congrArg a h).trans ht))
            refine ⟨a.subarc 0 t ht₀,(subarc_zero ..).trans ha₀,(subarc_one ..).trans ht,
              (subarc_range_subset ..).trans haU,haS.mono (subarc_range_subset ..)⟩
          · have hyz' : y≠z := fun h => hz ⟨1,ha₁.trans h⟩
            let b : Arc E := ⟨(Path.segment y z).toContinuousMap,Path.segment_injective_of_ne hyz'⟩
            have hb₀ : b 0=y := (Path.segment y z).source
            have hb₁ : b 1=z := (Path.segment y z).target
            have hbR : range b=segment ℝ y z := Path.range_segment y z
            obtain ⟨c,hc₀,hc₁,hcs⟩ := extend_arc a b (ha₁.trans hb₀.symm) (by simpa only [hb₁] using hz)
            refine ⟨c,hc₀.trans ha₀,hc₁.trans hb₁,hcs.trans (union_subset haU ?_),
              (haS.union ?_).mono hcs⟩
            · rwa [hbR]
            · rw [hbR]
              exact FiniteSupport.segment y z
  exact hh.resolve_left hne

end CannonPolygonal

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Lift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

namespace CannonWinding

lemma lift_exp (f : C(I,Circle)) (t : I) : Circle.exp (lift f t)=f t :=
  congr_fun (Circle.isCoveringMap_exp.liftPath_lifts f _ _) t

lemma turn_eq_of_lift (f : C(I,Circle)) (g : C(I,ℝ))
    (hg : ∀ t, Circle.exp (g t)=f t) : turn f=g 1-g 0 := by
  have hconst : ∀ t t', g t-lift f t=g t'-lift f t' := by
    apply Circle.isCoveringMap_exp.const_of_comp (g.continuous.sub (lift f).continuous)
    intro t t'
    change Circle.exp (g t-lift f t)=Circle.exp (g t'-lift f t')
    simp only [Circle.exp_sub,hg,lift_exp,div_self']
  have h := hconst 1 0
  dsimp only [turn]
  linarith

lemma turn_homotopy (H : C(I×I,Circle)) (hH : ∀ s, H (s,0)=H (s,1)) :
    turn (H.comp ⟨fun t => (0,t),by fun_prop⟩)=
      turn (H.comp ⟨fun t => (1,t),by fun_prop⟩) := by
  let f := H.comp (⟨fun t => (0,t),by fun_prop⟩ : C(I,I×I))
  let g := lift f
  have h₀ (t : I) : H (0,t)=Circle.exp (g t) := (lift_exp f t).symm
  let L := Circle.isCoveringMap_exp.liftHomotopy H g h₀
  have hL (s t : I) : Circle.exp (L (s,t))=H (s,t) :=
    congr_fun (Circle.isCoveringMap_exp.liftHomotopy_lifts H g h₀) (s,t)
  have heq : ∀ s s', L (s,1)-L (s,0)=L (s',1)-L (s',0) := by
    apply Circle.isCoveringMap_exp.const_of_comp (by fun_prop)
    intro s s'
    simp only [Circle.exp_sub,hL,←hH,div_self']
  rw [turn_eq_of_lift (H.comp ⟨fun t => (0,t),by fun_prop⟩) (L.comp ⟨fun t => (0,t),by fun_prop⟩) (fun t => hL 0 t),
    turn_eq_of_lift (H.comp ⟨fun t => (1,t),by fun_prop⟩) (L.comp ⟨fun t => (1,t),by fun_prop⟩) (fun t => hL 1 t)]
  exact heq 0 1

end CannonWinding

namespace CannonWinding
variable {A : Type*} [TopologicalSpace A]

lemma winding_homotopy (H : C(I×I,ℂ)) (hclosed : ∀ s, H (s,0)=H (s,1))
    (z : ℂ) (hz : z∉range H) :
    winding (H.comp ⟨fun t => (0,t),by fun_prop⟩) z
      (fun h => hz <| by rcases h with ⟨t,ht⟩; exact ⟨(0,t),ht⟩)=
    winding (H.comp ⟨fun t => (1,t),by fun_prop⟩) z
      (fun h => hz <| by rcases h with ⟨t,ht⟩; exact ⟨(1,t),ht⟩) := by
  let K := direction (H-.const (I×I) z) (fun p hp => hz ⟨p,sub_eq_zero.mp hp⟩)
  have hc (s : I) : K (s,0)=K (s,1) := by
    apply Circle.ext
    simp only [K,direction_coe,ContinuousMap.sub_apply,ContinuousMap.const_apply,hclosed]
  exact turn_homotopy K hc

lemma winding_moving_point (f : C(I,ℂ)) (hf : f 0=f 1) (p : C(I,ℂ))
    (hp : ∀ s, p s∉range f) : winding f (p 0) (hp 0)=winding f (p 1) (hp 1) := by
  let H : C(I×I,ℂ) := ⟨fun z => f z.2-p z.1,by fun_prop⟩
  have hH (z : I×I) : H z≠0 := fun h => hp z.1 ⟨z.2,sub_eq_zero.mp h⟩
  let K := direction H hH
  have hc (s : I) : K (s,0)=K (s,1) := by
    apply Circle.ext
    simp only [K,direction_coe,H,ContinuousMap.coe_mk,hf]
  exact turn_homotopy K hc

end CannonWinding

namespace CannonWinding
open Metric

lemma winding_eq_of_homotopy (f g : C(I,ℂ)) (z : ℂ) (hf : z∉range f) (hg : z∉range g)
    (H : C(I×I,ℂ)) (hclosed : ∀ s, H (s,0)=H (s,1))
    (h₀ : ∀ t, H (0,t)=f t) (h₁ : ∀ t, H (1,t)=g t) (hz : z∉range H) :
    winding f z hf=winding g z hg := by
  have h₀' : H.comp ⟨fun t => (0,t),by fun_prop⟩=f := ContinuousMap.ext h₀
  have h₁' : H.comp ⟨fun t => (1,t),by fun_prop⟩=g := ContinuousMap.ext h₁
  simpa only [h₀',h₁'] using winding_homotopy H hclosed z hz

theorem winding_locally_constant (f : C(I,ℂ)) (hf : f 0=f 1) :
    IsLocallyConstant (fun z : ↥((range f)ᶜ) => winding f z.val z.property) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro z
  have ho : IsOpen ((range f)ᶜ) := (isCompact_range f.continuous).isClosed.isOpen_compl
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds z.property)
  refine ⟨Subtype.val ⁻¹' ball z.val ε,isOpen_ball.preimage continuous_subtype_val,
    mem_ball_self hε,?_⟩
  intro w hw
  have hp (s : I) : Path.segment z.val w.val s∉range f := by
    apply hball
    apply (convex_ball z.val ε).segment_subset (mem_ball_self hε) hw
    rw [←Path.range_segment]
    exact mem_range_self s
  have heq := winding_moving_point f hf (Path.segment z.val w.val).toContinuousMap hp
  change winding f (Path.segment z.val w.val 0) _ =
    winding f (Path.segment z.val w.val 1) _ at heq
  simpa only [Path.source,Path.target] using heq.symm

end CannonWinding

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Reverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonPlanarCorner

lemma local_arc_flat {K : Set ℂ} {x : ℂ} (a : Arc ℂ)
    (Q : Finset (ℂ × ℂ)) (hQ : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {t : I} (ht₀ : 0<t) (ht₁ : t<1) (ht : a t=x)
    {U : Set ℂ} (hU : IsOpen U) (hxU : x∈U)
    (hUK : ∀ z∈U, z∈K ↔ z∈range a) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ x∈W ∧
      H (0,0)=x ∧ ∀ z∈W, (z∈K ↔ z∈H '' horizontal) := by
  obtain ⟨H,W,hW,htW,h₀,hW'⟩ := tame_graph_flat_chart (fun _ : Unit => a)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) Q (fun _ => hQ) () ht₀ ht₁
  refine ⟨H,W∩U,hW.inter hU,⟨ht ▸ htW,hxU⟩,h₀.trans ht,?_⟩
  intro z hz
  exact (hUK z hz.2).trans (by simpa only [iUnion_const] using hW' z hz.1)

lemma pair_start_local_arc (a b : Arc ℂ) (hab : a 0=b 0)
    (hc : ∀ s t, a s=b t → (s=0∨s=1) ∧ (t=0∨t=1)) :
    ∃ (c : Arc ℂ) (t : I) (U : Set ℂ), 0<t ∧ t<1 ∧ c t=a 0 ∧
      IsOpen U ∧ a 0∈U ∧ range c⊆range a∪range b ∧
      ∀ z∈U, (z∈range a∪range b ↔ z∈range c) := by
  let m : I := ⟨1/2,by constructor <;> norm_num⟩
  have hm₀ : 0 < m := by change (0:ℝ)<1/2; norm_num
  have hm₁ : m < 1 := by change (1/2:ℝ)<1; norm_num
  let A := a.subarc 0 m hm₀.ne
  let B := b.subarc 0 m hm₀.ne
  let p : Path (a m) (a 0) := A.path.symm.cast (by simp [A]) (by simp [A])
  let q : Path (a 0) (b m) := B.path.cast (by simpa [B] using hab) (by simp [B])
  have hp (s : I) : p s=a (Icc.convexComb 0 m (unitInterval.symm s)) := rfl
  have hq (s : I) : q s=b (Icc.convexComb 0 m s) := rfl
  have hpq (s t : I) (he : p s=q t) : s=1 ∧ t=0 := by
    obtain ⟨hs,ht⟩ := hc _ _ he
    have hsₘ : Icc.convexComb 0 m (unitInterval.symm s) ≤ m := Icc.convexComb_le hm₀.le _
    have htₘ : Icc.convexComb 0 m t ≤ m := Icc.convexComb_le hm₀.le _
    have hs₀ : Icc.convexComb 0 m (unitInterval.symm s)=0 := hs.resolve_right (fun h => hm₁.not_ge (h ▸ hsₘ))
    have ht₀ : Icc.convexComb 0 m t=0 := ht.resolve_right (fun h => hm₁.not_ge (h ▸ htₘ))
    have hsval := congrArg Subtype.val hs₀
    have htval := congrArg Subtype.val ht₀
    constructor <;> apply Subtype.ext
    · simp only [Icc.coe_convexComb,unitInterval.coe_symm_eq] at hsval
      change (s:ℝ)=1
      dsimp [m] at hsval
      linarith
    · simp only [Icc.coe_convexComb] at htval
      change (t:ℝ)=0
      dsimp [m] at htval
      linarith
  have hpi : Function.Injective p := fun s t he =>
    unitInterval.symm_bijective.injective (A.injective he)
  have hqi : Function.Injective q := B.injective
  let c : Arc ℂ := ⟨(p.trans q).toContinuousMap,trans_injective p q hpi hqi hpq⟩
  have hcrange : range c=a '' Icc 0 m ∪ b '' Icc 0 m := by
    change range (p.trans q)=_
    rw [Path.trans_range]
    have hpR : range p=range A := by exact Path.symm_range A.path
    rw [hpR]
    change range A∪range B=_
    rw [subarc_range_eq a hm₀,subarc_range_eq b hm₀]
  let T : Set ℂ := a '' Ici m ∪ b '' Ici m
  have hT : IsClosed T :=
    (isClosed_Ici.isCompact.image a.continuous).isClosed.union
      (isClosed_Ici.isCompact.image b.continuous).isClosed
  have hxT : a 0∉T := by
    rintro (⟨s,hs,he⟩|⟨s,hs,he⟩)
    · have he₀ := a.injective he
      subst s
      exact hm₀.not_ge hs
    · have he₀ := b.injective (he.trans hab)
      subst s
      exact hm₀.not_ge hs
  refine ⟨c,m,Tᶜ,hm₀,hm₁,?_,hT.isOpen_compl,hxT,?_,?_⟩
  · change (p.trans q) m=a 0
    rw [Path.trans_apply]
    split_ifs with h
    · have hr : (⟨2*(m:ℝ),(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨m.2.1,h⟩⟩:I)=1 := by apply Subtype.ext; dsimp [m]; norm_num
      rw [hr,Path.target]
    · exact (h (by change (1/2:ℝ)≤1/2; rfl)).elim
  · rw [hcrange]
    exact union_subset_union (image_subset_range _ _) (image_subset_range _ _)
  · intro z hz
    rw [hcrange]
    constructor
    · rintro (⟨s,rfl⟩|⟨s,rfl⟩)
      · exact Or.inl ⟨s,⟨unitInterval.nonneg s,le_of_not_ge (fun hm => hz (Or.inl ⟨s,hm,rfl⟩))⟩,rfl⟩
      · exact Or.inr ⟨s,⟨unitInterval.nonneg s,le_of_not_ge (fun hm => hz (Or.inr ⟨s,hm,rfl⟩))⟩,rfl⟩
    · intro hh
      exact union_subset_union (image_subset_range _ _) (image_subset_range _ _) hh
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonPlanarCorner CannonFaceIncidence

lemma pair_start_flat (a b : Arc ℂ) (hab : a 0 = b 0)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ a 0 ∈ W ∧
      H (0,0)=a 0 ∧ ∀ z∈W, (z∈range a ∪ range b ↔ z∈H '' horizontal) := by
  obtain ⟨c,t,U,ht₀,ht₁,ht,hU,hxU,hsub,hUK⟩ := pair_start_local_arc a b hab hc
  exact local_arc_flat c Q (fun z hz => (hsub hz).elim (fun h => ha h) (fun h => hb h)) ht₀ ht₁ ht hU hxU hUK

theorem pair_flat_at_left (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2) (t : I) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ a t ∈ W ∧
      H (0,0)=a t ∧ ∀ z∈W, (z∈range a ∪ range b ↔ z∈H '' horizontal) := by
  by_cases ht₀ : t=0
  · subst t
    exact pair_start_flat a b hab₀ hc Q ha hb
  by_cases ht₁ : t=1
  · subst t
    have hc' : ∀ s t, a.reverse s = b.reverse t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := by
      intro s t he
      obtain ⟨hs,ht⟩ := hc _ _ he
      simpa only [unitInterval.symm_eq_zero,unitInterval.symm_eq_one,or_comm] using And.intro hs ht
    have hh := pair_start_flat a.reverse b.reverse (by simpa) hc' Q
      (by simpa using ha) (by simpa using hb)
    simpa using hh
  have ht₀' : 0<t := lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht₀)
  have ht₁' : t<1 := lt_of_le_of_ne (unitInterval.le_one t) ht₁
  have htB : a t ∉ range b := by
    rintro ⟨s,hs⟩
    exact ((hc t s hs.symm).1).elim ht₀ ht₁
  exact local_arc_flat a Q ha ht₀' ht₁' rfl
    b.compact_range.isClosed.isOpen_compl htB (fun z hz => or_iff_left hz)

theorem pair_incident_labels (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {D : Type*} [TopologicalSpace D] [DiscreteTopology D]
    {π : ((range a ∪ range b)ᶜ : Set ℂ) → D} (hπ : Continuous π) :
    ∃ labels : Bool → D, ∀ x∈range a ∪ range b,
      incident _ π x=range labels := by
  let K : Set ℂ := range a ∪ range b
  have hK : IsPreconnected K :=
    IsPreconnected.union' ⟨a 0,mem_range_self 0,⟨0,hab₀.symm⟩⟩
      (isPreconnected_range a.continuous) (isPreconnected_range b.continuous)
  have hflat : ∀ x∈K, ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ x∈W ∧
      H (0,0)=x ∧ ∀ z∈W, (z∈K ↔ z∈H '' horizontal) := by
    rintro x (⟨t,rfl⟩|⟨t,rfl⟩)
    · exact pair_flat_at_left a b hab₀ hab₁ hc Q ha hb t
    · have hh := pair_flat_at_left b a hab₀.symm hab₁.symm
        (fun s t he => (hc t s he.symm).symm) Q hb ha t
      simpa only [K,union_comm] using hh
  have hloc₀ : ∀ x∈K, ∃ U : Set ℂ, IsOpen U ∧ x∈U ∧
      ∃ labels : Bool → D, ∀ y∈U∩K, incident _ π y=range labels := by
    intro x hx
    obtain ⟨H,W,hW,hxW,h₀,hW'⟩ := hflat x hx
    have he (z : ℂ) : z∈H '' horizontal ↔ (H.symm z).2=0 := by
      rw [H.image_eq_preimage_symm]
      rfl
    obtain ⟨U,hU,h₀U,_,labels,hlabels⟩ := flat_chart_incidence hπ H hW (h₀.symm ▸ hxW)
      (fun z hz => not_congr ((hW' z hz).trans (he z)))
    exact ⟨U,hU,h₀ ▸ h₀U,labels,by simpa only [compl_compl] using hlabels⟩
  have hloc : ∀ x∈K, ∃ U : Set ℂ, IsOpen U ∧ x∈U ∧
      ∀ y∈K∩U, incident _ π y=incident _ π x := by
    intro x hx
    obtain ⟨U,hU,hxU,l,hl⟩ := hloc₀ x hx
    exact ⟨U,hU,hxU,fun y hy => (hl y hy.symm).trans (hl x ⟨hxU,hx⟩).symm⟩
  have hxK : a 0∈K := Or.inl (mem_range_self 0)
  obtain ⟨U,hU,hxU,l,hl⟩ := hloc₀ (a 0) hxK
  refine ⟨l,fun x hx => ?_⟩
  exact (incident_constant_on_preconnected hK hloc x hx (a 0) hxK).trans (hl (a 0) ⟨hxU,hxK⟩)
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem pair_labels_surjective (a b : Arc ℂ) (hab₀ : a 0 = b 0) (hab₁ : a 1 = b 1)
    (hc : ∀ s t, a s = b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {D : Type*} [TopologicalSpace D] [DiscreteTopology D]
    {π : ((range a ∪ range b)ᶜ : Set ℂ) → D} (hπ : Continuous π)
    (hπs : Function.Surjective π) :
    ∃ labels : Bool → D, Function.Surjective labels ∧
      ∀ x∈range a ∪ range b, incident _ π x=range labels := by
  obtain ⟨l,hl⟩ := pair_incident_labels a b hab₀ hab₁ hc Q ha hb hπ
  refine ⟨l,?_,hl⟩
  intro d
  obtain ⟨z,hz⟩ := hπs d
  have hd : (region _ π d).Nonempty := ⟨z.val,z.property,hz⟩
  have hK : IsClosed (range a ∪ range b) := a.compact_range.isClosed.union b.compact_range.isClosed
  obtain ⟨x,hx,_,hxd⟩ := region_boundary_hits hK (T:=∅) isClosed_empty (empty_subset _)
    (by simpa using (isPreconnected_univ : IsPreconnected (univ : Set ℂ)))
    ⟨a 0,Or.inl (mem_range_self 0),notMem_empty _⟩ hπ d hd
  change d∈range l
  rw [←hl x hx]
  exact hxd
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

lemma centered_chord_endpoints (A B : ℂ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1/2) :
    let x := A+(1/2:ℝ)•(B-A)
    let c := ε•(B-A)
    x-c∈segment ℝ A B ∧ x+c∈segment ℝ A B := by
  dsimp
  rw [segment_eq_image']
  constructor
  · refine ⟨1/2-ε,⟨by linarith,by linarith⟩,?_⟩
    simp only [sub_smul]
    abel
  · refine ⟨1/2+ε,⟨by linarith,by linarith⟩,?_⟩
    simp only [add_smul]
    abel

lemma centered_chord_ball (A B : ℂ) (hAB : A≠B) {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : z∈segment ℝ A B)
    (hb : z∈ball (A+(1/2:ℝ)•(B-A)) ‖ε•(B-A)‖) :
    z∈segment ℝ (A+(1/2:ℝ)•(B-A)-ε•(B-A))
      (A+(1/2:ℝ)•(B-A)+ε•(B-A)) := by
  rw [segment_eq_image'] at hz ⊢
  obtain ⟨s,hs,rfl⟩ := hz
  have hD : 0 < ‖B-A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAB.symm)
  have he : A+s•(B-A)-(A+(1/2:ℝ)•(B-A))=(s-1/2)•(B-A) := by rw [sub_smul]; abel
  have habs : |s-1/2| < ε := by
    rw [mem_ball,dist_eq_norm,he,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hε] at hb
    exact (mul_lt_mul_iff_left₀ hD).mp hb
  have hlo := (abs_lt.mp habs).1
  have hhi := (abs_lt.mp habs).2
  refine ⟨(s-1/2+ε)/(2*ε),⟨div_nonneg (by linarith) (by positivity),
    (div_le_one (by positivity : 0 < 2*ε)).mpr (by linarith)⟩,?_⟩
  have hd : (A+(1/2:ℝ)•(B-A)+ε•(B-A))-
      (A+(1/2:ℝ)•(B-A)-ε•(B-A))=(2*ε)•(B-A) := by
    rw [mul_smul,two_smul]; abel
  dsimp only
  rw [hd,smul_smul,div_mul_cancel₀ _ (by positivity : 2*ε≠0)]
  simp only [add_smul,sub_smul]
  abel

theorem pair_isolated_chord (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ)) (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ (u v : I) (x c : ℂ), u < v ∧ c≠0 ∧ a u=x-c ∧ a v=x+c ∧
      a '' Icc u v=segment ℝ (a u) (a v) ∧
      (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v := by
  let m : I := ⟨1/2,by constructor  <;> norm_num⟩
  obtain ⟨p,q,hpm,hmq,hleft,_,_⟩ := tame_interior_corner Q a ha
    (t:=m) (by change (0:ℝ) < 1/2; norm_num) (by change (1/2:ℝ) < 1; norm_num)
  let D := a m-a p
  have hD : D≠0 := sub_ne_zero.mpr (a.injective.ne hpm.ne.symm)
  have hDn : 0 < ‖D‖ := norm_pos_iff.mpr hD
  let x := a p+(1/2:ℝ)•D
  have hxseg : x∈segment ℝ (a p) (a m) := by
    rw [segment_eq_image']
    exact ⟨1/2,by constructor  <;> norm_num,rfl⟩
  obtain ⟨w,hw,hwx⟩ := hleft.symm ▸ hxseg
  have hxp : x≠a p := by
    intro he
    have hh : (1/2:ℝ)•D=0 := by
      change a p+(1/2:ℝ)•D=a p at he
      exact add_left_cancel (he.trans (add_zero (a p)).symm)
    exact hD ((smul_eq_zero.mp hh).resolve_left (by norm_num))
  have hxm : x≠a m := by
    intro he
    have hh : (1/2:ℝ)•D=D := by
      change a p+(1/2:ℝ)•D=a m at he
      exact eq_sub_of_add_eq (by rwa [add_comm])
    have hh' : ((1/2:ℝ)-1)•D=0 := by rw [sub_smul,one_smul,hh,sub_self]
    exact hD ((smul_eq_zero.mp hh').resolve_left (by norm_num))
  have hpw : p < w := lt_of_le_of_ne hw.1 (fun he => hxp (he ▸ hwx).symm)
  have hwm : w  <  m := lt_of_le_of_ne hw.2 (fun he => hxm (he ▸ hwx).symm)
  let T : Set ℂ := a '' Iic p ∪ a '' Ici m ∪ range b
  have hT : IsClosed T :=
    ((isClosed_Iic.isCompact.image a.continuous).isClosed.union
      (isClosed_Ici.isCompact.image a.continuous).isClosed).union b.compact_range.isClosed
  have hxT : x∉T := by
    rintro ((⟨s,hs,he⟩|⟨s,hs,he⟩)|⟨s,hs⟩)
    · have he' := a.injective (he.trans hwx.symm)
      subst s
      exact hpw.not_ge hs
    · have he' := a.injective (he.trans hwx.symm)
      subst s
      exact hwm.not_ge hs
    · rcases (hc w s (hwx.trans hs.symm)).2 with rfl | rfl
      · have hwzero := a.injective ((hwx.trans hs.symm).trans hab₀.symm)
        exact (not_lt_of_ge (show (0:I) ≤ p from p.2.1)) (hwzero ▸ hpw)
      · have hwone := a.injective ((hwx.trans hs.symm).trans hab₁.symm)
        exact (not_lt_of_ge (show m ≤ (1:I) from m.2.2)) (hwone ▸ hwm)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hT.isOpen_compl.mem_nhds hxT)
  let ε := min (1/4) (δ/(2*‖D‖))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hε₁ : ε < 1/2 := (min_le_left _ _).trans_lt (by norm_num)
  let c : ℂ := ε•D
  have hcn : ‖c‖=ε*‖D‖ := by simp [c,Real.norm_eq_abs,abs_of_pos hε]
  have hc₀ : c≠0 := smul_ne_zero hε.ne' hD
  have hcδ : ‖c‖ < δ := by
    rw [hcn]
    have hh : ε*(2*‖D‖) ≤ δ := (le_div_iff₀ (by positivity)).mp (min_le_right (1/4) (δ/(2*‖D‖)))
    nlinarith
  have hend := centered_chord_endpoints (a p) (a m) hε hε₁
  change x-c∈segment ℝ (a p) (a m) ∧ x+c∈segment ℝ (a p) (a m) at hend
  obtain ⟨u,hu,hu'⟩ := hleft.symm ▸ hend.1
  obtain ⟨v,hv,hv'⟩ := hleft.symm ▸ hend.2
  have huv : u≠v := by
    intro he
    have hh : x-c=x+c := hu'.symm.trans (he ▸ hv')
    have hh' : c+c=0 := by linear_combination -hh
    exact hc₀ (by linear_combination (1/2:ℂ)*hh')
  have hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ segment ℝ (x-c) (x+c) := by
    rintro z ⟨hz,hzb⟩
    have hzT : z∉T := hball (ball_subset_ball hcδ.le hzb)
    rcases hz with ⟨s,rfl⟩|hz
    · have hsp : p ≤ s := le_of_not_ge (fun hh => hzT (Or.inl (Or.inl ⟨s,hh,rfl⟩)))
      have hsm : s  ≤  m := le_of_not_ge (fun hh => hzT (Or.inl (Or.inr ⟨s,hh,rfl⟩)))
      exact centered_chord_ball (a p) (a m) (a.injective.ne hpm.ne) hε
        (hleft ▸ ⟨s,⟨hsp,hsm⟩,rfl⟩) hzb
    · exact (hzT (Or.inr hz)).elim
  rcases lt_or_gt_of_ne huv with huv|hvu
  · have he := segment_subarc_image a hpm huv hleft
      (fun s hs => ⟨hu.1.trans hs.1,hs.2.trans hv.2⟩)
    refine ⟨u,v,x,c,huv,hc₀,hu',hv',he,?_⟩
    rw [he,hu',hv']
    exact hsmall
  · have he := segment_subarc_image a hpm hvu hleft
      (fun s hs => ⟨hv.1.trans hs.1,hs.2.trans hu.2⟩)
    refine ⟨v,u,x,-c,hvu,neg_ne_zero.mpr hc₀,?_,?_,he,?_⟩
    · simpa using hv'
    · simpa only [sub_eq_add_neg] using hu'
    · rw [norm_neg,he,hv',hu',segment_symm]
      exact hsmall
end CannonEmbeddedArc.Arc

noncomputable section
open Set Topology unitInterval

namespace CannonWinding
open Set Topology unitInterval

lemma turn_path_trans {a b c : Circle} (p : Path a b) (q : Path b c) :
    turn (p.trans q).toContinuousMap=turn p.toContinuousMap+turn q.toContinuousMap := by
  let f := lift p.toContinuousMap
  let g := lift q.toContinuousMap
  let P : Path (f 0) (f 1) := ⟨f,rfl,rfl⟩
  let Q : Path (f 1) (g 1+f 1-g 0) :=
    ⟨⟨fun t => g t+f 1-g 0,by fun_prop⟩,by ring,rfl⟩
  have hP (t : I) : Circle.exp (P t)=p t := lift_exp _ t
  have hQ (t : I) : Circle.exp (Q t)=q t := by
    change Circle.exp (g t+f 1-g 0)=q t
    simp only [Circle.exp_sub,Circle.exp_add,f,g,lift_exp]
    simp
  have hL (t : I) : Circle.exp ((P.trans Q) t)=(p.trans q) t := by
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs <;> simp only [hP,hQ]
  rw [turn_eq_of_lift _ (P.trans Q).toContinuousMap hL]
  change (P.trans Q) 1-(P.trans Q) 0=_
  rw [Path.target,Path.source]
  dsimp only [turn,f,g]
  ring

lemma winding_path_trans {a b c : ℂ} (p : Path a b) (q : Path b c)
    (z : ℂ) (hp : z∉range p) (hq : z∉range q) :
    winding (p.trans q).toContinuousMap z (by change z∉range (p.trans q); rw [Path.trans_range]; exact not_or.mpr ⟨hp,hq⟩)=
      winding p.toContinuousMap z hp+winding q.toContinuousMap z hq := by
  let f := direction (p.toContinuousMap-.const I z) (fun t ht => hp ⟨t,sub_eq_zero.mp ht⟩)
  let g := direction (q.toContinuousMap-.const I z) (fun t ht => hq ⟨t,sub_eq_zero.mp ht⟩)
  have hfg : f 1=g 0 := by
    apply Circle.ext
    simp [f,g,direction_coe]
  let P : Path (f 0) (f 1) := ⟨f,rfl,rfl⟩
  let Q : Path (f 1) (g 1) := ⟨g,hfg.symm,rfl⟩
  have he : direction ((p.trans q).toContinuousMap-.const I z)
      (fun t ht => (show z∉range (p.trans q) by rw [Path.trans_range]; exact not_or.mpr ⟨hp,hq⟩)
        ⟨t,sub_eq_zero.mp ht⟩)=(P.trans Q).toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change ((p.trans q) t-z)/(‖(p.trans q) t-z‖:ℂ)=((P.trans Q) t:ℂ)
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs <;> rfl
  change turn (direction _ _)=turn f+turn g
  rw [he]
  exact turn_path_trans P Q

lemma winding_path_homotopy {a : ℂ} {p q : Path a a} (H : p.Homotopy q)
    (z : ℂ) (hz : z∉range H) :
    winding p.toContinuousMap z (fun ⟨t,ht⟩ => hz ⟨(0,t),by simpa using ht⟩)=
      winding q.toContinuousMap z (fun ⟨t,ht⟩ => hz ⟨(1,t),by simpa using ht⟩) := by
  exact winding_eq_of_homotopy _ _ _ _ _ H.toHomotopy.toContinuousMap
    (fun s => (H.source s).trans (H.target s).symm)
    (fun t => H.map_zero_left t) (fun t => H.map_one_left t) hz

lemma upperSemi_im (t : I) : 0≤(upperSemi t).im := by
  change 0≤(Circle.exp (Real.pi*(1-(t:ℝ))):ℂ).im
  rw [Circle.coe_exp,Complex.exp_ofReal_mul_I_im]
  exact Real.sin_nonneg_of_mem_Icc ⟨mul_nonneg Real.pi_pos.le (sub_nonneg.mpr t.property.2),
    by nlinarith [t.property.1,Real.pi_pos]⟩
lemma lowerSemi_im (t : I) : (lowerSemi t).im≤0 := by
  change (Circle.exp (Real.pi*(1+(t:ℝ))):ℂ).im≤0
  rw [Circle.coe_exp,Complex.exp_ofReal_mul_I_im,
    show Real.pi*(1+(t:ℝ))=(Real.pi*(t:ℝ))+Real.pi by ring,Real.sin_add_pi]
  exact neg_nonpos.mpr (Real.sin_nonneg_of_mem_Icc
    ⟨mul_nonneg Real.pi_pos.le t.property.1,mul_le_of_le_one_right Real.pi_pos.le t.property.2⟩)

lemma winding_upperSemi :
    winding upperSemi.toContinuousMap 0 (by rintro ⟨t,ht⟩; change upperSemi t=0 at ht; have := upperSemi_norm t; rw [ht,norm_zero] at this; norm_num at this) = -Real.pi := by
  let f : C(I,ℝ) := ⟨fun t => Real.pi*(1-(t:ℝ)),by fun_prop⟩
  have he : direction (upperSemi.toContinuousMap-.const I 0) (by
      intro t ht
      have hn := upperSemi_norm t
      change upperSemi t-0=0 at ht
      rw [sub_zero] at ht
      rw [ht,norm_zero] at hn
      norm_num at hn)=Circle.exp.comp f := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change (upperSemi t-0)/(‖upperSemi t-0‖:ℂ)=(Circle.exp (f t):ℂ)
    simp only [sub_zero,upperSemi_norm,Complex.ofReal_one,div_one]
    rfl
  change turn (direction _ _)=_
  rw [he,turn_eq_of_lift _ f (fun _ => rfl)]
  simp [f]

lemma winding_lowerSemi :
    winding lowerSemi.toContinuousMap 0 (by rintro ⟨t,ht⟩; change lowerSemi t=0 at ht; have := lowerSemi_norm t; rw [ht,norm_zero] at this; norm_num at this) = Real.pi := by
  let f : C(I,ℝ) := ⟨fun t => Real.pi*(1+(t:ℝ)),by fun_prop⟩
  have he : direction (lowerSemi.toContinuousMap-.const I 0) (by
      intro t ht
      have hn := lowerSemi_norm t
      change lowerSemi t-0=0 at ht
      rw [sub_zero] at ht
      rw [ht,norm_zero] at hn
      norm_num at hn)=Circle.exp.comp f := by
    apply ContinuousMap.ext
    intro t
    apply Circle.ext
    change (lowerSemi t-0)/(‖lowerSemi t-0‖:ℂ)=(Circle.exp (f t):ℂ)
    simp only [sub_zero,lowerSemi_norm,Complex.ofReal_one,div_one]
    rfl
  change turn (direction _ _)=_
  rw [he,turn_eq_of_lift _ f (fun _ => rfl)]
  simp [f]
  ring
end CannonWinding

namespace CannonWinding
open Set Topology unitInterval Metric

lemma winding_outside_move {a : ℂ} (p : Path a a) (hp : ∀ t, 1≤‖p t‖)
    {z : ℂ} (hz : ‖z‖<1) :
    winding p.toContinuousMap z (path_outside_avoids p hp hz)=
      winding p.toContinuousMap 0 (path_outside_avoids p hp (by simp)) := by
  have hw (s : I) : ‖Path.segment z 0 s‖<1 := by
    have hs : Path.segment z 0 s∈ball (0:ℂ) 1 := by
      apply (convex_ball (0:ℂ) 1).segment_subset
        (by simpa [mem_ball,dist_zero_right] using hz) (show (0:ℂ)∈ball (0:ℂ) 1 by simp)
      rw [←Path.range_segment]
      exact mem_range_self s
    simpa [mem_ball,dist_zero_right] using hs
  have he := winding_moving_point p.toContinuousMap (by change p 0=p 1; simp)
    (Path.segment z 0).toContinuousMap (fun s => path_outside_avoids p hp (hw s))
  change winding _ (Path.segment z 0 0) _=winding _ (Path.segment z 0 1) _ at he
  simpa only [Path.source,Path.target] using he

lemma segment_diameter_im (t : I) : (Path.segment (-1:ℂ) 1 t).im=0 := by
  simp [Path.segment,AffineMap.lineMap_apply]

theorem winding_chord_replace (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (q : Path (-1:ℂ) 1) (hq : ∀ t, ‖q t‖=1)
    (sgn : ℝ) (hsgn : sgn=1 ∨ sgn= -1) (hside : ∀ t, sgn*(q t).im≤0)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    ∃ hz : ((sgn*η:ℝ):ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ),
      winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap
        (((sgn*η:ℝ):ℂ)*Complex.I) hz =
      winding (q.trans γ).toContinuousMap 0 (by
        apply path_outside_avoids (q.trans γ) _ (by simp)
        intro t
        rw [Path.trans_apply]
        split_ifs
        · exact (hq _).ge
        · exact hγ _) := by
  let z : ℂ := ((sgn*η:ℝ):ℂ)*Complex.I
  have hnz : ‖z‖<1 := by
    rcases hsgn with rfl|rfl <;> simpa [z,norm_mul,Complex.norm_I,abs_of_pos hη] using hη₁
  have himz : sgn*z.im=η := by
    rcases hsgn with rfl|rfl <;> simp [z]
  have him (s t : I) : sgn*(blendPaths (Path.segment (-1:ℂ) 1) q (s,t)).im≤0 := by
    change sgn*(((1-(s:ℝ)) • Path.segment (-1:ℂ) 1 t+(s:ℝ) • q t).im)≤0
    simp only [Complex.add_im,Complex.smul_im,smul_eq_mul,segment_diameter_im,mul_zero,zero_add]
    nlinarith [hside t,s.property.1]
  let H := (blendPaths (Path.segment (-1:ℂ) 1) q).hcomp (Path.Homotopy.refl γ)
  have hzH : z∉range H := by
    rintro ⟨⟨s,t⟩,he⟩
    change (blendPaths (Path.segment (-1:ℂ) 1) q).hcomp (Path.Homotopy.refl γ) (s,t)=z at he
    rw [Path.Homotopy.hcomp_apply] at he
    split_ifs at he with h
    · change blendPaths (Path.segment (-1:ℂ) 1) q (s,_) = z at he
      have hh := him s ⟨2*(t:ℝ),(unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1,h⟩⟩
      rw [he,himz] at hh
      exact hη.not_ge hh
    · exact path_outside_avoids γ hγ hnz ⟨_,he⟩
  have hp : z∉range ((Path.segment (-1:ℂ) 1).trans γ) := by
    rintro ⟨t,ht⟩
    exact hzH ⟨(0,t),by simpa [H] using ht⟩
  refine ⟨hp,?_⟩
  have he := winding_path_homotopy H z hzH
  change winding _ z hp=_
  rw [he]
  apply winding_outside_move (q.trans γ) _ hnz
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact (hq _).ge
  · exact hγ _

theorem chord_winding_jump (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    ∃ (hplus : (η:ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ))
      (hminus : -(η:ℂ)*Complex.I∉range ((Path.segment (-1:ℂ) 1).trans γ)),
    winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap ((η:ℂ)*Complex.I) hplus -
      winding ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap (-(η:ℂ)*Complex.I) hminus
      =2*Real.pi := by
  obtain ⟨hp,hp'⟩ := winding_chord_replace γ hγ lowerSemi lowerSemi_norm 1 (Or.inl rfl)
    (fun t => by simpa using lowerSemi_im t) η hη hη₁
  obtain ⟨hm,hm'⟩ := winding_chord_replace γ hγ upperSemi upperSemi_norm (-1) (Or.inr rfl)
    (fun t => by simpa using upperSemi_im t) η hη hη₁
  simp only [one_mul,neg_one_mul,Complex.ofReal_neg] at hp hm hp' hm'
  refine ⟨hp,hm,?_⟩
  have hγ₀ := path_outside_avoids γ hγ (z:=0) (by simp)
  have hl₀ := path_outside_avoids lowerSemi (fun t => (lowerSemi_norm t).ge) (z:=0) (by simp)
  have hu₀ := path_outside_avoids upperSemi (fun t => (upperSemi_norm t).ge) (z:=0) (by simp)
  rw [hp',hm',winding_path_trans lowerSemi γ 0 hl₀ hγ₀,
    winding_path_trans upperSemi γ 0 hu₀ hγ₀,winding_lowerSemi,winding_upperSemi]
  ring
end CannonWinding

namespace CannonWinding
open Set Topology unitInterval

lemma winding_on_component (f : C(I,ℂ)) (hf : f 0=f 1) {z w : ℂ}
    (hz : z∉range f) (hw : w∈connectedComponentIn (range f)ᶜ z) :
    winding f z hz=winding f w (connectedComponentIn_subset _ _ hw) := by
  let V : Set ℂ := (range f)ᶜ
  let z' : V := ⟨z,hz⟩
  let w' : V := ⟨w,connectedComponentIn_subset _ _ hw⟩
  have hwc : w'∈connectedComponent z' := by
    have hwi : w∈Subtype.val '' connectedComponent z' :=
      (connectedComponentIn_eq_image (F:=V) (x:=z) hz) ▸ hw
    obtain ⟨v,hv,hve⟩ := hwi
    have he : v=w' := Subtype.ext hve
    exact he ▸ hv
  exact (winding_locally_constant f hf).apply_eq_of_isPreconnected
    (s:=connectedComponent z') isPreconnected_connectedComponent
    (x:=z') (y:=w') (mem_connectedComponent (x:=z')) hwc

theorem chord_separates (γ : Path (1:ℂ) (-1)) (hγ : ∀ t, 1≤‖γ t‖)
    (η : ℝ) (hη : 0<η) (hη₁ : η<1) :
    -(η:ℂ)*Complex.I∉connectedComponentIn
      (range ((Path.segment (-1:ℂ) 1).trans γ))ᶜ ((η:ℂ)*Complex.I) := by
  obtain ⟨hp,hm,he⟩ := chord_winding_jump γ hγ η hη hη₁
  intro hh
  have hc : ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap 0=
      ((Path.segment (-1:ℂ) 1).trans γ).toContinuousMap 1 := by
    change ((Path.segment (-1:ℂ) 1).trans γ) 0=((Path.segment (-1:ℂ) 1).trans γ) 1
    simp
  have heq := winding_on_component _ hc hp hh
  rw [heq,sub_self] at he
  linarith [Real.pi_pos]
end CannonWinding

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Portion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

lemma portion_range (a : Arc ℂ) {u v : I} (huv : u ≤ v) :
    range (a.portion u v)=a '' Icc u v := by
  rcases huv.eq_or_lt with he|hl
  · subst v
    simp [portion,Icc.convexComb_eq]
  · exact subarc_range_eq a hl

lemma pair_closing_path (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (u v : I) :
    ∃ γ : Path (a v) (a u), range γ=
      a '' Icc v 1 ∪ range b ∪ a '' Icc 0 u := by
  let p : Path (a 1) (a 0) := b.path.symm.cast hab₁ hab₀
  refine ⟨((a.portion v 1).trans p).trans (a.portion 0 u),?_⟩
  rw [Path.trans_range,Path.trans_range,portion_range a (unitInterval.le_one v),
    portion_range a (unitInterval.nonneg u)]
  have hp : range p=range b := Path.symm_range b.path
  rw [hp]

lemma isolated_chord_closer (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    {u v : I} (huv : u < v) {x c : ℂ} (hu : a u=x-c) (hv : a v=x+c)
    (he : a '' Icc u v=segment ℝ (a u) (a v))
    (hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v) :
    ∃ γ : Path (a v) (a u),
      range (Path.segment (a u) (a v))∪range γ=range a∪range b ∧
      ∀ t, ‖c‖ ≤ dist (γ t) x := by
  obtain ⟨γ,hγ⟩ := pair_closing_path a b hab₀ hab₁ u v
  have hball : ∀ z∈(range a∪range b)∩ball x ‖c‖,
      ∃ s∈Ioo u v, a s=z := by
    intro z hz
    obtain ⟨s,hs,hsz⟩ := hsmall hz
    have hsu : s≠u := by
      intro h
      have hh := hz.2
      rw [←hsz,h,hu,mem_ball,dist_eq_norm] at hh
      have hd : x-c-x=-c := by abel
      rw [hd,norm_neg] at hh
      exact lt_irrefl _ hh
    have hsv : s≠v := by
      intro h
      have hh := hz.2
      rw [←hsz,h,hv,mem_ball,dist_eq_norm,add_sub_cancel_left] at hh
      exact lt_irrefl _ hh
    exact ⟨s,⟨lt_of_le_of_ne hs.1 hsu.symm,lt_of_le_of_ne hs.2 hsv⟩,hsz⟩
  refine ⟨γ,?_,?_⟩
  · rw [Path.range_segment,hγ,←he]
    apply Subset.antisymm
    · exact union_subset (fun _ h => Or.inl (image_subset_range _ _ h))
        (union_subset (union_subset (fun _ h => Or.inl (image_subset_range _ _ h)) subset_union_right)
          (fun _ h => Or.inl (image_subset_range _ _ h)))
    · rintro z (⟨s,rfl⟩|hz)
      · rcases lt_trichotomy s u with hsu | rfl | hus
        · exact Or.inr (Or.inr ⟨s,⟨unitInterval.nonneg s,hsu.le⟩,rfl⟩)
        · exact Or.inl ⟨s,⟨le_rfl,huv.le⟩,rfl⟩
        · by_cases hvs : v < s
          · exact Or.inr (Or.inl (Or.inl ⟨s,⟨hvs.le,unitInterval.le_one s⟩,rfl⟩))
          · exact Or.inl ⟨s,⟨hus.le,le_of_not_gt hvs⟩,rfl⟩
      · exact Or.inr (Or.inl (Or.inr hz))
  · intro t
    apply le_of_not_gt
    intro ht
    have htγ := mem_range_self (f:=γ) t
    rw [hγ] at htγ
    have htK : γ t∈range a∪range b := by
      rcases htγ with ((⟨s,_,he'⟩|hh)|⟨s,_,he'⟩)
      · exact Or.inl ⟨s,he'⟩
      · exact Or.inr hh
      · exact Or.inl ⟨s,he'⟩
    obtain ⟨s,hs,hse⟩ := hball (γ t) ⟨htK,ht⟩
    rcases htγ with ((⟨r,hr,he'⟩|⟨r,he'⟩)|⟨r,hr,he'⟩)
    · have hsr := a.injective (hse.trans he'.symm)
      subst r
      exact hs.2.not_ge hr.1
    · have hh := (hc s r (hse.trans he'.symm)).1
      rcases hh with hh|hh
      · exact (not_lt_of_ge (show (0:I) ≤ u from u.2.1)) (hh ▸ hs.1)
      · exact (not_lt_of_ge (show v ≤ (1:I) from v.2.2)) (hh ▸ hs.2)
    · have hsr := a.injective (hse.trans he'.symm)
      subst r
      exact hs.1.not_ge hr.2
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval

lemma isolated_chord_not_preconnected (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    {u v : I} (huv : u < v) {x c : ℂ} (hc₀ : c≠0) (hu : a u=x-c) (hv : a v=x+c)
    (he : a '' Icc u v=segment ℝ (a u) (a v))
    (hsmall : (range a ∪ range b)∩ball x ‖c‖ ⊆ a '' Icc u v) :
    ¬IsPreconnected (range a ∪ range b)ᶜ := by
  obtain ⟨γ,hγK,hγ⟩ := isolated_chord_closer a b hab₀ hab₁ hc huv hu hv he hsmall
  let L : ℂ ≃ₜ ℂ := (Homeomorph.addRight (-x)).trans
    (Homeomorph.mulRight₀ c⁻¹ (inv_ne_zero hc₀))
  have hL (z : ℂ) : L z=(z-x)/c := by rfl
  have hLu : L (a u)=-1 := by rw [hL,hu]; simp [sub_sub_cancel_left,hc₀]
  have hLv : L (a v)=1 := by rw [hL,hv]; simp [hc₀]
  let Γ : Path (1:ℂ) (-1) := (γ.map L.continuous).cast hLv.symm hLu.symm
  have hΓ (t : I) : 1 ≤ ‖Γ t‖ := by
    change 1 ≤ ‖L (γ t)‖
    rw [hL,norm_div]
    apply (le_div_iff₀ (norm_pos_iff.mpr hc₀)).mpr
    simpa only [one_mul,dist_eq_norm] using hγ t
  let N : ℂ →ᵃ[ℝ] ℂ := {
    toFun := fun z => (z-x)/c
    linear := {
      toFun := fun z => z/c
      map_add' := fun z w => add_div z w c
      map_smul' := fun r z => by simp only [Complex.real_smul, RingHom.id_apply]; ring }
    map_vadd' := fun z w => by change (w+z-x)/c=w/c+(z-x)/c; ring }
  have hseg : L '' segment ℝ (a u) (a v)=segment ℝ (-1:ℂ) 1 := by
    change N '' segment ℝ (a u) (a v)=_
    rw [image_segment ℝ N]
    change segment ℝ (L (a u)) (L (a v))=_
    rw [hLu,hLv]
  have hΓR : range Γ=L '' range γ := by
    change range (L ∘ γ)=_
    exact range_comp L γ
  let f := (Path.segment (-1:ℂ) 1).trans Γ
  have hfR : range f=L '' (range a∪range b) := by
    rw [show f=(Path.segment (-1:ℂ) 1).trans Γ from rfl,Path.trans_range,
      Path.range_segment,←hseg,hΓR,←image_union,←Path.range_segment,hγK]
  intro hconn
  have hconn' : IsPreconnected (range f)ᶜ := by
    rw [hfR,←L.image_compl]
    exact hconn.image L L.continuous.continuousOn
  obtain ⟨hp,hm,_⟩ := CannonWinding.chord_winding_jump Γ hΓ (1/2)
    (by norm_num) (by norm_num)
  exact CannonWinding.chord_separates Γ hΓ (1/2) (by norm_num) (by norm_num)
    (hconn'.subset_connectedComponentIn hp subset_rfl hm)

theorem pair_complement_not_preconnected (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ)) (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ¬IsPreconnected (range a ∪ range b)ᶜ := by
  obtain ⟨u,v,x,c,huv,hc₀,hu,hv,he,hs⟩ := pair_isolated_chord a b hab₀ hab₁ hc Q ha
  exact isolated_chord_not_preconnected a b hab₀ hab₁ hc huv hc₀ hu hv he hs
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem tame_pair_jordan (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ labels : Bool ≃ ConnectedComponents ((range a ∪ range b)ᶜ : Set ℂ),
      ∀ x∈range a ∪ range b,
        incident _ ConnectedComponents.mk x=range labels := by
  let K : Set ℂ := range a ∪ range b
  have hK : IsClosed K := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hK.isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (Kᶜ : Set ℂ)) := inferInstance
  obtain ⟨l,hls,hl⟩ := pair_labels_surjective a b hab₀ hab₁ hc Q ha hb
    (π:=ConnectedComponents.mk) ConnectedComponents.continuous_coe ConnectedComponents.surjective_coe
  have hne : l false ≠ l true := by
    intro he
    have hconst (s t : Bool) : l s=l t := by
      cases s <;> cases t
      · rfl
      · exact he
      · exact he.symm
      · rfl
    have hsub (d e : ConnectedComponents (Kᶜ : Set ℂ)) : d=e := by
      obtain ⟨s,rfl⟩ := hls d
      obtain ⟨t,rfl⟩ := hls e
      exact hconst s t
    have hconn : PreconnectedSpace (Kᶜ : Set ℂ) := by
      rw [preconnectedSpace_iff_connectedComponent]
      intro x
      apply eq_univ_of_forall
      intro y
      exact ConnectedComponents.coe_eq_coe'.mp (hsub _ _)
    exact pair_complement_not_preconnected a b hab₀ hab₁ hc Q ha
      (isPreconnected_iff_preconnectedSpace.mpr hconn)
  have hli : Function.Injective l := by
    intro s t h
    cases s <;> cases t
    · rfl
    · exact (hne h).elim
    · exact (hne h.symm).elim
    · rfl
  exact ⟨Equiv.ofBijective l ⟨hli,hls⟩,hl⟩
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_RadialStable
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonPolygonal
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polyJoined_of_preconnected_finite_segments (Q : Finset (E×E))
    (hK : IsPreconnected (⋃ q∈Q,segment ℝ q.1 q.2))
    {x y : E} (hx : x∈⋃ q∈Q,segment ℝ q.1 q.2)
    (hy : y∈⋃ q∈Q,segment ℝ q.1 q.2) :
    PolyJoined (⋃ q∈Q,segment ℝ q.1 q.2) x y := by
  classical
  let K := ⋃ q∈Q,segment ℝ q.1 q.2
  let V := ⋃ q∈Q.filter (fun q => PolyJoined K x q.1),segment ℝ q.1 q.2
  let W := ⋃ q∈Q.filter (fun q => ¬PolyJoined K x q.1),segment ℝ q.1 q.2
  have hseg (q : E×E) (hq : q∈Q) : segment ℝ q.1 q.2⊆K :=
    subset_iUnion₂_of_subset q hq Subset.rfl
  have hreach (q : E×E) (hq : q∈Q) {z : E} (hz : z∈segment ℝ q.1 q.2) :
      PolyJoined K x z ↔ PolyJoined K x q.1 := by
    constructor
    · intro h
      exact h.tail (((convex_segment q.1 q.2 : Convex ℝ _).segment_subset hz (left_mem_segment ..)).trans (hseg q hq))
    · intro h
      exact h.tail (((convex_segment q.1 q.2 : Convex ℝ _).segment_subset (left_mem_segment ..) hz).trans (hseg q hq))
  have hV (z : E) : z∈V ↔ z∈K ∧ PolyJoined K x z := by
    constructor
    · intro hz
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      obtain ⟨hq,hqr⟩ := Finset.mem_filter.mp hq
      exact ⟨hseg q hq hzq,(hreach q hq hzq).mpr hqr⟩
    · rintro ⟨hz,hr⟩
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,(hreach q hq hzq).mp hr⟩,hzq⟩
  have hW (z : E) : z∈W ↔ z∈K ∧ ¬PolyJoined K x z := by
    constructor
    · intro hz
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      obtain ⟨hq,hqr⟩ := Finset.mem_filter.mp hq
      exact ⟨hseg q hq hzq,fun h => hqr ((hreach q hq hzq).mp h)⟩
    · rintro ⟨hz,hr⟩
      obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
      exact mem_iUnion₂.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,fun h => hr ((hreach q hq hzq).mpr h)⟩,hzq⟩
  have hcV : IsClosed V := isClosed_biUnion_finset fun q _ => by
    have hh := (isCompact_range (Path.segment q.1 q.2).continuous).isClosed
    simpa only [Path.range_segment] using hh
  have hcW : IsClosed W := isClosed_biUnion_finset fun q _ => by
    have hh := (isCompact_range (Path.segment q.1 q.2).continuous).isClosed
    simpa only [Path.range_segment] using hh
  by_contra hn
  have hcover : K⊆V∪W := by
    intro z hz
    by_cases hr : PolyJoined K x z
    · exact Or.inl ((hV z).mpr ⟨hz,hr⟩)
    · exact Or.inr ((hW z).mpr ⟨hz,hr⟩)
  obtain ⟨z,hzK,hzV,hzW⟩ := isPreconnected_closed_iff.mp hK V W hcV hcW hcover
    ⟨x,hx,(hV x).mpr ⟨hx,.refl⟩⟩ ⟨y,hy,(hW y).mpr ⟨hy,hn⟩⟩
  exact ((hW z).mp hzW).2 ((hV z).mp hzV).2

theorem preconnected_finite_segments_arc (Q : Finset (E×E))
    (hK : IsPreconnected (⋃ q∈Q,segment ℝ q.1 q.2))
    {x y : E} (hx : x∈⋃ q∈Q,segment ℝ q.1 q.2)
    (hy : y∈⋃ q∈Q,segment ℝ q.1 q.2) (hne : x≠y) :
    ∃ a : CannonEmbeddedArc.Arc E, a 0=x ∧ a 1=y ∧
      range a⊆⋃ q∈Q,segment ℝ q.1 q.2 ∧ FiniteSupport (range a) :=
  polyJoined_arc (polyJoined_of_preconnected_finite_segments Q hK hx hy) hne
end CannonPolygonal

namespace CannonEmbeddedArc.Arc
open Set unitInterval CannonPolygonal CannonSegmentCones

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Finite ι]

theorem finite_graph_exact_segments (F : ι → Arc E)
    (Q : Finset (E×E)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2) :
    ∃ P : Finset (E×E), (⋃ i,range (F i))=⋃ p∈P,segment ℝ p.1 p.2 := by
  classical
  let _ := Fintype.ofFinite ι
  choose P hP₀ hP₁ hPs using fun i => finite_segment_arc_subdivision Q (F i) (hQ i)
  let R : Finset (E×E) := Finset.univ.biUnion fun i =>
    (segments (P i)).image (fun z => (F i z.1,F i z.2))
  refine ⟨R,?_⟩
  have he (i : ι) : range (F i)=⋃ z : segments (P i),
      segment ℝ (F i z.val.1) (F i z.val.2) := by
    rw [subdivision_cover (F i) (P i) (hP₀ i) (hP₁ i)]
    exact iUnion_congr fun z => hPs i z
  simp only [he]
  ext x
  constructor
  · intro hx
    obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
    obtain ⟨z,hz⟩ := mem_iUnion.mp hxi
    apply mem_iUnion₂.mpr
    refine ⟨(F i z.val.1,F i z.val.2),?_,hz⟩
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,
      Finset.mem_image.mpr ⟨z.val,z.property,rfl⟩⟩
  · intro hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨⟨z,hz⟩,hxp⟩⟩

end CannonEmbeddedArc.Arc
namespace CannonSegmentCones
open Set Metric Topology

lemma complex_segment_supporting_line (a b : ℂ) :
    ∃ f : ℂ →L[ℝ] ℝ, f≠0 ∧ segment ℝ a b⊆{x | f x=f a} := by
  let x₀ := Complex.reCLM
  let x₁ := Complex.imCLM
  by_cases hd : b.re=a.re
  · refine ⟨x₀,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : ℂ →L[ℝ] ℝ => f 1) h
      norm_num [x₀] at hh
    · exact ((convex_singleton (x₀ a)).linear_preimage x₀.toLinearMap).segment_subset rfl hd
  · let f := x₁-((b.im-a.im)/(b.re-a.re)) • x₀
    refine ⟨f,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : ℂ →L[ℝ] ℝ => f Complex.I) h
      norm_num [f,x₀,x₁] at hh
    · have hab : f b=f a := by
        change b.im-((b.im-a.im)/(b.re-a.re))*b.re=a.im-((b.im-a.im)/(b.re-a.re))*a.re
        have hn := sub_ne_zero.mpr hd
        field_simp [hn]
        ring
      exact ((convex_singleton (f a)).linear_preimage f.toLinearMap).segment_subset rfl hab

lemma complex_finite_segments_compl_dense (Q : Finset (ℂ × ℂ)) :
    Dense ((⋃ q∈Q,segment ℝ q.1 q.2)ᶜ : Set ℂ) := by
  classical
  choose f hf hfs using fun q : Q => complex_segment_supporting_line q.val.1 q.val.2
  have hsurj (q : Q) : Function.Surjective (f q) := by
    obtain ⟨v,hv⟩ : ∃ v, f q v≠0 := by
      by_contra hn
      push Not at hn
      apply hf q
      ext v
      exact hn v
    intro y
    refine ⟨(y/f q v) • v,?_⟩
    simp only [map_smul,smul_eq_mul]
    exact div_mul_cancel₀ y hv
  have hopen (q : Q) : IsOpen {x | f q x≠f q q.val.1} :=
    isOpen_compl_singleton.preimage (f q).continuous
  have hdense (q : Q) : Dense {x | f q x≠f q q.val.1} :=
    (dense_compl_singleton _).preimage ((f q).isOpenMap (hsurj q))
  have hd := dense_iInter_of_isOpen hopen hdense
  apply hd.mono
  intro z hz hzQ
  obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hzQ
  exact (mem_iInter.mp hz ⟨q,hq⟩) (hfs ⟨q,hq⟩ hzq)

end CannonSegmentCones

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_RegionEdges
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma interior_dense_interval : closure (Ioo (0:I) 1)=univ := by
  rw [closure_Ioo zero_ne_one]
  ext t
  simp only [mem_Icc,mem_univ,iff_true]
  exact ⟨t.property.1,t.property.2⟩

lemma range_in_closed_of_interior {X : Type*} [TopologicalSpace X] (a : Arc X)
    {S : Set X} (hS : IsClosed S) (hI : ∀ t : I, 0<t → t<1 → a t∈S) : range a⊆S := by
  have hs : closure (Ioo (0:I) 1)⊆a ⁻¹' S :=
    closure_minimal (fun t ht => hI t ht.1 ht.2) (hS.preimage a.continuous)
  rw [interior_dense_interval] at hs
  rintro x ⟨t,rfl⟩
  exact hs (mem_univ t)

lemma region_edge_in_closure (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    {π : ((⋃ j,range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π)
    {d : D} {i : ι} (hi : i∈regionEdges F π d) :
    range (F i)⊆closure (region _ π d) := by
  obtain ⟨s,hs₀,hs₁,hds⟩ := hi
  obtain ⟨labels,hlabels⟩ := tame_edge_incident_labels F hF Q hQ hπ i
  apply range_in_closed_of_interior (F i) isClosed_closure
  intro t ht₀ ht₁
  show d∈incident _ π (F i t)
  rwa [hlabels t ht₀ ht₁,←hlabels s hs₀ hs₁]

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_TameEdgeIncidenceOpen
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

lemma finite_segment_union (P Q : Finset (ℂ × ℂ)) :
    (⋃ p∈P∪Q,segment ℝ p.1 p.2)=(⋃ p∈P,segment ℝ p.1 p.2)∪(⋃ p∈Q,segment ℝ p.1 p.2) := by
  ext x
  simp only [mem_iUnion,Finset.mem_union,mem_union]
  constructor
  · rintro ⟨p,hp,hx⟩
    exact hp.elim (fun h => Or.inl ⟨p,h,hx⟩) (fun h => Or.inr ⟨p,h,hx⟩)
  · rintro (⟨p,hp,hx⟩|⟨p,hp,hx⟩)
    · exact ⟨p,Or.inl hp,hx⟩
    · exact ⟨p,Or.inr hp,hx⟩

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_VertexLines
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology CannonFaceIncidence CannonPolygonal

variable {ι : Type*} [Finite ι]

lemma mem_faceVertices (F : ι → Arc ℂ) (d : Faces F) (v : ℂ) :
    v∈faceVertices F d ↔ Vertex F v ∧ v∈closure (face F d) := by
  simp [faceVertices]

omit [Finite ι] in
lemma face_nonempty (F : ι → Arc ℂ) (d : Faces F) : (face F d).Nonempty :=
  (component_region_connected _ d).nonempty
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_LabelsConstant
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonClosedCover
open Set

variable {X D J : Type*} [TopologicalSpace X] [Finite J]

theorem labels_constant {S : Set X} (hS : IsPreconnected S) (C : J → Set X)
    (hC : ∀ j,IsClosed (C j)) (hcover : S⊆⋃ j,C j) (hne : ∀ j,(S∩C j).Nonempty)
    (l : J → D) (hcompat : ∀ x∈S,∀ i,x∈C i → ∀ j,x∈C j → l i=l j) :
    ∀ i j,l i=l j := by
  classical
  intro i j
  by_contra hij
  let A := ⋃ k∈{k | l k=l i},C k
  let B := ⋃ k∈{k | l k≠l i},C k
  have hA : IsClosed A := isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hC k
  have hB : IsClosed B := isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hC k
  have hAB : S⊆A∪B := by
    intro x hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover hx)
    by_cases h : l k=l i
    · exact Or.inl (mem_iUnion₂.mpr ⟨k,h,hk⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨k,h,hk⟩)
  obtain ⟨u,hu,huC⟩ := hne i
  obtain ⟨v,hv,hvC⟩ := hne j
  obtain ⟨x,hx,hxa,hxb⟩ := isPreconnected_closed_iff.mp hS A B hA hB hAB
    ⟨u,hu,mem_iUnion₂.mpr ⟨i,rfl,huC⟩⟩
    ⟨v,hv,mem_iUnion₂.mpr ⟨j,Ne.symm hij,hvC⟩⟩
  obtain ⟨k,hk,hkx⟩ := mem_iUnion₂.mp hxa
  obtain ⟨m,hm,hmx⟩ := mem_iUnion₂.mp hxb
  exact hm ((hcompat x hx m hmx k hkx).trans hk)
end CannonClosedCover

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FaceClosuresCover
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι]

theorem edge_interior_complement_preconnected (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j))) (e : ι)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) :
    IsPreconnected ((⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}) := by
  classical
  let R : Set ℂ := (⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}
  let m : I := ⟨1/2,by norm_num,by norm_num⟩
  have hm₀ : (0:I) < m := by change (0:ℝ)<1/2; norm_num
  have hm₁ : m < (1:I) := by change (1/2:ℝ)<1; norm_num
  let q := F e m
  let S : Set ℂ := (⋃ i,range (F i))\{q}
  have hR₀ : F e 0∈R := Or.inr (by simp)
  have hR₁ : F e 1∈R := Or.inr (by simp)
  have hRi (i : {i : ι // i≠e}) : range (F i.val)⊆R := fun z hz => Or.inl (mem_iUnion.mpr ⟨i,hz⟩)
  have hnot (i : {i : ι // i≠e}) : q∉range (F i.val) := by
    rintro ⟨t,ht⟩
    rcases ((hF i.property).1 t m ht).2 with h|h
    · exact hm₀.ne' h
    · exact hm₁.ne h
  have hRS : R⊆S := by
    rintro z (hz|hz)
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact ⟨mem_iUnion.mpr ⟨i.val,hzi⟩,fun he => hnot i (he ▸ hzi)⟩
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact ⟨mem_iUnion.mpr ⟨e,mem_range_self 0⟩,fun he => hm₀.ne ((F e).injective he)⟩
      · exact ⟨mem_iUnion.mpr ⟨e,mem_range_self 1⟩,fun he => hm₁.ne ((F e).injective he).symm⟩
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  let C : ({i : ι // i≠e}⊕Bool) → Set ℂ := Sum.elim (fun i => range (F i.val))
    (fun b => if b then F e '' Icc m (1:I) else F e '' Icc (0:I) m)
  let l : ({i : ι // i≠e}⊕Bool) → Bool := Sum.elim (fun i => f (F i.val 0))
    (fun b => if b then f (F e 1) else f (F e 0))
  have hclosed : ∀ j,IsClosed (C j) := by
    rintro (i|b)
    · exact (F i.val).compact_range.isClosed
    · cases b <;> exact (isCompact_Icc.image (F e).continuous).isClosed
  have hcover : S⊆⋃ j,C j := by
    rintro z ⟨hz,hzq⟩
    obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hz
    by_cases hi : i=e
    · subst i
      rcases le_total t m with ht|ht
      · exact mem_iUnion.mpr ⟨Sum.inr false,⟨t,⟨nonneg t,ht⟩,rfl⟩⟩
      · exact mem_iUnion.mpr ⟨Sum.inr true,⟨t,⟨ht,le_one t⟩,rfl⟩⟩
    · exact mem_iUnion.mpr ⟨Sum.inl ⟨i,hi⟩,mem_range_self t⟩
  have hne : ∀ j,(S∩C j).Nonempty := by
    rintro (i|b)
    · exact ⟨F i.val 0,hRS (hRi i (mem_range_self 0)),mem_range_self 0⟩
    · cases b
      · exact ⟨F e 0,hRS hR₀,⟨0,⟨le_rfl,hm₀.le⟩,rfl⟩⟩
      · exact ⟨F e 1,hRS hR₁,⟨1,⟨hm₁.le,le_rfl⟩,rfl⟩⟩
  have hlabel (i : {i : ι // i≠e}) {z : ℂ} (hz : z∈C (Sum.inl i)) :
      f z=l (Sum.inl i) :=
    (isPreconnected_range (F i.val).continuous).constant (hf.mono (hRi i)) hz (mem_range_self 0)
  have holdnew (i : {i : ι // i≠e}) (b : Bool) {z : ℂ}
      (hzi : z∈C (Sum.inl i)) (hzb : z∈C (Sum.inr b)) :
      l (Sum.inl i)=l (Sum.inr b) := by
    obtain ⟨s,rfl⟩ := hzi
    cases b
    · obtain ⟨t,ht,he⟩ := hzb
      have ht₀ : t=0 := ((hF i.property).1 s t he.symm).2.resolve_right
        (fun h => hm₁.not_ge (h ▸ ht.2))
      have hz : F i.val s=F e 0 := ht₀ ▸ he.symm
      exact (hlabel i (mem_range_self s)).symm.trans (congrArg f hz)
    · obtain ⟨t,ht,he⟩ := hzb
      have ht₁ : t=1 := ((hF i.property).1 s t he.symm).2.resolve_left
        (fun h => hm₀.not_ge (h ▸ ht.1))
      have hz : F i.val s=F e 1 := ht₁ ▸ he.symm
      exact (hlabel i (mem_range_self s)).symm.trans (congrArg f hz)
  have hall : ∀ i j,l i=l j := by
    apply CannonClosedCover.labels_constant (hK q) C hclosed hcover hne l
    intro z hz i hzi j hzj
    rcases i with i|b <;> rcases j with j|c
    · exact (hlabel i hzi).symm.trans (hlabel j hzj)
    · exact holdnew i c hzi hzj
    · exact (holdnew j b hzj hzi).symm
    · cases b <;> cases c
      · rfl
      · obtain ⟨s,hs,rfl⟩ := hzi
        obtain ⟨t,ht,he⟩ := hzj
        have hts := (F e).injective he
        have hsm : s=m := le_antisymm hs.2 (hts ▸ ht.1)
        exact (hz.2 (congrArg (F e) hsm)).elim
      · obtain ⟨s,hs,rfl⟩ := hzi
        obtain ⟨t,ht,he⟩ := hzj
        have hts := (F e).injective he
        have hsm : s=m := le_antisymm (hts ▸ ht.2) hs.1
        exact (hz.2 (congrArg (F e) hsm)).elim
      · rfl
  have hvalue {z : ℂ} (hz : z∈R) : f z=l (Sum.inr false) := by
    rcases hz with hz|hz
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact (hlabel i hzi).trans (hall _ _)
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · rfl
      · exact hall (Sum.inr true) _
  exact (hvalue hx).trans (hvalue hy).symm
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set unitInterval Topology Metric CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Finite ι]

theorem edge_on_tame_cycle (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (e : ι) :
    ∃ b : Arc ℂ,b 0=F e 0 ∧ b 1=F e 1 ∧
      range b⊆⋃ i,range (F i) ∧ FiniteSupport (range b) ∧
      ∀ s t,F e s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1) := by
  classical
  let R : Set ℂ := (⋃ i : {i : ι // i≠e},range (F i.val))∪{F e 0,F e 1}
  have hR : IsPreconnected R := edge_interior_complement_preconnected F hF e hK
  obtain ⟨P,hP⟩ := finite_graph_exact_segments (fun i : {i : ι // i≠e} => F i.val) Q (fun i => hQ i.val)
  let T := P∪{(F e 0,F e 0),(F e 1,F e 1)}
  have hT : R=⋃ p∈T,segment ℝ p.1 p.2 := by
    rw [finite_segment_union,←hP]
    apply congrArg (fun S : Set ℂ => (⋃ i : {i : ι // i≠e},range (F i.val))∪S)
    ext z
    constructor
    · intro hz
      rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact mem_iUnion₂.mpr ⟨(F e 0,F e 0),Finset.mem_insert_self ..,left_mem_segment ..⟩
      · exact mem_iUnion₂.mpr ⟨(F e 1,F e 1),Finset.mem_insert_of_mem (Finset.mem_singleton_self _),left_mem_segment ..⟩
    · intro hz
      obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
      rcases Finset.mem_insert.mp hp with rfl|hp
      · exact Or.inl (by simpa only [segment_same,mem_singleton_iff] using hz)
      · have hp' := Finset.mem_singleton.mp hp
        subst p
        exact Or.inr (by simpa only [segment_same,mem_singleton_iff] using hz)
  obtain ⟨b,hb₀,hb₁,hbT,hbS⟩ := preconnected_finite_segments_arc T (hT ▸ hR)
    (hT ▸ (show F e 0∈R from Or.inr (by simp)))
    (hT ▸ (show F e 1∈R from Or.inr (by simp))) (F e).endpoints_ne
  have hbR : range b⊆R := by rwa [←hT] at hbT
  have hRK : R⊆⋃ i,range (F i) := by
    rintro z (hz|hz)
    · obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨i.val,hzi⟩
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z=F e 0 ∨ z=F e 1) with rfl|rfl
      · exact mem_iUnion.mpr ⟨e,mem_range_self 0⟩
      · exact mem_iUnion.mpr ⟨e,mem_range_self 1⟩
  refine ⟨b,hb₀,hb₁,hbR.trans hRK,hbS,?_⟩
  intro s t he
  have hs : s=0 ∨ s=1 := by
    have hbs : F e s∈R := he.symm ▸ hbR (mem_range_self t)
    rcases hbs with hbs|hbs
    · obtain ⟨i,u,hu⟩ := mem_iUnion.mp hbs
      exact ((hF i.property).1 u s hu).2
    · rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hbs : F e s=F e 0 ∨ F e s=F e 1) with h|h
      · exact Or.inl ((F e).injective h)
      · exact Or.inr ((F e).injective h)
  refine ⟨hs,?_⟩
  rcases hs with rfl|rfl
  · exact Or.inl (b.injective (he.symm.trans hb₀.symm))
  · exact Or.inr (b.injective (he.symm.trans hb₁.symm))
end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_TamePairJordanRegions
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

theorem tame_pair_jordan_regions (a b : Arc ℂ) (hab₀ : a 0=b 0) (hab₁ : a 1=b 1)
    (hc : ∀ s t, a s=b t → (s=0 ∨ s=1) ∧ (t=0 ∨ t=1))
    (Q : Finset (ℂ × ℂ))
    (ha : range a ⊆ ⋃ q∈Q, segment ℝ q.1 q.2)
    (hb : range b ⊆ ⋃ q∈Q, segment ℝ q.1 q.2) :
    ∃ R : Bool → Set ℂ,
      (∀ i, IsOpen (R i) ∧ IsConnected (R i) ∧
        closure (R i)=R i ∪ (range a∪range b) ∧ frontier (R i)=range a∪range b) ∧
      Disjoint (R false) (R true) ∧ R false∪R true=(range a∪range b)ᶜ := by
  let K : Set ℂ := range a∪range b
  have hK : IsClosed K := a.compact_range.isClosed.union b.compact_range.isClosed
  let _ : LocallyConnectedSpace (Kᶜ : Set ℂ) := hK.isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (Kᶜ : Set ℂ)) := inferInstance
  obtain ⟨l,hl⟩ := tame_pair_jordan a b hab₀ hab₁ hc Q ha hb
  let R := fun i => region Kᶜ ConnectedComponents.mk (l i)
  have hRsub (i) : R i⊆Kᶜ := region_subset _ _ _
  have hRclose (i) : closure (R i)=R i∪K := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxK : x∈K
      · exact Or.inr hxK
      · exact Or.inl (closure_region_inside hK.isOpen_compl ConnectedComponents.continuous_coe hx hxK)
    · apply union_subset subset_closure
      intro x hx
      show l i∈incident _ ConnectedComponents.mk x
      rw [hl x hx]
      exact mem_range_self i
  refine ⟨R,fun i => ⟨region_isOpen hK.isOpen_compl ConnectedComponents.continuous_coe _,
    component_region_connected _ _,hRclose i,?_⟩,
    component_regions_disjoint _ (l.injective.ne (by decide)),?_⟩
  · rw [frontier, (region_isOpen hK.isOpen_compl ConnectedComponents.continuous_coe (l i)).interior_eq,
      hRclose i]
    ext x
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hx,hn⟩
      exact hx.resolve_left hn
    · intro hx
      exact ⟨Or.inr hx,fun h => hRsub i h hx⟩
  · apply Subset.antisymm (union_subset (hRsub false) (hRsub true))
    intro x hx
    obtain ⟨i,hi⟩ := l.surjective (ConnectedComponents.mk ⟨x,hx⟩)
    cases i
    · exact Or.inl ⟨hx,hi.symm⟩
    · exact Or.inr ⟨hx,hi.symm⟩

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_NoncutEdgeTwoFaces
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal CannonSegmentCones

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem noncut_edge_two_faces (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (e : ι) :
    ∃ d₀ d₁ : Faces F,d₀≠d₁ ∧ e∈regionEdges F ConnectedComponents.mk d₀ ∧
      e∈regionEdges F ConnectedComponents.mk d₁ := by
  classical
  let K := ⋃ i,range (F i)
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  obtain ⟨b,hb₀,hb₁,hbK,⟨P,hP⟩,hab⟩ := edge_on_tame_cycle F hF Q hQ hK e
  have ha' : range (F e)⊆⋃q∈Q∪P,segment ℝ q.1 q.2 := by
    intro z hz
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp (hQ e hz)
    exact mem_iUnion₂.mpr ⟨q,Finset.mem_union_left P hq,hzq⟩
  have hb' : range b⊆⋃q∈Q∪P,segment ℝ q.1 q.2 := by
    intro z hz
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp (hP hz)
    exact mem_iUnion₂.mpr ⟨q,Finset.mem_union_right Q hq,hzq⟩
  obtain ⟨R,hR,hdis,hcov⟩ := tame_pair_jordan_regions (F e) b hb₀.symm hb₁.symm hab (Q∪P) ha' hb'
  have hsub (d : Faces F) : face F d⊆R false ∨ face F d⊆R true := by
    apply (component_region_connected Kᶜ d).isPreconnected.subset_or_subset (hR false).1 (hR true).1 hdis
    rw [hcov]
    intro z hz hh
    exact hz.1 (hh.elim (fun h=>mem_iUnion.mpr ⟨e,h⟩) (fun h=>hbK h))
  have hkey (i : Bool) {z : ℂ} (hz : z∈R i) (hzK : z∉K) :
      face F (ConnectedComponents.mk ⟨z,hzK⟩)⊆R i := by
    have hzF : z∈face F (ConnectedComponents.mk ⟨z,hzK⟩) := ⟨hzK,rfl⟩
    rcases hsub (ConnectedComponents.mk ⟨z,hzK⟩) with hh|hh
    · cases i
      · exact hh
      · exact False.elim (disjoint_left.mp hdis (hh hzF) hz)
    · cases i
      · exact False.elim (disjoint_left.mp hdis hz (hh hzF))
      · exact hh
  let t : I := ⟨1/2,by constructor <;> norm_num⟩
  have ht₀ : (0:I)<t := by change (0:ℝ)<1/2; norm_num
  have ht₁ : t<(1:I) := by change (1/2:ℝ)<1; norm_num
  have hfind (i : Bool) : ∃ d : Faces F,face F d⊆R i ∧ F e t∈closure (face F d) := by
    let B : Set (Faces F) := {d | face F d⊆R i}
    let T := ⋃ d∈B,closure (face F d)
    have hT : IsClosed T := isClosed_iUnion_of_finite fun d=>isClosed_iUnion_of_finite fun _=>isClosed_closure
    have hd : Dense (Kᶜ : Set ℂ) :=
      (complex_finite_segments_compl_dense Q).mono (compl_subset_compl.mpr (iUnion_subset hQ))
    have hinc : R i∩Kᶜ⊆T := by
      intro z hz
      exact mem_iUnion₂.mpr ⟨ConnectedComponents.mk ⟨z,hz.2⟩,hkey i hz.1 hz.2,subset_closure ⟨hz.2,rfl⟩⟩
    have hRT : R i⊆T := by
      intro z hz
      exact closure_minimal hinc hT ((hR i).1.inter_closure ⟨hz,hd z⟩)
    have hx : F e t∈closure (R i) := by
      rw [(hR i).2.2.1]
      exact Or.inr (Or.inl (mem_range_self t))
    obtain ⟨d,hd,hx⟩ := mem_iUnion₂.mp (closure_minimal hRT hT hx)
    exact ⟨d,hd,hx⟩
  obtain ⟨d₀,hd₀,hx₀⟩ := hfind false
  obtain ⟨d₁,hd₁,hx₁⟩ := hfind true
  refine ⟨d₀,d₁,?_,⟨t,ht₀,ht₁,hx₀⟩,⟨t,ht₀,ht₁,hx₁⟩⟩
  intro he
  obtain ⟨z,hz⟩ := face_nonempty F d₀
  exact disjoint_left.mp hdis (hd₀ hz) (hd₁ (he ▸ hz))

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_Crossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set

attribute [local instance] Classical.propDecidable

lemma crossing_neg (y z A : ℝ) : crossing z y (-A)= -crossing y z A := by
  unfold crossing
  simp only [neg_pos,neg_lt_zero]
  have hdis : ¬((y<0 ∧ 0<z ∧ 0<A) ∧ (z<0 ∧ 0<y ∧ A<0)) := by
    rintro ⟨h,k⟩
    exact lt_asymm h.1 k.2.1
  by_cases h : y<0 ∧ 0<z ∧ 0<A
  · have k : ¬(z<0 ∧ 0<y ∧ A<0) := fun k=>hdis ⟨h,k⟩
    simp only [ite_eq_left h,ite_eq_right k]
  · by_cases k : z<0 ∧ 0<y ∧ A<0 <;> simp only [h,k,and_self,ite_false,ite_true,neg_zero,neg_neg]

lemma positive_triangle_degree {y z w A B C : ℝ}
    (hy : y≠0) (hz : z≠0) (hw : w≠0) (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (hp : 0<A+B+C) (hr : y*B+z*C+w*A=0) :
    crossing y z A+crossing z w B+crossing w y C=
      if 0<A ∧ 0<B ∧ 0<C then 1 else 0 := by
  rcases lt_or_gt_of_ne hy with hy|hy <;>
    rcases lt_or_gt_of_ne hz with hz|hz <;>
    rcases lt_or_gt_of_ne hw with hw|hw <;>
    rcases lt_or_gt_of_ne hA with hA|hA <;>
    rcases lt_or_gt_of_ne hB with hB|hB <;>
    rcases lt_or_gt_of_ne hC with hC|hC <;>
    (have hy' := lt_asymm hy
     have hz' := lt_asymm hz
     have hw' := lt_asymm hw
     have hA' := lt_asymm hA
     have hB' := lt_asymm hB
     have hC' := lt_asymm hC
     simp only [crossing,hy,hz,hw,hA,hB,hC,hy',hz',hw',hA',hB',hC',
       and_self,and_true,and_false,ite_true,ite_false]
     norm_num)
  all_goals
    first
    | have h1 := mul_pos hy hB
    | have h1 := mul_pos_of_neg_of_neg hy hB
    | have h1 := mul_neg_of_neg_of_pos hy hB
    | have h1 := mul_neg_of_pos_of_neg hy hB
    first
    | have h2 := mul_pos hz hC
    | have h2 := mul_pos_of_neg_of_neg hz hC
    | have h2 := mul_neg_of_neg_of_pos hz hC
    | have h2 := mul_neg_of_pos_of_neg hz hC
    first
    | have h3 := mul_pos hw hA
    | have h3 := mul_pos_of_neg_of_neg hw hA
    | have h3 := mul_neg_of_neg_of_pos hw hA
    | have h3 := mul_neg_of_pos_of_neg hw hA
    linarith

lemma area_swap (a b p : ℂ) : area b a p= -area a b p := by
  unfold area
  ring
lemma area_cyclic (a b c : ℂ) : area b c a=area a b c := by
  unfold area
  ring
lemma area_sum (a b c p : ℂ) : area a b p+area b c p+area c a p=area a b c := by
  unfold area
  ring
lemma area_relation (a b c p : ℂ) :
    (a.im-p.im)*area b c p+(b.im-p.im)*area c a p+(c.im-p.im)*area a b p=0 := by
  unfold area
  ring

lemma edgeIndex_swap (p a b : ℂ) : edgeIndex p b a= -edgeIndex p a b := by
  unfold edgeIndex
  rw [area_swap,crossing_neg]

lemma triangle_index {a b c p : ℂ} (harea : 0<area a b c) (hgen : Generic a b c p) :
    edgeIndex p a b+edgeIndex p b c+edgeIndex p c a=if Inside a b c p then 1 else 0 := by
  have ht := positive_triangle_degree (sub_ne_zero.mpr hgen.1) (sub_ne_zero.mpr hgen.2.1)
    (sub_ne_zero.mpr hgen.2.2.1) hgen.2.2.2.1 hgen.2.2.2.2.1 hgen.2.2.2.2.2
    (by rw [area_sum]; exact harea) (area_relation a b c p)
  by_cases h : Inside a b c p
  · rw [ite_eq_left h]
    change 0<area a b p ∧ 0<area b c p ∧ 0<area c a p at h
    rw [ite_eq_left h] at ht
    exact ht
  · rw [ite_eq_right h]
    change ¬(0<area a b p ∧ 0<area b c p ∧ 0<area c a p) at h
    rw [ite_eq_right h] at ht
    exact ht

lemma inside_open (a b c : ℂ) : IsOpen {p | Inside a b c p} := by
  have H (a b : ℂ) : Continuous (area a b) := by unfold area; fun_prop
  exact (isOpen_lt continuous_const (H a b)).inter
    ((isOpen_lt continuous_const (H b c)).inter (isOpen_lt continuous_const (H c a)))

end CannonTriangleWinding

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {F : ι → Arc ℂ} {d : Faces F}

omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.mem_a (C : FacialCycle F d) : C.a∈faceVertices F d := by rw [C.vertices]; simp
omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.mem_b (C : FacialCycle F d) : C.b∈faceVertices F d := by rw [C.vertices]; simp
omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.mem_c (C : FacialCycle F d) : C.c∈faceVertices F d := by rw [C.vertices]; simp

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_InnerFlux
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set Topology

lemma dense_ne_of_openMap {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (hf : IsOpenMap f) (t : ℝ) : Dense {x | f x≠t} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨y,hy,ht⟩ := (dense_compl_singleton t).inter_open_nonempty (f '' U)
    (hf U hU) (hne.image f)
  obtain ⟨x,hx,rfl⟩ := hy
  exact ⟨x,hx,ht⟩

lemma area_openMap {a b : ℂ} (hab : a≠b) : IsOpenMap (area a b) := by
  let L : ℂ →L[ℝ] ℝ := (b.re-a.re) • Complex.imCLM-(b.im-a.im) • Complex.reCLM
  have hL (p : ℂ) : L p=(b.re-a.re)*p.im-(b.im-a.im)*p.re := rfl
  have hsurj : Function.Surjective L := by
    intro t
    by_cases h : b.re-a.re=0
    · have h' : b.im-a.im≠0 := by
        intro hh
        exact hab (Complex.ext (sub_eq_zero.mp h).symm (sub_eq_zero.mp hh).symm)
      refine ⟨⟨-t/(b.im-a.im),0⟩,?_⟩
      rw [hL]
      simp only [h,zero_mul,zero_sub]
      field_simp
    · refine ⟨⟨0,t/(b.re-a.re)⟩,?_⟩
      rw [hL]
      simp only [mul_zero,sub_zero]
      exact mul_div_cancel₀ _ h
  have ho : IsOpenMap (fun p : ℂ=>p-a) := isOpenMap_sub_right a
  exact (L.isOpenMap hsurj).comp ho

lemma generic_dense_open (a b c : ℂ) (hab : a≠b) (hbc : b≠c) (hca : c≠a) :
    Dense {p | Generic a b c p} ∧ IsOpen {p | Generic a b c p} := by
  have hd (x : ℂ) : Dense {p : ℂ | x.im≠p.im} := by
    simpa only [ne_comm] using dense_ne_of_openMap Complex.im Complex.isOpenMap_im x.im
  have he (x y : ℂ) (hxy : x≠y) : Dense {p | area x y p≠0} :=
    dense_ne_of_openMap (area x y) (area_openMap hxy) 0
  have ho (x : ℂ) : IsOpen {p : ℂ | x.im≠p.im} := isOpen_ne_fun continuous_const Complex.continuous_im
  have hp (x y : ℂ) : IsOpen {p | area x y p≠0} := by
    apply isOpen_ne_fun _ continuous_const
    unfold area
    fun_prop
  have Hr := ((he a b hab).inter_of_isOpen_right
    ((he b c hbc).inter_of_isOpen_right (he c a hca) (hp c a)) ((hp b c).inter (hp c a)))
  have HrO := (hp a b).inter ((hp b c).inter (hp c a))
  have Hq := (hd c).inter_of_isOpen_right Hr HrO
  have HqO := (ho c).inter HrO
  have HH := (hd b).inter_of_isOpen_right Hq HqO
  have HHO := (ho b).inter HqO
  exact ⟨(hd a).inter_of_isOpen_right HH HHO,(ho a).inter HHO⟩

lemma area_pos_distinct {a b c : ℂ} (h : 0<area a b c) : a≠b ∧ b≠c ∧ c≠a := by
  constructor
  · intro he; subst b; simp [area] at h
  constructor
  · intro he; subst c; have : area a b b=0 := by unfold area; ring
    rw [this] at h; exact lt_irrefl _ h
  · intro he; subst c; simp [area] at h

end CannonTriangleWinding

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_InteriorBallCover
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set Topology

attribute [local instance] Classical.propDecidable

lemma generic_union_iff {D : Type*} [Fintype D] (a b c : D → ℂ) (u v w p : ℂ)
    (hpos : ∀ d,0<area (a d) (b d) (c d)) (ho : 0<area u v w)
    (hg : ∀ d,Generic (a d) (b d) (c d) p) (hgo : Generic u v w p)
    (hc : ∀ f : ℂ → ℂ → ℤ,(∀ x y,f y x= -f x y) →
      (∑ d : D,(f (a d) (b d)+f (b d) (c d)+f (c d) (a d)))=f u v+f v w+f w u) :
    (∃ d,Inside (a d) (b d) (c d) p) ↔ Inside u v w p := by
  classical
  have H := hc (edgeIndex p) (edgeIndex_swap p)
  simp only [triangle_index (hpos _) (hg _),triangle_index ho hgo] at H
  constructor
  · rintro ⟨d,hd⟩
    have hl : (1:ℤ)≤∑ i,if Inside (a i) (b i) (c i) p then (1:ℤ) else 0 := by
      have hh := Finset.single_le_sum (f:=fun i=>if Inside (a i) (b i) (c i) p then (1:ℤ) else 0)
        (fun i hi=>by split_ifs <;> norm_num) (Finset.mem_univ d)
      simpa only [ite_eq_left hd] using hh
    rw [H] at hl
    by_contra hn
    simp only [ite_eq_right hn] at hl
    norm_num at hl
  · intro hp
    by_contra hn
    push Not at hn
    simp only [ite_eq_right (hn _),Finset.sum_const_zero,ite_eq_left hp] at H
    norm_num at H

lemma closure_eq_of_dense_inter_eq {X : Type*} [TopologicalSpace X]
    {G U V : Set X} (hG : Dense G) (hU : IsOpen U) (hV : IsOpen V) (hUV : G∩U=G∩V) :
    closure U=closure V := by
  apply le_antisymm
  · apply closure_minimal ?_ isClosed_closure
    exact (hG.open_subset_closure_inter hU).trans (by rw [Set.inter_comm U G,hUV]; exact closure_mono inter_subset_right)
  · apply closure_minimal ?_ isClosed_closure
    exact (hG.open_subset_closure_inter hV).trans (by rw [Set.inter_comm V G,←hUV]; exact closure_mono inter_subset_right)

theorem triangle_closures_fill {D : Type*} [Fintype D] (a b c : D → ℂ) (u v w : ℂ)
    (hpos : ∀ d,0<area (a d) (b d) (c d)) (ho : 0<area u v w)
    (hchain : ∀ f : ℂ → ℂ → ℤ,(∀ x y,f y x= -f x y) →
      (∑ d : D,(f (a d) (b d)+f (b d) (c d)+f (c d) (a d)))=f u v+f v w+f w u) :
    (⋃ d,closure {p | Inside (a d) (b d) (c d) p})=closure {p | Inside u v w p} := by
  have hg (d : D) := generic_dense_open (a d) (b d) (c d)
    (area_pos_distinct (hpos d)).1 (area_pos_distinct (hpos d)).2.1 (area_pos_distinct (hpos d)).2.2
  have hgO := generic_dense_open u v w (area_pos_distinct ho).1
    (area_pos_distinct ho).2.1 (area_pos_distinct ho).2.2
  let G := (⋂ d : D,{p | Generic (a d) (b d) (c d) p})∩{p | Generic u v w p}
  have hG : Dense G :=
    (dense_iInter_of_isOpen (fun d=>(hg d).2) (fun d=>(hg d).1)).inter_of_isOpen_right hgO.1 hgO.2
  rw [←closure_iUnion_of_finite]
  apply closure_eq_of_dense_inter_eq hG (isOpen_iUnion fun d=>inside_open _ _ _) (inside_open _ _ _)
  ext p
  change (p∈G ∧ p∈⋃ d,{p | Inside (a d) (b d) (c d) p}) ↔ p∈G ∧ Inside u v w p
  simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
  apply and_congr_right
  intro hp
  exact generic_union_iff a b c u v w p hpos ho (fun d=>mem_iInter.mp hp.1 d) hp.2 hchain

end CannonTriangleWinding

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_ClosedInside
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set Metric Topology

lemma area_combo (a b x y : ℂ) (s t : ℝ) (hst : s+t=1) :
    area a b (s • x+t • y)=s*area a b x+t*area a b y := by
  have ht : t=1-s := by linarith
  subst t
  simp only [area,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

lemma closedInside_convex (a b c : ℂ) : Convex ℝ {p | ClosedInside a b c p} := by
  intro x hx y hy s t hs ht hst
  change 0≤area a b (s • x+t • y) ∧ 0≤area b c (s • x+t • y) ∧ 0≤area c a (s • x+t • y)
  rw [area_combo _ _ _ _ _ _ hst,area_combo _ _ _ _ _ _ hst,area_combo _ _ _ _ _ _ hst]
  exact ⟨add_nonneg (mul_nonneg hs hx.1) (mul_nonneg ht hy.1),
    add_nonneg (mul_nonneg hs hx.2.1) (mul_nonneg ht hy.2.1),
    add_nonneg (mul_nonneg hs hx.2.2) (mul_nonneg ht hy.2.2)⟩
lemma area_barycentric (a b c p : ℂ) (h : area a b c≠0) :
    (area b c p/area a b c) • a+(area c a p/area a b c) • b+(area a b p/area a b c) • c=p := by
  apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  · field_simp
    simp only [area]
    ring
  · field_simp
    simp only [area]
    ring

lemma convexHull_eq_closedInside {a b c : ℂ} (h : 0<area a b c) :
    convexHull ℝ ({a,b,c}:Set ℂ)={p | ClosedInside a b c p} := by
  apply Subset.antisymm
  · apply convexHull_min _ (closedInside_convex a b c)
    have az (x y : ℂ) : area x y x=0 := by simp [area]
    have bz (x y : ℂ) : area x y y=0 := by unfold area; ring
    have ha : ClosedInside a b c a := ⟨by rw [az],by rw [area_cyclic]; exact h.le,by rw [bz]⟩
    have hb : ClosedInside a b c b := ⟨by rw [bz],by rw [az],by rw [area_cyclic,area_cyclic]; exact h.le⟩
    have hc : ClosedInside a b c c := ⟨h.le,by rw [bz],by rw [az]⟩
    rintro p (rfl|rfl|rfl) <;> assumption
  · intro p hp
    let w : Fin 3 → ℝ := ![area b c p/area a b c,area c a p/area a b c,area a b p/area a b c]
    let v : Fin 3 → ℂ := ![a,b,c]
    apply mem_convexHull_of_exists_fintype w v
    · intro i
      fin_cases i
      · exact div_nonneg hp.2.1 h.le
      · exact div_nonneg hp.2.2 h.le
      · exact div_nonneg hp.1 h.le
    · simp only [w,Fin.sum_univ_three]
      change area b c p/area a b c+area c a p/area a b c+area a b p/area a b c=1
      rw [←add_div,←add_div]
      have hs := area_sum a b c p
      convert div_self h.ne' using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      linarith
    · intro i
      fin_cases i <;> simp [v]
    · simp only [w,v,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
      exact area_barycentric a b c p h.ne'

lemma convexHull_interior_nonempty {a b c : ℂ} (h : 0<area a b c) :
    (interior (convexHull ℝ ({a,b,c}:Set ℂ))).Nonempty := by
  have hsub : {p | Inside a b c p}⊆convexHull ℝ ({a,b,c}:Set ℂ) := by
    rw [convexHull_eq_closedInside h]
    exact fun p hp=>⟨hp.1.le,hp.2.1.le,hp.2.2.le⟩
  have hmean (x y z : ℂ) : area x y ((3:ℝ)⁻¹ • (x+y+z))=area x y z/3 := by
    simp only [area,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
    ring
  have hcent : Inside a b c ((3:ℝ)⁻¹ • (a+b+c)) := by
    constructor
    · rw [hmean]; positivity
    constructor
    · have he : a+b+c=b+c+a := by ring
      rw [he,hmean,area_cyclic]
      positivity
    · have he : a+b+c=c+a+b := by ring
      rw [he,hmean,area_cyclic,area_cyclic]
      positivity
  exact ⟨_,(interior_mono hsub) (by rw [(inside_open a b c).interior_eq]; exact hcent)⟩

lemma area_isOpenMap {a b c : ℂ} (h : 0<area a b c) : IsOpenMap (area a b) := by
  let L : ℂ →L[ℝ] ℝ := (b.re-a.re) • Complex.imCLM-(b.im-a.im) • Complex.reCLM
  have hL : Function.Surjective L := by
    intro y
    refine ⟨(y / area a b c) • (c-a),?_⟩
    rw [map_smul]
    have he : L (c-a)=area a b c := by simp [L,area]
    rw [he,smul_eq_mul,div_mul_cancel₀ _ h.ne']
  have he : area a b=fun p=>L (p-a) := by
    funext p
    simp [L,area]
  rw [he]
  exact (L.isOpenMap hL).comp (Homeomorph.subRight a).isOpenMap

lemma area_continuous (a b : ℂ) : Continuous (area a b) := by
  unfold area
  fun_prop

lemma convexHull_interior {a b c : ℂ} (h : 0<area a b c) :
    interior (convexHull ℝ ({a,b,c}:Set ℂ))={p | Inside a b c p} := by
  have h1 := (area_isOpenMap h).preimage_interior_eq_interior_preimage (area_continuous a b) (Ici 0)
  have hb : 0<area b c a := by simpa only [area_cyclic] using h
  have hc : 0<area c a b := by simpa only [area_cyclic] using h
  have h2 := (area_isOpenMap hb).preimage_interior_eq_interior_preimage (area_continuous b c) (Ici 0)
  have h3 := (area_isOpenMap hc).preimage_interior_eq_interior_preimage (area_continuous c a) (Ici 0)
  rw [interior_Ici] at h1 h2 h3
  rw [convexHull_eq_closedInside h]
  change interior ((area a b ⁻¹' Ici 0)∩((area b c ⁻¹' Ici 0)∩(area c a ⁻¹' Ici 0)))=_
  rw [interior_inter,interior_inter,←h1,←h2,←h3]
  ext p
  simp only [mem_inter_iff,mem_preimage,mem_Ioi,mem_ofPred_eq,Inside]

lemma convexHull_closure_inside {a b c : ℂ} (h : 0<area a b c) :
    closure {p | Inside a b c p}=convexHull ℝ ({a,b,c}:Set ℂ) := by
  rw [←convexHull_interior h]
  rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior (convexHull_interior_nonempty h)]
  have hc : IsClosed (convexHull ℝ ({a,b,c}:Set ℂ)) := by
    rw [convexHull_eq_closedInside h]
    exact (isClosed_le continuous_const (area_continuous a b)).inter
      ((isClosed_le continuous_const (area_continuous b c)).inter
        (isClosed_le continuous_const (area_continuous c a)))
  exact hc.closure_eq

end CannonTriangleWinding

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence CannonTriangleWinding
open scoped OnePoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} {d : Faces F}

omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.hull_eq (C : FacialCycle F d) (z : ℂ → ℂ) :
    faceHull F z d=convexHull ℝ ({z C.a,z C.b,z C.c}:Set ℂ) := by
  unfold faceHull
  rw [C.vertices]
  simp only [Finset.coe_insert,Finset.coe_singleton,image_insert_eq,image_singleton]

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_ClosedInsideSegment
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
omit [DecidableEq ι] [Fintype (Faces F)] in
lemma vertex_inner_face
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    {v : ℂ} (hvV : Vertex F v) : ∃ d:Faces F,d≠out ∧ v∈faceVertices F d := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  obtain ⟨i,hi⟩ := hvV
  have hv : v∈range (F i) := hi.elim (fun h=>h ▸ ⟨0,rfl⟩) (fun h=>h ▸ ⟨1,rfl⟩)
  obtain ⟨a,b,hab,ha,hb⟩ := noncut_edge_two_faces F hF Q hQ hK i
  have mem (d : Faces F) (hd : i∈regionEdges F ConnectedComponents.mk d) : v∈faceVertices F d :=
    (mem_faceVertices F _ _).mpr ⟨⟨i,hi⟩,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hd hv⟩
  by_cases hao : a=out
  · exact ⟨b,fun h=>hab (hao.trans h.symm),mem b hb⟩
  · exact ⟨a,hao,mem a ha⟩

theorem DevelopedFaces.hull_geometry_oai (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (hthree : ∀ d,(faceVertices F d).card=3)
    (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) :
    (∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c)) ∧
    (∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e))) ∧
    (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out := by
  classical
  obtain ⟨w,C,O,hw,hlen,hpos,ho,hchain,hdis⟩:=B.univalent_triangles hF Q hQ hK hthree
  have heq (v : ℂ) (hv : Vertex F v) : z v=w v := by
    obtain ⟨d,hd,hm⟩:=vertex_inner_face hF Q hQ hK hv
    exact (hz d hd v hm).trans (hw d hd v hm).symm
  have heqV (d : Faces F) (v : ℂ) (hv : v∈faceVertices F d) : z v=w v:=
    heq v ((mem_faceVertices F d v).mp hv).1
  have hhull (d : Faces F) : faceHull F z d=faceHull F w d := by
    unfold faceHull
    congr 1
    exact Set.image_congr (fun x hx=>heqV d x hx)
  have hcycle (d : Faces F) (C : FacialCycle F d) :
      area (z C.a) (z C.b) (z C.c)=area (w C.a) (w C.b) (w C.c) := by
    rw [heqV d C.a C.mem_a,heqV d C.b C.mem_b,heqV d C.c C.mem_c]
  refine ⟨?_,?_,?_⟩
  · intro d
    by_cases hd : d=out
    · subst d
      exact ⟨O,by rw [hcycle]; exact ho⟩
    · exact ⟨C ⟨d,hd⟩,by rw [hcycle]; exact hpos ⟨d,hd⟩⟩
  · intro d e hd he hde
    rw [hhull,hhull,(C ⟨d,hd⟩).hull_eq,(C ⟨e,he⟩).hull_eq,
      convexHull_interior (hpos ⟨d,hd⟩),convexHull_interior (hpos ⟨e,he⟩)]
    exact hdis (show (⟨d,hd⟩:{d : Faces F // d≠out})≠⟨e,he⟩ from fun h=>hde (congrArg Subtype.val h))
  · simp_rw [hhull]
    have H:=triangle_closures_fill (fun d=>w (C d).a) (fun d=>w (C d).b) (fun d=>w (C d).c)
      (w O.a) (w O.b) (w O.c) hpos ho (hchain ℤ)
    simp only [convexHull_closure_inside (hpos _),convexHull_closure_inside ho] at H
    simp_rw [(C _).hull_eq,O.hull_eq]
    exact H
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CannonEmbeddedArc.Arc.DevelopedFaces.hull_geometry_oai.{u_1} := @OAI.CannonEmbeddedArc.Arc.DevelopedFaces.hull_geometry_oai.{u_1}
