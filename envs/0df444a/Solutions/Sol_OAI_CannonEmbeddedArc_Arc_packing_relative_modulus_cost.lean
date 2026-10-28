-- Prove2me | solution 1 for OAI.CannonEmbeddedArc.Arc.packing_relative_modulus_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:04:32.948931+00:00
-- url     : https://prove2.me/submissions/7f8236b0-f06c-4e26-90ef-3502706a350c

import Mathlib
import Definitions.Def_OAIQ046C002
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_face_incidence_card_le

section
-- module Solutions.OAIQ046_CN.Compat
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Boundary_ThreeMarksTwoMetrics
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
namespace CannonFiniteNormalization
open Set Metric

lemma three_marks_two_metrics {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (v : Fin 3 → X) (w : Fin 3 → Y) {s t : ℝ}
    (hv : ∀ i j,i ≠ j → s ≤ dist (v i) (v j))
    (hw : ∀ i j,i ≠ j → t ≤ dist (w i) (w j)) (x : X) (y : Y) :
    ∃ i,s/2 ≤ dist x (v i) ∧ t/2 ≤ dist y (w i) := by
  classical
  by_contra hn
  have hc (i : Fin 3) : dist x (v i) < s/2 ∨ dist y (w i) < t/2 := by
    by_cases hi : s/2 ≤ dist x (v i)
    · exact Or.inr (lt_of_not_ge (fun hh=>hn ⟨i,hi,hh⟩))
    · exact Or.inl (lt_of_not_ge hi)
  let b : Fin 3 → Bool:=fun i=>decide (dist x (v i) < s/2)
  have hb : Function.Injective b := by
    intro i j hij
    by_contra hne
    have heq : (dist x (v i) < s/2)↔(dist x (v j) < s/2) := by
      simpa only [b,decide_eq_decide] using hij
    by_cases hi : dist x (v i) < s/2
    · have hj:=heq.mp hi
      have ht:=dist_triangle (v i) x (v j)
      rw [dist_comm (v i) x] at ht
      have hs:=hv i j hne
      linarith
    · have hi':=(hc i).resolve_left hi
      have hj':=(hc j).resolve_left (fun hj=>hi (heq.mpr hj))
      have ht:=dist_triangle (w i) y (w j)
      rw [dist_comm (w i) y] at ht
      have hs:=hw i j hne
      linarith
  have hh:=Fintype.card_le_of_injective b hb
  norm_num at hh

end CannonFiniteNormalization

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_ClosedCoverReflTrans
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
namespace CannonFiniteCarrier
open Set Topology Relation

lemma path_in_open_enlargement {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {A U : Set X} (hA : IsPreconnected A)
    (hU : IsOpen U) (hAU : A⊆U) {x y : X} (hx : x∈A) (hy : y∈A) :
    ∃ γ : Path x y,∀ t,γ t∈U := by
  have hsub := hA.subset_connectedComponentIn hx hAU
  have hc : IsConnected (connectedComponentIn U x) :=
    isConnected_connectedComponentIn_iff.mpr (hAU hx)
  have hp := hU.connectedComponentIn.isConnected_iff_isPathConnected.mp hc
  have hj := hp.joinedIn x (hsub hx) y (hsub hy)
  exact ⟨hj.somePath,fun t=>connectedComponentIn_subset U x (hj.somePath_mem t)⟩
end CannonFiniteCarrier

end
end
end
end

end OAI
end

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

lemma area_cyclic (a b c : ℂ) : area b c a=area a b c := by
  unfold area
  ring
lemma area_sum (a b c p : ℂ) : area a b p+area b c p+area c a p=area a b c := by
  unfold area
  ring

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
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_BoundaryBallCover
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
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι]
variable {F : ι → Arc ℂ} {d : Faces F}

lemma FacialCycle.pair_edge (C : FacialCycle F d) {u v : ℂ}
    (hu : u∈faceVertices F d) (hv : v∈faceVertices F d) (huv : u≠v) :
    ∃ i,Spans (F i) u v := by
  rw [C.vertices] at hu hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl
  all_goals first
    | exact (huv rfl).elim
    | exact ⟨C.e,C.spans_e⟩
    | exact ⟨C.e,C.spans_e.symm⟩
    | exact ⟨C.f,C.spans_f⟩
    | exact ⟨C.f,C.spans_f.symm⟩
    | exact ⟨C.g,C.spans_g⟩
    | exact ⟨C.g,C.spans_g.symm⟩

omit [Fintype ι] in
lemma Spans.developed_length {i : ι} {u v : ℂ} (h : Spans (F i) u v)
    (z : ℂ → ℂ) (r : ℂ → ℝ)
    (hlen : dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1)) :
    dist (z u) (z v)=r u+r v := by
  rcases h with ⟨h0,h1⟩|⟨h0,h1⟩
  · simpa only [h0,h1] using hlen
  · simpa only [h0,h1,dist_comm,add_comm] using hlen

lemma FacialCycle.developed_length (C : FacialCycle F d) {u v : ℂ}
    (hu : u∈faceVertices F d) (hv : v∈faceVertices F d) (huv : u≠v)
    (z : ℂ → ℂ) (r : ℂ → ℝ)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1)) :
    dist (z u) (z v)=r u+r v := by
  obtain ⟨i,hi⟩:=C.pair_edge hu hv huv
  exact hi.developed_length z r (hlen i)

end CannonEmbeddedArc.Arc

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
namespace CannonTriangleWinding
open Set Metric Topology

lemma closedInside_zero_segment {a b c p : ℂ} (h : 0<area a b c)
    (hp : ClosedInside a b c p) (hz : area a b p=0) : p∈segment ℝ a b := by
  refine ⟨area b c p/area a b c,area c a p/area a b c,
    div_nonneg hp.2.1 h.le,div_nonneg hp.2.2 h.le,?_,?_⟩
  · rw [←add_div]
    have hs:=area_sum a b c p
    have he : area b c p+area c a p=area a b c := by linarith
    rw [he,div_self h.ne']
  · have H:=area_barycentric a b c p h.ne'
    simpa only [hz,zero_div,zero_smul,add_zero] using H

lemma frontier_hull_segments {a b c : ℂ} (h : 0<area a b c) :
    frontier (convexHull ℝ ({a,b,c}:Set ℂ))⊆
      segment ℝ a b∪segment ℝ b c∪segment ℝ c a := by
  intro p hp
  have hclosed : IsClosed (convexHull ℝ ({a,b,c}:Set ℂ)) :=
    (Set.toFinite ({a,b,c}:Set ℂ)).isCompact_convexHull ℝ |>.isClosed
  have hin : ClosedInside a b c p := by
    have H:=hclosed.closure_eq ▸ hp.1
    rw [convexHull_eq_closedInside h] at H
    exact H
  have hout : ¬ Inside a b c p := by
    simpa only [convexHull_interior h,mem_ofPred_eq] using hp.2
  have hz : area a b p=0 ∨ area b c p=0 ∨ area c a p=0 := by
    by_contra H
    push Not at H
    exact hout ⟨lt_of_le_of_ne hin.1 (Ne.symm H.1),
      lt_of_le_of_ne hin.2.1 (Ne.symm H.2.1),lt_of_le_of_ne hin.2.2 (Ne.symm H.2.2)⟩
  rcases hz with hz|hz|hz
  · exact Or.inl (Or.inl (closedInside_zero_segment h hin hz))
  · exact Or.inl (Or.inr (closedInside_zero_segment (by rwa [area_cyclic])
      ⟨hin.2.1,hin.2.2,hin.1⟩ hz))
  · exact Or.inr (closedInside_zero_segment (by rwa [area_cyclic,area_cyclic])
      ⟨hin.2.2,hin.1,hin.2.1⟩ hz)

end CannonTriangleWinding

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {d e : Faces F}

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.frontier_edges (C : FacialCycle F d) (z : ℂ → ℂ)
    (hpos : 0<area (z C.a) (z C.b) (z C.c)) {p : ℂ}
    (hp : p∈frontier (faceHull F z d)) :
    ∃ u∈faceVertices F d,∃ v∈faceVertices F d,u≠v ∧ p∈segment ℝ (z u) (z v) := by
  rw [C.hull_eq] at hp
  rcases frontier_hull_segments hpos hp with (hp|hp)|hp
  · exact ⟨C.a,C.mem_a,C.b,C.mem_b,C.ab,hp⟩
  · exact ⟨C.b,C.mem_b,C.c,C.mem_c,C.bc,hp⟩
  · exact ⟨C.c,C.mem_c,C.a,C.mem_a,C.ac.symm,hp⟩

end CannonEmbeddedArc.Arc

end
end
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

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_SphereTile
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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
open scoped OnePoint

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma sphereTile_closed (z : ℂ → ℂ) (out d : Faces F) : IsClosed (sphereTile F z out d) := by
  classical
  unfold sphereTile
  split_ifs
  · exact (OnePoint.isOpenMap_coe _ isOpen_interior).isClosed_compl
  · exact ((((faceVertices F d).finite_toSet.image z).isCompact_convexHull ℝ).image OnePoint.continuous_coe).isClosed

variable {X : Type*} [TopologicalSpace X] [T2Space X]
omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] [T2Space X] in
lemma compactifiedFace_vertex (e : ℂ → X) (he : Continuous e)
    {d : Faces F} {v : ℂ} (hv : v∈faceVertices F d) : e v∈compactifiedFace F e d :=
  image_closure_subset_closure_image he ⟨v,((mem_faceVertices F d v).mp hv).2,rfl⟩

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

theorem normalized_carrier {X ι : Type*} [TopologicalSpace X]
    (A : ι → Set X) (K : ι → Set Sphere)
    (hc : ∀ S : Set Sphere,IsPreconnected S →
      IsPreconnected (⋃ (i : {i : ι // (S∩K i).Nonempty}),A i.val))
    (N : Sphere ≃ₜ Sphere) (S : Set Sphere) (hS : IsPreconnected S) :
    IsPreconnected (⋃ (i : {i : ι // (S∩N '' K i).Nonempty}),A i.val) := by
  have he (i : ι) : (S∩N '' K i).Nonempty ↔ (N ⁻¹' S∩K i).Nonempty := by
    constructor
    · rintro ⟨_,hs,⟨x,hx,rfl⟩⟩
      exact ⟨x,hs,hx⟩
    · rintro ⟨x,hx,hk⟩
      exact ⟨N x,hx,⟨x,hk,rfl⟩⟩
  have hpre : IsPreconnected (N ⁻¹' S) := by
    rw [←Homeomorph.image_symm]
    exact hS.image N.symm N.symm.continuous.continuousOn
  have hu : (⋃ (i : {i : ι // (S∩N '' K i).Nonempty}),A i.val)=
      (⋃ (i : {i : ι // (N ⁻¹' S∩K i).Nonempty}),A i.val) := by
    ext x
    simp only [mem_iUnion,Subtype.exists]
    constructor <;> rintro ⟨i,hi,hx⟩
    · exact ⟨i,(he i).mp hi,hx⟩
    · exact ⟨i,(he i).mpr hi,hx⟩
  rw [hu]
  exact hc _ hpre
end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_Quad
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonGeneralizedDisk
open Set Metric
open scoped ComplexConjugate OnePoint

lemma Quad.value_inner (q : Quad) (z : ℂ) :
    q.value z=q.A*‖z‖^2-2*inner ℝ q.b z+q.C := by
  simp only [value,Complex.normSq_eq_norm_sq,Complex.inner,mul_comm (conj q.b) z]

lemma Quad.affine_value (q : Quad) (a b z : ℂ) :
    (q.affine a b).value (a*z+b)=Complex.normSq a*q.value z := by
  simp only [value,affine,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

lemma Quad.affine_discr (q : Quad) (a b : ℂ) :
    (q.affine a b).discr=Complex.normSq a*q.discr := by
  simp only [discr,affine,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

lemma Quad.inv_discr (q : Quad) : q.inv.discr=q.discr := by
  simp only [discr,inv,Complex.normSq_conj]
  ring

lemma Quad.inv_value (q : Quad) {z : ℂ} (hz : z≠0) :
    q.inv.value z⁻¹=q.value z/Complex.normSq z := by
  have hnorm : Complex.normSq z≠0:=(Complex.normSq_pos.mpr hz).ne'
  change q.C*Complex.normSq z⁻¹-2*(conj (conj q.b)*z⁻¹).re+q.A = _
  rw [Complex.normSq_inv]
  simp only [value,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.inv_re,Complex.inv_im]
  field_simp
  ring

lemma Quad.affine_mem_iff (q : Quad) (a b : ℂ) (ha : a≠0) (z : ℂ) :
    (q.affine a b).value (a*z+b)<0 ↔ q.value z<0 := by
  rw [affine_value]
  simpa only [mul_zero] using
    (mul_lt_mul_iff_right₀ (Complex.normSq_pos.mpr ha) :
      Complex.normSq a*q.value z<Complex.normSq a*0 ↔ q.value z<0)

lemma Quad.inv_mem_iff (q : Quad) {z : ℂ} (hz : z≠0) :
    q.inv.value z⁻¹<0 ↔ q.value z<0 := by
  rw [inv_value q hz,div_lt_iff₀ (Complex.normSq_pos.mpr hz),zero_mul]

lemma disk_value (a z : ℂ) (r : ℝ) :
    (disk a r).value z=dist z a^2-r^2 := by
  rw [Quad.value_inner,dist_eq_norm,norm_sub_sq_real]
  simp only [disk,one_mul,Complex.normSq_eq_norm_sq]
  rw [real_inner_comm a z]
  ring

lemma disk_discr (a : ℂ) (r : ℝ) : (disk a r).discr=r^2 := by
  simp [disk,Quad.discr]

lemma disk_region (a : ℂ) {r : ℝ} (hr : 0 < r) :
    (disk a r).region=((↑) '' ball a r : Set (OnePoint ℂ)) := by
  ext p
  induction p using OnePoint.rec with
  | infty => simp [disk,Quad.region]
  | coe z =>
    rw [Quad.mem_region_coe,disk_value]
    constructor
    · intro h
      exact ⟨z,by rw [mem_ball]; nlinarith [dist_nonneg (x:=z) (y:=a)],rfl⟩
    · rintro ⟨w,hw,hwz⟩
      have he : w=z:=OnePoint.coe_injective hwz
      subst w
      rw [mem_ball] at hw
      nlinarith [dist_nonneg (x:=z) (y:=a)]

end CannonGeneralizedDisk

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_AffineRegion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonMobius
open Set Metric Topology CannonGeneralizedDisk
open scoped OnePoint

lemma affine_region (q : Quad) (a b : ℂ) (ha : a≠0) :
    affine a b ha '' q.region=(q.affine a b).region := by
  have hf (p : Sphere) : affine a b ha p∈(q.affine a b).region ↔ p∈q.region := by
    induction p using OnePoint.rec with
    | infty => simp only [affine_infty,Quad.mem_region_infty,Quad.affine]
    | coe z => simpa only [affine_coe,Quad.mem_region_coe] using q.affine_mem_iff a b ha z
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact (hf p).mpr hp
  · intro hx
    refine ⟨(affine a b ha).symm x,?_,(affine a b ha).apply_symm_apply x⟩
    apply (hf _).mp
    simpa only [Homeomorph.apply_symm_apply] using hx

lemma inversion_region (q : Quad) : inversion '' q.region=q.inv.region := by
  have hf (p : Sphere) : inversion p∈q.inv.region ↔ p∈q.region := by
    induction p using OnePoint.rec with
    | infty =>
      change q.inv.value 0<0 ↔ q.A<0
      simp [Quad.value,Quad.inv]
    | coe z =>
      by_cases hz : z=0
      · subst z
        change inv ((0:ℂ):Sphere)∈q.inv.region ↔ ((0:ℂ):Sphere)∈q.region
        rw [inv_zero]
        simp [Quad.region,Quad.value,Quad.inv]
      · simpa only [show inversion (z:Sphere)=(z⁻¹:ℂ) from inv_coe hz,
          Quad.mem_region_coe] using q.inv_mem_iff hz
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact (hf p).mpr hp
  · intro hx
    refine ⟨inversion.symm x,?_,inversion.apply_symm_apply x⟩
    apply (hf _).mp
    simpa only [Homeomorph.apply_symm_apply] using hx

end CannonMobius

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Round
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

lemma sphere_dist (p q : Sphere) : dist p q=dist (roundChart p) (roundChart q) := rfl

end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_Chart
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonStereo
open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stereo_inner {v : E} (hv : ‖v‖=1) (x y : (ℝ ∙ v)ᗮ) :
    inner ℝ (stereoInvFunAux v x) (stereoInvFunAux v y) =
      (16*inner ℝ (x:E) (y:E)+(‖x‖^2-4)*(‖y‖^2-4)) /
        ((‖x‖^2+4)*(‖y‖^2+4)) := by
  have hx := Submodule.mem_orthogonal_singleton_iff_inner_left.mp x.2
  have hy := Submodule.mem_orthogonal_singleton_iff_inner_left.mp y.2
  have hy' : inner ℝ v (y:E)=0 := by rw [real_inner_comm,hy]
  simp only [stereoInvFunAux_apply,inner_smul_left,inner_smul_right,
    inner_add_left,inner_add_right,conj_trivial,hx,hy',real_inner_self_eq_norm_sq,hv]
  simp only [div_eq_mul_inv,mul_inv_rev,Submodule.norm_coe]

  ring

lemma stereo_dist_sq {v : E} (hv : ‖v‖=1) (x y : (ℝ ∙ v)ᗮ) :
    (dist (stereoInvFun hv x) (stereoInvFun hv y))^2 =
      16*(dist x y)^2/((‖x‖^2+4)*(‖y‖^2+4)) := by
  have hx := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv x.2)
  have hy := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv y.2)
  change (dist (stereoInvFunAux v x) (stereoInvFunAux v y))^2=_
  rw [dist_eq_norm,norm_sub_sq_real,hx,hy,stereo_inner hv]
  rw [dist_eq_norm,norm_sub_sq_real]
  have hp : ‖x‖^2+4 ≠ 0 := by positivity
  have hq : ‖y‖^2+4 ≠ 0 := by positivity
  simp only [Submodule.coe_inner]
  field_simp [hp,hq]
  ring

end CannonStereo

noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

lemma coe_dist_sq (z w : ℂ) : dist (z:Sphere) (w:Sphere)^2=
    16*dist z w^2/((‖z‖^2+4)*(‖w‖^2+4)) := by
  rw [sphere_dist,roundChart_coe,roundChart_coe,CannonStereo.stereo_dist_sq]
  simp only [planeHyperplane.isometry.dist_eq,planeHyperplane.norm_map]

lemma coe_dist_le (z w : ℂ) : dist (z:Sphere) (w:Sphere) ≤ dist z w := by
  have h:=coe_dist_sq z w
  have hden : 0<(‖z‖^2+4)*(‖w‖^2+4):=by positivity
  have hden' : 16≤(‖z‖^2+4)*(‖w‖^2+4):=by nlinarith [sq_nonneg ‖z‖,sq_nonneg ‖w‖,mul_nonneg (sq_nonneg ‖z‖) (sq_nonneg ‖w‖)]
  have hs : dist (z:Sphere) (w:Sphere)^2 ≤ dist z w^2 := by
    rw [h,div_le_iff₀ hden]
    nlinarith [mul_nonneg (sq_nonneg (dist z w)) (show 0≤(‖z‖^2+4)*(‖w‖^2+4)-16 by linarith)]
  nlinarith [dist_nonneg (x:=z) (y:=w),dist_nonneg (x:=(z:Sphere)) (y:=(w:Sphere))]

lemma isometry_of_punctured_dist (f : Sphere ≃ₜ Sphere) (p : ℂ)
    (h : ∀ z w : ℂ,z≠p → w≠p → dist (f (z:Sphere)) (f (w:Sphere))=dist (z:Sphere) (w:Sphere)) :
    Isometry f := by
  let S : Set Sphere:=((↑) : ℂ → Sphere) '' {p}ᶜ
  have hd : Dense S:=OnePoint.denseRange_coe.dense_image OnePoint.continuous_coe (dense_compl_singleton p)
  have hx (x : Sphere) (hx : x∈S) : ∀ y,dist (f x) (f y)=dist x y := by
    have he : EqOn (fun y=>dist (f x) (f y)) (fun y=>dist x y) S := by
      rintro y ⟨w,hw,rfl⟩
      obtain ⟨z,hz,rfl⟩:=hx
      exact h z w hz hw
    have he':=he.closure (continuous_const.dist f.continuous) (continuous_const.dist continuous_id)
    rw [hd.closure_eq] at he'
    exact fun _=>he' (mem_univ _)
  apply Isometry.of_dist_eq
  intro x y
  have he : EqOn (fun x=>dist (f x) (f y)) (fun x=>dist x y) S:=fun x hh=>hx x hh y
  have he':=he.closure (f.continuous.dist continuous_const) (continuous_id.dist continuous_const)
  rw [hd.closure_eq] at he'
  exact he' (mem_univ _)

lemma chartZero_finite {z : ℂ} (hz : z≠0) : chartZero (z:Sphere)=((4/z:ℂ):Sphere) := by
  change affine 4 0 _ (inv (z:Sphere))=_
  rw [inv_coe hz,affine_coe]
  simp [div_eq_mul_inv]

lemma chartOne_finite {z : ℂ} (hz : z≠1) : chartOne (z:Sphere)=(((z+4)/(1-z):ℂ):Sphere) := by
  have hden : -(1:ℂ)*z+1≠0:=by intro e; apply hz; linear_combination -e
  change affine 5 (-1) _ (inv (affine (-1) 1 _ (z:Sphere)))=_
  rw [affine_coe,inv_coe hden,affine_coe]
  congr 1
  have hn : (1:ℂ)-z≠0:=sub_ne_zero.mpr hz.symm
  simp only [neg_one_mul,neg_add_eq_sub]
  field_simp
  ring

lemma chartOne_norm_id (z : ℂ) : ‖z+4‖^2+4*‖1-z‖^2=5*(‖z‖^2+4) := by
  simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,
    Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.one_re,Complex.one_im]
  norm_num
  ring

theorem chartZero_isometry : Isometry chartZero := by
  apply isometry_of_punctured_dist _ 0
  intro z w hz hw
  rw [chartZero_finite hz,chartZero_finite hw]
  have hnz : ‖z‖≠0:=norm_ne_zero_iff.mpr hz
  have hnw : ‖w‖≠0:=norm_ne_zero_iff.mpr hw
  have he : (4:ℂ)/z-4/w= -4*(z-w)/(z*w):=by field_simp; ring
  have hs : dist ((4/z:ℂ):Sphere) ((4/w:ℂ):Sphere)^2=dist (z:Sphere) (w:Sphere)^2 := by
    rw [coe_dist_sq,coe_dist_sq]
    simp only [dist_eq_norm,he,norm_div,norm_mul,norm_neg,Complex.norm_ofNat]
    field_simp
    ring
  nlinarith [dist_nonneg (x:=((4/z:ℂ):Sphere)) (y:=((4/w:ℂ):Sphere)),dist_nonneg (x:=(z:Sphere)) (y:=(w:Sphere))]

theorem chartOne_isometry : Isometry chartOne := by
  apply isometry_of_punctured_dist _ 1
  intro z w hz hw
  rw [chartOne_finite hz,chartOne_finite hw]
  have hz' : (1:ℂ)-z≠0:=sub_ne_zero.mpr hz.symm
  have hw' : (1:ℂ)-w≠0:=sub_ne_zero.mpr hw.symm
  have hnz : ‖(1:ℂ)-z‖≠0:=norm_ne_zero_iff.mpr hz'
  have hnw : ‖(1:ℂ)-w‖≠0:=norm_ne_zero_iff.mpr hw'
  have he : (z+4)/(1-z)-(w+4)/(1-w)=5*(z-w)/((1-z)*(1-w)):=by field_simp; ring
  have hs : dist (((z+4)/(1-z):ℂ):Sphere) (((w+4)/(1-w):ℂ):Sphere)^2=dist (z:Sphere) (w:Sphere)^2 := by
    rw [coe_dist_sq,coe_dist_sq]
    simp only [dist_eq_norm,he,norm_div,norm_mul,Complex.norm_ofNat]
    have hiz:=chartOne_norm_id z
    have hiw:=chartOne_norm_id w
    field_simp
    have hiz' : ‖z+4‖^2+‖1-z‖^2*4=5*(‖z‖^2+4):=by nlinarith [hiz]
    have hiw' : ‖w+4‖^2+‖1-w‖^2*4=5*(‖w‖^2+4):=by nlinarith [hiw]
    rw [hiz',hiw']
    ring
  nlinarith [dist_nonneg (x:=(((z+4)/(1-z):ℂ):Sphere)) (y:=(((w+4)/(1-w):ℂ):Sphere)),dist_nonneg (x:=(z:Sphere)) (y:=(w:Sphere))]
end CannonMobius

end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_CompleteSquare
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonGeneralizedDisk
open Set Metric
open scoped ComplexConjugate OnePoint

lemma Quad.complete_square (q : Quad) (hA : q.A≠0) (z : ℂ) :
    q.value z=q.A*(dist z (q.b/(q.A:ℂ))^2-q.discr/q.A^2) := by
  rw [dist_eq_norm,←Complex.normSq_eq_norm_sq]
  simp only [value,discr,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.mul_re,
    Complex.conj_re,Complex.conj_im]
  field_simp
  ring

lemma Quad.finite_disk (q : Quad) (hA : 0<q.A) (hq : 0<q.discr) :
    ∃ a : ℂ,∃ r : ℝ,0 < r ∧ q.region=((↑) '' ball a r : Set (OnePoint ℂ)) := by
  let a : ℂ:=q.b/(q.A:ℂ)
  let r : ℝ:=Real.sqrt q.discr/q.A
  have hr : 0 < r:=div_pos (Real.sqrt_pos.mpr hq) hA
  have hr2 : r^2=q.discr/q.A^2:=by
    dsimp [r]
    rw [div_pow,Real.sq_sqrt hq.le]
  refine ⟨a,r,hr,?_⟩
  ext p
  induction p using OnePoint.rec with
  | infty => simp [Quad.region,not_lt.mpr hA.le]
  | coe z =>
    rw [Quad.mem_region_coe,q.complete_square hA.ne' z,←hr2]
    change q.A*(dist z a^2-r^2)<0 ↔ (z:OnePoint ℂ)∈(↑) '' ball a r
    have hm : q.A*(dist z a^2-r^2)<0 ↔ dist z a^2-r^2<0 := by
      simpa only [mul_zero] using
        (mul_lt_mul_iff_right₀ hA : q.A*(dist z a^2-r^2)<q.A*0 ↔ dist z a^2-r^2<0)
    rw [hm]
    constructor
    · intro h
      refine ⟨z,mem_ball.mpr ?_,rfl⟩
      nlinarith [dist_nonneg (x:=z) (y:=a)]
    · rintro ⟨w,hw,he⟩
      have he' : w=z:=OnePoint.coe_injective he
      subst w
      have hd:=mem_ball.mp hw
      nlinarith [dist_nonneg (x:=z) (y:=a)]

end CannonGeneralizedDisk

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_ClosureCoeBall
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonMobius
open Set Metric Topology CannonGeneralizedDisk
open scoped OnePoint

lemma closure_coe_ball (a : ℂ) {r : ℝ} (hr : 0 < r) :
    closure ((↑) '' ball a r : Set Sphere)=(↑) '' closedBall a r := by
  apply subset_antisymm
  · exact closure_minimal (image_mono ball_subset_closedBall)
      (((isCompact_closedBall a r).image OnePoint.continuous_coe).isClosed)
  · rw [←closure_ball a hr.ne']
    exact image_closure_subset_closure_image OnePoint.continuous_coe

theorem biholomorphic_finite_disk (N : Sphere ≃ₜ Sphere) (hN : N∈biholomorphic)
    (a : ℂ) {r : ℝ} (hr : 0 < r)
    (hpole : ∞∉N '' ((↑) '' closedBall a r : Set Sphere)) :
    ∃ a' : ℂ,∃ r' : ℝ,0 < r' ∧
      N '' ((↑) '' ball a r : Set Sphere)=((↑) '' ball a' r' : Set Sphere) ∧
      N '' ((↑) '' closedBall a r : Set Sphere)=((↑) '' closedBall a' r' : Set Sphere) := by
  have hq : 0<(disk a r).discr:=by rw [disk_discr]; exact sq_pos_of_pos hr
  have hfinite : ∃ q' : Quad,0<q'.A ∧ 0<q'.discr ∧
      N '' (disk a r).region=q'.region := by
    rcases biholomorphic_normal_form N hN with ⟨α,β,hα,rfl⟩|⟨p,α,β,hα,rfl⟩
    · refine ⟨(disk a r).affine α β,by norm_num [Quad.affine,disk],?_,
        affine_region _ α β hα⟩
      rw [Quad.affine_discr]
      exact mul_pos (Complex.normSq_pos.mpr hα) hq
    · let w : ℂ:=-β/α
      have hw : α*w+β=0 := by
        dsimp only [w]
        rw [mul_div_cancel₀ (-β) hα,neg_add_cancel]
      have hmap : (affine 1 p one_ne_zero*inversion*affine α β hα) (w:Sphere)=∞ := by
        change affine 1 p one_ne_zero (inv (affine α β hα (w:Sphere)))=∞
        rw [affine_coe,hw,inv_zero,affine_infty]
      have hwr : r<dist w a := by
        by_contra hn
        exact hpole ⟨(w:Sphere),⟨w,mem_closedBall.mpr (le_of_not_gt hn),rfl⟩,hmap⟩
      have hval : 0<(disk a r).value w := by
        rw [disk_value]
        nlinarith [dist_nonneg (x:=w) (y:=a)]
      have hC : 0<((disk a r).affine α β).C := by
        have he:=Quad.affine_value (disk a r) α β w
        rw [hw] at he
        have he' : ((disk a r).affine α β).C=Complex.normSq α*(disk a r).value w := by
          simpa [Quad.value] using he
        rw [he']
        exact mul_pos (Complex.normSq_pos.mpr hα) hval
      refine ⟨((disk a r).affine α β).inv.affine 1 p,hC,?_,?_⟩
      · rw [Quad.affine_discr,Quad.inv_discr,Quad.affine_discr]
        simpa only [Complex.normSq_one,one_mul] using
          mul_pos (Complex.normSq_pos.mpr hα) hq
      · rw [←affine_region ((disk a r).affine α β).inv 1 p one_ne_zero,
          ←inversion_region ((disk a r).affine α β),←affine_region (disk a r) α β hα]
        rw [Set.image_image,Set.image_image]
        rfl
  obtain ⟨q',hA,hq',he⟩:=hfinite
  obtain ⟨a',r',hr',hreg⟩:=q'.finite_disk hA hq'
  rw [disk_region a hr,hreg] at he
  refine ⟨a',r',hr',he,?_⟩
  rw [←closure_coe_ball a hr,←closure_coe_ball a' hr',N.image_closure,he]

end CannonMobius

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_TangentDiskMeet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonTileTopology
open Set Metric Topology
open scoped OnePoint

lemma tangent_disk_meet {a b : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hd : dist a b=r+s) : (closedBall a r∩closedBall b s).Nonempty := by
  let q:=AffineMap.lineMap a b (r/(r+s))
  have hsum : 0 < r+s:=add_pos hr hs
  have ht : 0 ≤ r/(r+s):=div_nonneg hr.le hsum.le
  have ht' : r/(r+s)≤1:=(div_le_one hsum).mpr (by linarith)
  refine ⟨q,?_,?_⟩
  · change dist q a ≤ r
    dsimp [q]
    rw [dist_lineMap_left,Real.norm_eq_abs,abs_of_nonneg ht,hd,div_mul_cancel₀ _ hsum.ne']
  · change dist q b ≤ s
    dsimp [q]
    rw [dist_lineMap_right,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht'),hd]
    have he : (1-r/(r+s))*(r+s)=s:=by field_simp; ring
    exact he.le

lemma transformed_disks_touch (N : OnePoint ℂ ≃ₜ OnePoint ℂ)
    {a b a' b' : ℂ} {r s r' s' : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hd : dist a b=r+s)
    (ha : N '' ((↑) '' closedBall a r : Set (OnePoint ℂ))=(↑) '' closedBall a' r')
    (hb : N '' ((↑) '' closedBall b s : Set (OnePoint ℂ))=(↑) '' closedBall b' s') :
    dist a' b' ≤ r'+s' := by
  obtain ⟨q,hqa,hqb⟩:=tangent_disk_meet hr hs hd
  have ha' : N (q:OnePoint ℂ)∈((↑) '' closedBall a' r' : Set (OnePoint ℂ)):=
    ha ▸ ⟨(q:OnePoint ℂ),⟨q,hqa,rfl⟩,rfl⟩
  have hb' : N (q:OnePoint ℂ)∈((↑) '' closedBall b' s' : Set (OnePoint ℂ)):=
    hb ▸ ⟨(q:OnePoint ℂ),⟨q,hqb,rfl⟩,rfl⟩
  obtain ⟨u,hu,heu⟩:=ha'
  obtain ⟨v,hv,hev⟩:=hb'
  have huv : u=v:=OnePoint.coe_injective (heu.trans hev.symm)
  subst v
  have ht:=dist_triangle a' u b'
  rw [dist_comm a' u] at ht
  exact ht.trans (add_le_add hu hv)

lemma packing_balls_disjoint {ν : Type*} (z : ν → ℂ) (r : ν → ℝ)
    (hsep : ∀ i j,i≠j → r i+r j≤dist (z i) (z j)) :
    Pairwise fun i j=>Disjoint (ball (z i) (r i)) (ball (z j) (r j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro q hqi hqj
  have h1:=mem_ball.mp hqi
  have h2:=mem_ball.mp hqj
  have ht:=dist_triangle (z i) q (z j)
  rw [dist_comm (z i) q] at ht
  have hs:=hsep i j hij
  linarith
end CannonTileTopology

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_FinitePackingVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonMobius
open Set Metric Topology CannonTileTopology
open scoped OnePoint

theorem finite_packing_at_vertex {ν : Type*} (z : ν → ℂ) (r : ν → ℝ)
    (hr : ∀ j,0 < r j) (hsep : ∀ i j,i≠j → r i+r j≤dist (z i) (z j))
    (N : Sphere ≃ₜ Sphere) (hN : N∈biholomorphic) (pole : ν)
    (hpole : N (z pole:Sphere)=∞) :
    ∃ c : {j : ν // j≠pole} → ℂ,∃ t : {j : ν // j≠pole} → ℝ,
      (∀ j,0<t j) ∧
      (∀ j,N '' ((↑) '' ball (z j.val) (r j.val) : Set Sphere)=(↑) '' ball (c j) (t j)) ∧
      (∀ j,N '' ((↑) '' closedBall (z j.val) (r j.val) : Set Sphere)=(↑) '' closedBall (c j) (t j)) ∧
      Pairwise (fun i j=>Disjoint (ball (c i) (t i)) (ball (c j) (t j))) := by
  have hex (j : {j : ν // j≠pole}) : ∃ c : ℂ,∃ t : ℝ,0<t ∧
      N '' ((↑) '' ball (z j.val) (r j.val) : Set Sphere)=(↑) '' ball c t ∧
      N '' ((↑) '' closedBall (z j.val) (r j.val) : Set Sphere)=(↑) '' closedBall c t := by
    apply biholomorphic_finite_disk N hN (z j.val) (hr j.val)
    rintro ⟨p,⟨q,hq,rfl⟩,hep⟩
    have hqpole : q=z pole:=OnePoint.coe_injective (N.injective (hep.trans hpole.symm))
    subst q
    have hs:=hsep pole j.val j.property.symm
    have hq':=mem_closedBall.mp hq
    linarith [hr pole]
  choose c t ht hb hc using hex
  refine ⟨c,t,ht,hb,hc,?_⟩
  intro i j hij
  have hn : i.val≠j.val:=fun h=>hij (Subtype.ext h)
  have hd:=packing_balls_disjoint z r hsep hn
  have hd':=hd.image OnePoint.coe_injective.injOn (subset_univ _) (subset_univ _)
  have hd'':=hd'.image N.injective.injOn (subset_univ _) (subset_univ _)
  rw [hb i,hb j] at hd''
  exact hd''.of_image
end CannonMobius

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_Weights
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
noncomputable section
open scoped InnerProductSpace
open Set

namespace CannonDuality

variable {ι : Type*} [Fintype ι]

lemma inner_bound_convexHull {V : Set (Weights ι)} {w : Weights ι} {c : ℝ}
    (h : ∀ v ∈ V, c ≤ ⟪w, v⟫_ℝ) :
    ∀ v ∈ convexHull ℝ V, c ≤ ⟪w, v⟫_ℝ := by
  apply convexHull_min h
  intro x hx y hy a b ha hb hab
  change c ≤ ⟪w, a • x + b • y⟫_ℝ
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  change c ≤ ⟪w, x⟫_ℝ at hx
  change c ≤ ⟪w, y⟫_ℝ at hy
  calc
    c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    _ ≤ a * ⟪w, x⟫_ℝ + b * ⟪w, y⟫_ℝ :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

lemma nonnegative_convexHull {V : Set (Weights ι)}
    (h : ∀ v ∈ V, Nonnegative v) :
    ∀ v ∈ convexHull ℝ V, Nonnegative v := by
  apply convexHull_min h
  intro x hx y hy a b ha hb hab i
  change 0 ≤ a * x i + b * y i
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem exists_dual_minimizer (V : Finset (Weights ι)) (hne : V.Nonempty)
    (hnonneg : ∀ v ∈ V, Nonnegative v)
    (hpositive : ∀ v ∈ V, 1 ≤ ∑ i, v i) :
    ∃ P ∈ convexHull ℝ (V : Set (Weights ι)),
      Nonnegative P ∧ P ≠ 0 ∧ ∀ v ∈ V, ‖P‖ ^ 2 ≤ ⟪P, v⟫_ℝ := by
  have hK : (convexHull ℝ (V : Set (Weights ι))).Nonempty :=
    hne.to_set.mono (subset_convexHull ℝ _)
  obtain ⟨P, hP, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hK
    ((V.finite_toSet.isCompact_convexHull ℝ).isComplete)
    (convex_convexHull ℝ _) (0 : Weights ι)
  refine ⟨P, hP, nonnegative_convexHull hnonneg P hP, ?_, ?_⟩
  · let one : Weights ι := (WithLp.toLp 2 fun _ => (1 : ℝ))
    have hsum : ∀ v ∈ (V : Set (Weights ι)), 1 ≤ ⟪one, v⟫_ℝ := by
      intro v hv
      simpa [one, EuclideanSpace.inner_eq_star_dotProduct, dotProduct] using hpositive v hv
    have hb := inner_bound_convexHull hsum P hP
    intro hz
    norm_num [hz] at hb
  · have hproj := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ _)
      hP).mp hmin
    intro v hv
    have hi := hproj v (subset_convexHull ℝ _ hv)
    simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hi
    linarith

lemma normalized_admissible {V : Set (Weights ι)} {P : Weights ι}
    (hP : Nonnegative P) (hPne : P ≠ 0)
    (hdual : ∀ v ∈ V, ‖P‖ ^ 2 ≤ ⟪P, v⟫_ℝ) :
    Admissible V ((‖P‖ ^ 2)⁻¹ • P) := by
  have hp : 0 < ‖P‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hPne)
  constructor
  · intro i
    change 0 ≤ (‖P‖ ^ 2)⁻¹ * P i
    exact mul_nonneg (inv_nonneg.mpr hp.le) (hP i)
  · intro v hv
    rw [real_inner_smul_left]
    calc
      1 = (‖P‖ ^ 2)⁻¹ * ‖P‖ ^ 2 := (inv_mul_cancel₀ hp.ne').symm
      _ ≤ (‖P‖ ^ 2)⁻¹ * ⟪P, v⟫_ℝ :=
        mul_le_mul_of_nonneg_left (hdual v hv) (inv_nonneg.mpr hp.le)

lemma normalized_energy {P : Weights ι} (hPne : P ≠ 0) :
    ‖(‖P‖ ^ 2)⁻¹ • P‖ ^ 2 = (‖P‖ ^ 2)⁻¹ := by
  have hp : ‖P‖ ≠ 0 := norm_ne_zero_iff.mpr hPne
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

lemma admissible_energy_lower {V : Set (Weights ι)} {P : Weights ι}
    (hP : P ∈ convexHull ℝ V) (hPne : P ≠ 0)
    {w : Weights ι} (hw : Admissible V w) :
    (‖P‖ ^ 2)⁻¹ ≤ ‖w‖ ^ 2 := by
  have hpair : 1 ≤ ⟪w, P⟫_ℝ := inner_bound_convexHull hw.2 P hP
  have hcs := real_inner_mul_inner_self_le w P
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hprod : 1 ≤ ‖w‖ ^ 2 * ‖P‖ ^ 2 := by nlinarith
  have hp : 0 < ‖P‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hPne)
  simpa only [one_div] using (div_le_iff₀ hp).mpr hprod

theorem modulus_eq_inverse_dual_energy (V : Finset (Weights ι)) (hne : V.Nonempty)
    (hnonneg : ∀ v ∈ V, Nonnegative v)
    (hpositive : ∀ v ∈ V, 1 ≤ ∑ i, v i) :
    ∃ P ∈ convexHull ℝ (V : Set (Weights ι)),
      Nonnegative P ∧ P ≠ 0 ∧
      Modulus (V : Set (Weights ι)) = (‖P‖ ^ 2)⁻¹ ∧
      Admissible (V : Set (Weights ι)) ((‖P‖ ^ 2)⁻¹ • P) := by
  obtain ⟨P, hP, hnon, hneP, hdual⟩ := exists_dual_minimizer V hne hnonneg hpositive
  have hadm := normalized_admissible hnon hneP hdual
  have henergy := normalized_energy hneP
  refine ⟨P, hP, hnon, hneP, ?_, hadm⟩
  apply le_antisymm
  · apply csInf_le
    · use 0
      rintro _ ⟨w, _, rfl⟩
      exact sq_nonneg ‖w‖
    · exact ⟨_, hadm, henergy.symm⟩
  · apply le_csInf
    · exact ⟨_, _, hadm, rfl⟩
    · rintro e ⟨w, hw, rfl⟩
      exact admissible_energy_lower hP hneP hw

end CannonDuality

namespace CannonCells
open Set CannonDuality
open scoped InnerProductSpace

variable {X ι : Type*} [Fintype ι]

lemma mem_familyVectors (C : ι → Set X) (F : Set (Set X)) (v : Weights ι) :
    v ∈ familyVectors C F ↔ ∃ A ∈ F, incidence C A = v := by
  classical
  simp only [familyVectors,Finset.mem_image,Set.Finite.mem_toFinset,Set.mem_image,incidence]
  constructor
  · rintro ⟨s,⟨A,hA,rfl⟩,hv⟩
    exact ⟨A,hA,hv⟩
  · rintro ⟨A,hA,hv⟩
    exact ⟨indices C A,⟨A,hA,rfl⟩,hv⟩

lemma incidence_nonnegative (C : ι → Set X) (A : Set X) : Nonnegative (incidence C A) := by
  classical
  intro i
  change 0 ≤ if i ∈ indices C A then (1:ℝ) else 0
  split <;> norm_num

lemma incidence_at (C : ι → Set X) (A : Set X) {i : ι} (hi : (A ∩ C i).Nonempty) :
    incidence C A i = 1 := by
  classical
  change (if i ∈ indices C A then (1:ℝ) else 0) = 1
  rw [ite_eq_left ((mem_indices C A i).mpr hi)]

lemma incidence_positive (C : ι → Set X) (hC : ∀ x, ∃ i, x ∈ C i)
    {A : Set X} (hA : A.Nonempty) : 1 ≤ ∑ i, incidence C A i := by
  classical
  obtain ⟨x,hx⟩ := hA
  obtain ⟨i,hi⟩ := hC x
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => incidence_nonnegative C A j)
    (Finset.mem_univ i)
  rwa [incidence_at C A ⟨x,hx,hi⟩] at h

lemma admissible_iff (C : ι → Set X) (F : Set (Set X)) (w : Weights ι) :
    Admissible (familyVectors C F : Set (Weights ι)) w ↔
      Nonnegative w ∧ ∀ A ∈ F, 1 ≤ ∑ i ∈ indices C A, w i := by
  classical
  have hinner (A : Set X) : ⟪w,incidence C A⟫_ℝ = ∑ i ∈ indices C A, w i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [incidence,weight,dotProduct]
  constructor
  · rintro ⟨hn,hw⟩
    refine ⟨hn,fun A hA => ?_⟩
    rw [← hinner]
    exact hw _ ((mem_familyVectors C F _).mpr ⟨A,hA,rfl⟩)
  · rintro ⟨hn,hw⟩
    refine ⟨hn,?_⟩
    intro v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    rw [hinner]
    exact hw A hA

lemma familyVectors_nonempty (C : ι → Set X) {F : Set (Set X)} (hF : F.Nonempty) :
    (familyVectors C F).Nonempty := by
  obtain ⟨A,hA⟩ := hF
  exact ⟨incidence C A,(mem_familyVectors C F _).mpr ⟨A,hA,rfl⟩⟩

theorem modulus_minimum (C : ι → Set X) (hC : ∀ x, ∃ i, x ∈ C i)
    {F : Set (Set X)} (hF : F.Nonempty) (hFn : ∀ A ∈ F, A.Nonempty) :
    0 < modulus C F ∧ ∃ w : Weights ι,
      Admissible (familyVectors C F : Set (Weights ι)) w ∧ ‖w‖^2 = modulus C F := by
  have hn : ∀ v ∈ familyVectors C F, Nonnegative v := by
    intro v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    exact incidence_nonnegative C A
  have hp : ∀ v ∈ familyVectors C F, 1 ≤ ∑ i, v i := by
    intro v hv
    obtain ⟨A,hA,rfl⟩ := (mem_familyVectors C F v).mp hv
    exact incidence_positive C hC (hFn A hA)
  obtain ⟨P,_,_,hP,hmod,hadm⟩ := modulus_eq_inverse_dual_energy
    (familyVectors C F) (familyVectors_nonempty C hF) hn hp
  have hpositive : 0 < ‖P‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hP)
  refine ⟨?_,(‖P‖^2)⁻¹ • P,hadm,?_⟩
  · change 0 < Modulus _
    rw [hmod]
    exact inv_pos.mpr hpositive
  · exact (normalized_energy hP).trans hmod.symm

end CannonCells
end

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlanarGraphs_RadialIncidenceLength
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
open MeasureTheory Set
open scoped BigOperators

namespace CannonRadialEnergy

attribute [local instance] Classical.propDecidable

theorem radial_incidence_length {ι : Type*} [Fintype ι]
    {a b A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (d r w : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ t ∈ Icc a b,
      1 ≤ ∑ i, if |t - d i| ≤ A * r i then w i else 0) :
    b - a ≤ 2 * A * ∑ i, r i * w i := by
  classical
  let J : ι → Set ℝ := fun i => Icc (d i - A * r i) (d i + A * r i)
  let f : ι → ℝ → ℝ := fun i => (J i).indicator (fun _ => w i)
  have hf (i : ι) : Integrable (f i) volume := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrable_const (w i)
  have hg : Integrable ((Icc a b).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrable_const 1
  have hiff (i : ι) (t : ℝ) : t ∈ J i ↔ |t - d i| ≤ A * r i := by
    simp only [J, mem_Icc, abs_le]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  have he (t : ℝ) : (∑ i, f i t) =
      ∑ i, if |t-d i| ≤ A*r i then w i else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [f, indicator_apply, hiff]
  have hnonneg (i : ι) (t : ℝ) : 0 ≤ f i t := by
    exact indicator_nonneg (fun _ _ => hw i) t
  have hpoint (t : ℝ) : (Icc a b).indicator (fun _ : ℝ => (1 : ℝ)) t ≤ ∑ i, f i t := by
    by_cases ht : t ∈ Icc a b
    · simpa only [indicator_of_mem ht, he] using hcover t ht
    · rw [indicator_of_notMem ht]
      exact Finset.sum_nonneg (fun i _ => hnonneg i t)
  have hbound := integral_mono hg (integrable_finsetSum _ (fun i _ => hf i)) hpoint
  have hint (i : ι) : (∫ t, f i t) = 2 * A * r i * w i := by
    have hh : d i-A*r i ≤ d i+A*r i := by nlinarith [mul_nonneg hA (hr i)]
    dsimp [f,J]
    rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hh,
      smul_eq_mul]
    ring
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hab,
    smul_eq_mul, mul_one, integral_finsetSum _ (fun i _ => hf i)] at hbound
  simp only [hint] at hbound
  calc
    b-a ≤ ∑ i, 2*A*r i*w i := hbound
    _ = 2*A*∑ i, r i*w i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem radial_incidence_energy {ι : Type*} [Fintype ι]
    {a b A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (d r w : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ t ∈ Icc a b,
      1 ≤ ∑ i, if |t - d i| ≤ A * r i then w i else 0) :
    (b - a)^2 ≤ 4 * A^2 * (∑ i, r i^2) * ∑ i, w i^2 := by
  have hh := radial_incidence_length hab hA d r w hr hw hcover
  have hsq : (b-a)^2 ≤ (2*A*(∑ i, r i*w i))^2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hab) hh 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r w
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4*A^2 by positivity)
  calc
    (b-a)^2 ≤ (2*A*(∑ i, r i*w i))^2 := hsq
    _ = 4*A^2*(∑ i, r i*w i)^2 := by ring
    _ ≤ 4*A^2*((∑ i, r i^2)*(∑ i, w i^2)) := hm
    _ = _ := by ring

end CannonRadialEnergy

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_RadialCellEnergy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
open MeasureTheory Set
open scoped BigOperators

namespace CannonRadialEnergy

attribute [local instance] Classical.propDecidable

theorem radial_cell_energy {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    {a b A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (p : X) (c : ι → X) (r w : ι → ℝ) (U : ι → Set X)
    (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hcell : ∀ i, U i ⊆ Metric.closedBall (c i) (A*r i))
    (hadm : ∀ t ∈ Icc a b,
      1 ≤ ∑ i, if (U i ∩ Metric.sphere p t).Nonempty then w i else 0) :
    (b-a)^2 ≤ 4*A^2*(∑ i, r i^2)*∑ i, w i^2 := by
  classical
  apply radial_incidence_energy hab hA (fun i => dist p (c i)) r w hr hw
  intro t ht
  apply (hadm t ht).trans
  apply Finset.sum_le_sum
  intro i hi
  by_cases hu : (U i ∩ Metric.sphere p t).Nonempty
  · have hu₀ := hu
    rcases hu with ⟨x,hx,hxt⟩
    have hd : dist x p=t := hxt
    have hxc : dist x (c i) ≤ A*r i := hcell i hx
    have hrad : |t-dist p (c i)| ≤ A*r i := by
      simpa only [hd, dist_comm (c i) p] using (abs_dist_sub_le x (c i) p).trans hxc
    simp only [hrad,hu₀,ite_eq_left,le_refl]
  · rw [ite_eq_right hu]
    split_ifs
    · exact hw i
    · exact le_rfl

theorem radial_cell_energy_budget {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    {a b A P : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (p : X) (c : ι → X) (r w : ι → ℝ) (U : ι → Set X)
    (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hcell : ∀ i, U i ⊆ Metric.closedBall (c i) (A*r i))
    (hbudget : (∑ i, r i^2) ≤ P)
    (hadm : ∀ t ∈ Icc a b,
      1 ≤ ∑ i, if (U i ∩ Metric.sphere p t).Nonempty then w i else 0) :
    (b-a)^2 ≤ 4*A^2*P*∑ i, w i^2 := by
  apply (radial_cell_energy hab hA p c r w U hr hw hcell hadm).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbudget (by positivity))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end CannonRadialEnergy

namespace CannonRadialEnergy
attribute [local instance] Classical.propDecidable

theorem disjoint_disk_square_budget {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (r : ι → ℝ) (p : ℂ) {R : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hR : 0 ≤ R)
    (hdisj : Pairwise (fun i j => Disjoint (Metric.ball (c i) (r i))
      (Metric.ball (c j) (r j))))
    (hcontain : ∀ i, Metric.ball (c i) (r i) ⊆ Metric.ball p R) :
    (∑ i, r i^2) ≤ R^2 := by
  classical
  have harea (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
      volume.real (Metric.ball z s) = s^2*Real.pi := by
    simp [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hs]
  have hU : (⋃ i ∈ (Finset.univ : Finset ι), Metric.ball (c i) (r i)) ⊆ Metric.ball p R := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨i,hi⟩
    rcases mem_iUnion.mp hi with ⟨_,hxi⟩
    exact hcontain i hxi
  have hs : volume.real (⋃ i ∈ (Finset.univ : Finset ι), Metric.ball (c i) (r i)) =
      ∑ i, volume.real (Metric.ball (c i) (r i)) := by
    apply measureReal_biUnion_finset
    · intro i hi j hj hij
      exact hdisj hij
    · exact fun _ _ => Metric.isOpen_ball.measurableSet
    · intro i hi
      rw [Complex.volume_ball]
      finiteness
  have hh := measureReal_mono (μ := volume) hU (by rw [Complex.volume_ball]; finiteness)
  rw [hs,harea p hR] at hh
  simp only [harea _ (hr _)] at hh
  rw [← Finset.sum_mul] at hh
  nlinarith [Real.pi_pos]

end CannonRadialEnergy

end

end
end
section
noncomputable section

namespace CannonTransfer
theorem overlap_energy {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (R : α → Finset β) (w : β → ℝ) (kr kc : ℕ)
    (hrow : ∀ i, (R i).card ≤ kr)
    (hcol : ∀ j, (Finset.univ.filter (fun i => j ∈ R i)).card ≤ kc) :
    (∑ i, (∑ j ∈ R i, w j)^2) ≤
      (kr : ℝ) * kc * (∑ j, (w j)^2) := by
  classical
  have hrowE (i : α) : (∑ j ∈ R i, w j)^2 ≤ (kr : ℝ) * (∑ j ∈ R i, (w j)^2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (R i) (fun _ => (1:ℝ)) w
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hrow i)
      (Finset.sum_nonneg (fun j _ => sq_nonneg (w j))))
  have hswap : (∑ i, ∑ j ∈ R i, (w j)^2) =
      ∑ j, ((Finset.univ.filter (fun i => j ∈ R i)).card : ℝ) * (w j)^2 := by
    calc
      _ = ∑ i, ∑ j : β, if j ∈ R i then (w j)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_filter]
        simp
      _ = ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j ∈ R i), (w j)^2 := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
      _ = _ := by simp
  calc
    _ ≤ ∑ i, (kr : ℝ) * (∑ j ∈ R i, (w j)^2) := Finset.sum_le_sum (fun i _ => hrowE i)
    _ = (kr : ℝ) * (∑ i, ∑ j ∈ R i, (w j)^2) := (Finset.mul_sum ..).symm
    _ = (kr : ℝ) * (∑ j, ((Finset.univ.filter (fun i => j ∈ R i)).card : ℝ) * (w j)^2) := by rw [hswap]
    _ ≤ (kr : ℝ) * (∑ j, (kc : ℝ) * (w j)^2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcol j) (sq_nonneg (w j)))
    _ = _ := by rw [← Finset.mul_sum]; ring

end CannonTransfer

end
end
section
noncomputable section
open Set Metric Topology
open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable
namespace CannonCarrierCharging

lemma sum_le_charges {ι ν : Type*} [DecidableEq ι] [DecidableEq ν]
    (I : Finset ι) (A : Finset ν) (R : ν → Finset ι) (w : ι → ℝ)
    (hw : ∀ i,0≤w i) (hcover : ∀ i∈I,∃ v∈A,i∈R v) :
    (∑ i∈I,w i)≤∑ v∈A,∑ i∈R v,w i := by
  have hi (i : ι) (hi : i∈I) : w i≤∑ v∈A,if i∈R v then w i else 0 := by
    obtain ⟨v,hv,hiv⟩:=hcover i hi
    have hh:=Finset.single_le_sum (s:=A) (f:=fun v=>if i∈R v then w i else 0)
      (fun v _=>by split; exact hw i; exact le_rfl) hv
    simpa only [ite_eq_left hiv] using hh
  calc
    _ ≤ ∑ i∈I,∑ v∈A,if i∈R v then w i else 0 := Finset.sum_le_sum hi
    _ = ∑ v∈A,∑ i∈I,if i∈R v then w i else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      rw [←Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi=>(Finset.mem_filter.mp hi).2) (fun i _ _=>hw i)

theorem path_cell_charging {X Y ι ν κ : Type*} [MetricSpace X]
    [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
    (A : κ → Set X) (K : κ → Set Y) (U : ν → Set Y)
    (s : κ → ν) (v : ν → X) (q : ι → X) (S : Set Y)
    (mesh η D : ℝ)
    (hdiam : ∀ d,∀ x∈A d,dist x (v (s d))≤D)
    (hstar : ∀ d,K d⊆U (s d))
    {x y : X} (γ : Path x y)
    (hγ : range γ⊆thickening η (⋃ (d : {d : κ // (S∩K d).Nonempty}),A d.val))
    (w : ι → ℝ) (hw : ∀ i,0≤w i) :
    (∑ i∈CannonCells.indices (fun i=>ball (q i) (2*mesh)) (range γ),w i) ≤
      ∑ j∈Finset.univ.filter (fun j=>(S∩U j).Nonempty),
        ∑ i∈Finset.univ.filter (fun i=>dist (q i) (v j)<2*mesh+η+D),w i := by
  classical
  apply sum_le_charges _ _ _ _ hw
  intro i hi
  obtain ⟨z,hzγ,hzq⟩:=(CannonCells.mem_indices _ _ _).mp hi
  obtain ⟨a,ha,hza⟩:=mem_thickening_iff.mp (hγ hzγ)
  obtain ⟨d,had⟩:=mem_iUnion.mp ha
  refine ⟨s d.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  · obtain ⟨b,hbS,hbK⟩:=d.property
    exact ⟨b,hbS,hstar d.val hbK⟩
  · have hdist:=dist_triangle (q i) z (v (s d.val))
    have hdist':=dist_triangle z a (v (s d.val))
    have hd:=hdiam d.val a had
    have hz:=mem_ball.mp hzq
    rw [dist_comm z (q i)] at hz
    linarith

theorem carrier_admissible_charging {X Y ι ν κ : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] [Fintype ι] [Fintype ν]
    [DecidableEq ι] [DecidableEq ν]
    (A : κ → Set X) (K : κ → Set Y) (U : ν → Set Y)
    (s : κ → ν) (v : ν → X) (q : ι → X) (S : Set Y)
    (mesh η D : ℝ) (hη : 0<η)
    (hdiam : ∀ d,∀ x∈A d,dist x (v (s d))≤D)
    (hstar : ∀ d,K d⊆U (s d))
    (hconn : IsPreconnected (⋃ (d : {d : κ // (S∩K d).Nonempty}),A d.val))
    {x y : X}
    (hx : x∈⋃ (d : {d : κ // (S∩K d).Nonempty}),A d.val)
    (hy : y∈⋃ (d : {d : κ // (S∩K d).Nonempty}),A d.val)
    (F : Set (Set X)) (hF : ∀ γ : Path x y,range γ∈F)
    (w : CannonDuality.Weights ι)
    (hw : CannonDuality.Admissible (CannonCells.familyVectors
      (fun i=>ball (q i) (2*mesh)) F : Set (CannonDuality.Weights ι)) w) :
    1≤∑ j∈Finset.univ.filter (fun j=>(S∩U j).Nonempty),
      ∑ i∈Finset.univ.filter (fun i=>dist (q i) (v j)<2*mesh+η+D),w i := by
  obtain ⟨γ,hγ⟩:=CannonFiniteCarrier.path_in_open_enlargement hconn
    isOpen_thickening (self_subset_thickening hη _) hx hy
  obtain ⟨hw0,hw1⟩:=(CannonCells.admissible_iff _ _ _).mp hw
  apply (hw1 (range γ) (hF γ)).trans
  apply path_cell_charging A K U s v q S mesh η D hdiam hstar γ _ (fun i=>w i) hw0
  rintro _ ⟨t,rfl⟩
  exact hγ t
end CannonCarrierCharging

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_Ambient
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

namespace CannonCarrierCharging
open Set Metric Topology CannonUniformization
open scoped OnePoint

variable {X : Type*} [MetricSpace X]

lemma spherical_radial_level_preimage (f : C(X,OnePoint ℂ))
    (E : Set X) (hE : IsPreconnected E) (p : ℂ)
    {u v : X} (hu : u∈E) (hv : v∈E) {a b : ℝ}
    (hu' : f u∈((↑) '' closedBall p a : Set (OnePoint ℂ)))
    (hv' : f v∉((↑) '' ball p b : Set (OnePoint ℂ))) :
    ∀ t∈Icc a b,∃ x∈E,f x∈((↑) '' sphere p t : Set (OnePoint ℂ)) := by
  intro t ht
  let U : Set (OnePoint ℂ):=((↑) '' closedBall p t)
  let V : Set (OnePoint ℂ):=((↑) '' ball p t)ᶜ
  have hU : IsClosed U := ((isCompact_closedBall p t).image OnePoint.continuous_coe).isClosed
  have hV : IsClosed V := (OnePoint.isOpenMap_coe _ isOpen_ball).isClosed_compl
  have huc : f u∈U := by
    obtain ⟨z,hz,hzf⟩:=hu'
    exact ⟨z,(mem_closedBall.mp hz).trans ht.1,hzf⟩
  have hvc : f v∈V := by
    intro h
    apply hv'
    obtain ⟨z,hz,hzf⟩:=h
    exact ⟨z,(mem_ball.mp hz).trans_le ht.2,hzf⟩
  have hcover : f '' E⊆U∪V := by
    intro y _
    by_cases hy : y∈((↑) '' ball p t : Set (OnePoint ℂ))
    · obtain ⟨z,hz,rfl⟩:=hy
      exact Or.inl ⟨z,(mem_ball.mp hz).le,rfl⟩
    · exact Or.inr hy
  obtain ⟨q,⟨x,hx,hxq⟩,hqU,hqV⟩:=isPreconnected_closed_iff.mp
    (hE.image f f.continuous.continuousOn) U V hU hV hcover
    ⟨f u,mem_image_of_mem f hu,huc⟩ ⟨f v,mem_image_of_mem f hv,hvc⟩
  obtain ⟨z,hz,hzq⟩:=hqU
  have hnot : ¬dist z p<t := by
    intro hh
    exact hqV ⟨z,hh,hzq⟩
  refine ⟨x,hx,z,le_antisymm hz (le_of_not_gt hnot),?_⟩
  exact hzq.trans hxq.symm

theorem spherical_continua_carrier_crossing {κ : Type*}
    (f : C(X,OnePoint ℂ)) (A : κ → Set X) (K : κ → Set (OnePoint ℂ))
    (hpre : ∀ S : Set (OnePoint ℂ),f ⁻¹' S⊆
      ⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val)
    (E F : Set X) (hE : IsPreconnected E) (hF : IsPreconnected F)
    (o : X) (r R : ℝ) (hEin : E⊆closedBall o r) (hFout : F⊆(ball o R)ᶜ)
    (p : ℂ) (a b : ℝ)
    (hErange : ∃ u∈E,∃ v∈E,
      f u∈((↑) '' closedBall p a : Set (OnePoint ℂ)) ∧
      f v∉((↑) '' ball p b : Set (OnePoint ℂ)))
    (hFrange : ∃ u∈F,∃ v∈F,
      f u∈((↑) '' closedBall p a : Set (OnePoint ℂ)) ∧
      f v∉((↑) '' ball p b : Set (OnePoint ℂ))) :
    ∀ t∈Icc a b,
      ∃ x∈⋃(d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val,
      ∃ y∈⋃(d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val,
        ∀ γ : Path x y,range γ∈annulusFamily o r R := by
  obtain ⟨u,hu,v,hv,hu',hv'⟩:=hErange
  obtain ⟨u',huF,v',hvF,huF',hvF'⟩:=hFrange
  intro t ht
  obtain ⟨x,hx,hfx⟩:=spherical_radial_level_preimage f E hE p hu hv hu' hv' t ht
  obtain ⟨y,hy,hfy⟩:=spherical_radial_level_preimage f F hF p huF hvF huF' hvF' t ht
  refine ⟨x,hpre _ hfx,y,hpre _ hfy,?_⟩
  intro γ
  exact ⟨x,y,γ,rfl,hEin hx,le_of_not_gt (hFout hy)⟩

lemma spherical_circle_carriers_preconnected {κ : Type*}
    (A : κ → Set X) (K : κ → Set (OnePoint ℂ))
    (hc : ∀ S : Set (OnePoint ℂ),IsPreconnected S →
      IsPreconnected (⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val))
    (p : ℂ) (t : ℝ) :
    IsPreconnected
      (⋃(d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val) := by
  apply hc
  exact (isPreconnected_sphere (by simp) p t).image _ OnePoint.continuous_coe.continuousOn
end CannonCarrierCharging

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_BoundaryNormalizedAnnularCarriers
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonTileTopology
open Set Topology Metric
open scoped OnePoint

lemma regular_tiles_inter_frontier {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : closure (interior A)=A) (hB : closure (interior B)=B)
    (hd : Disjoint (interior A) (interior B)) {x : X} (hxA : x∈A) (hxB : x∈B) :
    x∈frontier A ∩ frontier B := by
  have hda : Disjoint (interior A) B := hB ▸ hd.closure_right isOpen_interior
  have hdb : Disjoint A (interior B) := hA ▸ hd.closure_left isOpen_interior
  exact ⟨⟨subset_closure hxA,fun h=>Set.disjoint_left.mp hda h hxB⟩,
    ⟨subset_closure hxB,fun h=>Set.disjoint_left.mp hdb hxA h⟩⟩

lemma compact_trace {K : Set (OnePoint ℂ)} (hc : IsClosed K) (hpole : ∞∉K) :
    IsCompact (((↑) : ℂ → OnePoint ℂ) ⁻¹' K) := by
  have he : (↑) '' (((↑) : ℂ → OnePoint ℂ) ⁻¹' K)=K := by
    apply image_preimage_eq_of_subset
    intro x hx
    exact OnePoint.ne_infty_iff_exists.mp (fun h=>hpole (h ▸ hx))
  have hc' : IsClosed (((↑) : ℂ → OnePoint ℂ) '' (((↑) : ℂ → OnePoint ℂ) ⁻¹' K)) := by rw [he]; exact hc
  exact (OnePoint.isClosed_image_coe.mp hc').2

lemma trace_frontier (K : Set (OnePoint ℂ)) :
    frontier (((↑) : ℂ → OnePoint ℂ) ⁻¹' K)=
      ((↑) : ℂ → OnePoint ℂ) ⁻¹' frontier K :=
  (OnePoint.isOpenMap_coe.preimage_frontier_eq_frontier_preimage
    OnePoint.continuous_coe K).symm

end CannonTileTopology

namespace CannonTileTopology
open Set Metric Topology
open scoped OnePoint

lemma coe_image_interior (K : Set ℂ) :
    interior (((↑) : ℂ → OnePoint ℂ) '' K)=((↑) : ℂ → OnePoint ℂ) '' interior K := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨z,hz,rfl⟩:=interior_subset hx
    have h:=OnePoint.isOpenMap_coe.preimage_interior_eq_interior_preimage OnePoint.continuous_coe
      (((↑) : ℂ → OnePoint ℂ) '' K)
    rw [Set.preimage_image_eq _ OnePoint.coe_injective] at h
    exact ⟨z,h ▸ hx,rfl⟩
  · exact OnePoint.isOpenMap_coe.image_interior_subset _

lemma coe_closure_interior {K : Set ℂ} (hc : IsCompact K)
    (hr : closure (interior K)=K) :
    closure (((↑) : ℂ → OnePoint ℂ) '' interior K)=((↑) : ℂ → OnePoint ℂ) '' K := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono interior_subset) (hc.image OnePoint.continuous_coe).isClosed
  · simpa only [hr] using (image_closure_subset_closure_image (OnePoint.continuous_coe (X := ℂ)) (s := interior K))

lemma coe_regular {K : Set ℂ} (hc : IsCompact K) (hr : closure (interior K)=K) :
    closure (interior (((↑) : ℂ → OnePoint ℂ) '' K))=((↑) : ℂ → OnePoint ℂ) '' K := by
  rw [coe_image_interior,coe_closure_interior hc hr]

lemma coe_frontier {K : Set ℂ} (hc : IsCompact K) :
    frontier (((↑) : ℂ → OnePoint ℂ) '' K)=((↑) : ℂ → OnePoint ℂ) '' frontier K := by
  rw [frontier,frontier,(hc.image OnePoint.continuous_coe).isClosed.closure_eq,
    hc.isClosed.closure_eq,coe_image_interior,Set.image_sdiff OnePoint.coe_injective]

lemma coe_interior_frontier {K : Set ℂ} (hc : IsCompact K)
    (hr : closure (interior K)=K) :
    frontier (((↑) : ℂ → OnePoint ℂ) '' interior K)=((↑) : ℂ → OnePoint ℂ) '' frontier K := by
  rw [frontier,coe_closure_interior hc hr,
    (OnePoint.isOpenMap_coe _ isOpen_interior).interior_eq,
    frontier,hc.isClosed.closure_eq,Set.image_sdiff OnePoint.coe_injective]

lemma segment_two_closedBalls {a b : ℂ} {r s : ℝ}
    (h : dist a b=r+s) : segment ℝ a b⊆closedBall a r∪closedBall b s := by
  intro z hz
  have he:=dist_add_dist_of_mem_segment hz
  rw [h,dist_comm a z] at he
  by_cases hza : dist z a ≤ r
  · exact Or.inl hza
  · exact Or.inr (show dist z b ≤ s by linarith)
end CannonTileTopology

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Conformal_MarkedChart
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
namespace CannonMobius
open Set Metric Topology
open scoped OnePoint

lemma markedChart_biholomorphic (i : Fin 3) : markedChart i∈biholomorphic := by
  fin_cases i
  · exact biholomorphic.one_mem
  · exact biholomorphic.mul_mem (affine_biholomorphic _ _ _) inversion_biholomorphic
  · exact biholomorphic.mul_mem
      (biholomorphic.mul_mem (affine_biholomorphic _ _ _) inversion_biholomorphic)
      (affine_biholomorphic _ _ _)
lemma markedChart_isometry (i : Fin 3) : Isometry (markedChart i) := by
  fin_cases i
  · exact isometry_id
  · exact chartZero_isometry
  · exact chartOne_isometry
lemma markedChart_pole (i : Fin 3) : markedChart i (std i)=∞ := by
  fin_cases i
  · rfl
  · change affine 4 0 _ (inv ((0:ℂ):Sphere))=∞
    rw [inv_zero,affine_infty]
  · change affine 5 (-1) _ (inv (affine (-1) 1 _ ((1:ℂ):Sphere)))=∞
    rw [affine_coe]
    norm_num
lemma markedChart_other (i j : Fin 3) (hij : i≠j) :
    ∃ z : ℂ,markedChart i (std j)=(z:Sphere) ∧ ‖z‖≤4 := by
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact ⟨0,rfl,by norm_num⟩
  · exact ⟨1,rfl,by norm_num⟩
  · refine ⟨0,?_,by norm_num⟩
    change affine 4 0 _ (inv ∞)=_
    rw [inv_infty,affine_coe]
    norm_num
  · exact ⟨4,by simpa [markedChart,std] using chartZero_finite (z:=1) (by norm_num),by norm_num⟩
  · refine ⟨-1,?_,by norm_num⟩
    change affine 5 (-1) _ (inv (affine (-1) 1 (by norm_num) ∞))=_
    rw [affine_infty,inv_infty,affine_coe]
    norm_num
  · exact ⟨4,by simpa [markedChart,std] using chartOne_finite (z:=0) (by norm_num),by norm_num⟩

lemma coordinate_bound_away_pole {δ : ℝ} (hδ : 0<δ) :
    ∃ B : ℝ,1≤B ∧ ∀ z : ℂ,δ≤dist (z:Sphere) ∞ → ‖z‖≤B := by
  let K : Set Sphere:={p | δ≤dist p ∞}
  have hK : IsClosed K:=isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hinfinity : ∞∉K := by simpa [K] using hδ
  have hc:=CannonTileTopology.compact_trace hK hinfinity
  obtain ⟨B,hB⟩:=hc.isBounded.subset_closedBall 0
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro z hz
  have hh:=hB hz
  rw [mem_closedBall,dist_zero_right] at hh
  exact hh.trans (le_max_right _ _)

lemma coordinate_comparison {B : ℝ} (_hB : 0≤B) {z w : ℂ}
    (hz : ‖z‖≤B) (hw : ‖w‖≤B) :
    dist z w≤(B^2+4)*dist (z:Sphere) (w:Sphere) := by
  have he:=coe_dist_sq z w
  have hd : 0<(‖z‖^2+4)*(‖w‖^2+4):=by positivity
  have hz2:=pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hw2:=pow_le_pow_left₀ (norm_nonneg w) hw 2
  have hden : (‖z‖^2+4)*(‖w‖^2+4)≤(B^2+4)^2 := by
    calc
      _ ≤ (B^2+4)*(B^2+4):=mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = _:=by ring
  have hs : dist z w^2 ≤ ((B^2+4)*dist (z:Sphere) (w:Sphere))^2 := by
    have hh:=(div_eq_iff hd.ne').mp he.symm
    have hm:=mul_le_mul_of_nonneg_left hden (sq_nonneg (dist (z:Sphere) (w:Sphere)))
    nlinarith [sq_nonneg (dist z w)]
  have hn : 0≤(B^2+4)*dist (z:Sphere) (w:Sphere):=by positivity
  nlinarith [dist_nonneg (x:=z) (y:=w)]
end CannonMobius

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_ClippedRadialEnergy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Metric Topology
open scoped BigOperators OnePoint

namespace CannonRadialEnergy
attribute [local instance] Classical.propDecidable
open Set Metric

theorem clipped_radial_energy {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    (K : ι → Set X) (c : ι → X) (r w : ι → ℝ) (good : ι → Prop)
    (hr : ∀ i,0 ≤ r i) (hw : ∀ i,0≤w i)
    (p : X) {a b R P : ℝ} (hab : a≤b) (hb : b≤R) (hR : 0≤R)
    (hcell : ∀ i,good i → K i⊆closedBall (c i) (3*r i))
    (hbudget : (∑ i,if good i ∧ (K i∩closedBall p R).Nonempty then
      (min (r i) R)^2 else 0)≤P)
    (D : ℕ) (hbad : (Finset.univ.filter (fun i=>¬good i)).card≤D)
    (hadm : ∀ t∈Icc a b,1≤∑ i,if (K i∩sphere p t).Nonempty then w i else 0) :
    (b-a)^2≤36*(P+(D:ℝ)*R^2)*∑ i,w i^2 := by
  classical
  let act (i : ι) := (K i∩closedBall p R).Nonempty
  let U (i : ι) := K i∩closedBall p R
  let rad (i : ι) := if act i then (if good i then min (r i) R else R) else 0
  let cen (i : ι) := if good i ∧ r i≤R then c i else p
  have hrad (i : ι) : 0 ≤ rad i := by
    dsimp [rad]
    split_ifs
    · exact le_min (hr i) hR
    · exact hR
    · exact le_rfl
  have hU (i : ι) : U i⊆closedBall (cen i) (3*rad i) := by
    intro x hx
    have ha : act i:=⟨x,hx⟩
    dsimp [rad,cen]
    rw [ite_eq_left ha]
    by_cases hg : good i
    · rw [ite_eq_left hg]
      by_cases hrR : r i≤R
      · rw [ite_eq_left ⟨hg,hrR⟩,min_eq_left hrR]
        exact hcell i hg hx.1
      · rw [ite_eq_right (fun h=>hrR h.2),min_eq_right (le_of_not_ge hrR)]
        exact (mem_closedBall.mp hx.2).trans (by linarith)
    · rw [ite_eq_right hg,ite_eq_right (fun h=>hg h.1)]
      exact (mem_closedBall.mp hx.2).trans (by linarith)
  have hbud : (∑ i,rad i^2)≤P+(D:ℝ)*R^2 := by
    have he (i : ι) : rad i^2 ≤
        (if good i ∧ act i then (min (r i) R)^2 else 0)+
        (if ¬good i then R^2 else 0) := by
      by_cases ha : act i <;> by_cases hg : good i <;> simp [rad,ha,hg,sq_nonneg]
    calc
      _ ≤ ∑ i,((if good i ∧ act i then (min (r i) R)^2 else 0)+
          (if ¬good i then R^2 else 0)) := Finset.sum_le_sum (fun i _=>he i)
      _ = (∑ i,if good i ∧ act i then (min (r i) R)^2 else 0)+
          ((Finset.univ.filter (fun i=>¬good i)).card:ℝ)*R^2 := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [←Finset.sum_filter]
        simp
      _ ≤ P+(D:ℝ)*R^2 := add_le_add hbudget
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hbad) (sq_nonneg R))
  have hadm' : ∀ t∈Icc a b,1≤∑ i,if (U i∩sphere p t).Nonempty then w i else 0 := by
    intro t ht
    convert hadm t ht using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply propext
    constructor
    · rintro ⟨x,⟨hx,-⟩,hxt⟩
      exact ⟨x,hx,hxt⟩
    · rintro ⟨x,hx,hxt⟩
      exact ⟨x,⟨hx,(mem_sphere.mp hxt).le.trans (ht.2.trans hb)⟩,hxt⟩
  have hh:=radial_cell_energy_budget hab (show (0:ℝ)≤3 by norm_num) p cen rad w U
    hrad hw hU hbud hadm'
  norm_num at hh ⊢
  exact hh
end CannonRadialEnergy

namespace CannonCarrierCharging
open CannonCells CannonDuality

attribute [local instance] Classical.propDecidable

theorem clipped_spherical_carrier_modulus {X ι κ : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : κ → Set X) (K : κ → Set (OnePoint ℂ)) (v : κ → X) (q : ι → X)
    (mesh η diam : ℝ) (hη : 0<η)
    (hdiam : ∀ d,∀ x∈A d,dist x (v d)≤diam)
    (F : Set (Set X)) (hFn : ∀ E∈F,E.Nonempty)
    (hcover : ∀ x,∃ i,x∈ball (q i) (2*mesh))
    (c : κ → ℂ) (rad : κ → ℝ) (good : κ → Prop)
    (hr : ∀ d,0 ≤ rad d) (p : ℂ) {a b R : ℝ}
    (hab : a≤b) (hb : b≤R) (hR : 0≤R) (D : ℕ)
    (hcell : ∀ d,good d → ((↑) : ℂ → OnePoint ℂ) ⁻¹' K d⊆closedBall (c d) (3*rad d))
    (hbudget : (∑ d,if good d ∧ ((((↑) : ℂ → OnePoint ℂ) ⁻¹' K d)∩closedBall p R).Nonempty
      then (min (rad d) R)^2 else 0)≤(25*(D:ℝ)+1)*R^2)
    (hbad : (Finset.univ.filter (fun d=>¬good d)).card≤D)
    (hconn : ∀ t∈Icc a b,IsPreconnected
      (⋃ (d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val))
    (hcross : ∀ t∈Icc a b,
      ∃ x∈⋃ (d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val,
      ∃ y∈⋃ (d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val,
        ∀ γ : Path x y,range γ∈F)
    (kr kc : ℕ)
    (hrow : ∀ d,(Finset.univ.filter (fun i=>dist (q i) (v d)<2*mesh+η+diam)).card≤kr)
    (hcol : ∀ i,(Finset.univ.filter (fun d=>dist (q i) (v d)<2*mesh+η+diam)).card≤kc) :
    (b-a)^2≤36*(26*(D:ℝ)+1)*R^2*(kr:ℝ)*kc*modulus (fun i=>ball (q i) (2*mesh)) F := by
  classical
  have hF : F.Nonempty := by
    obtain ⟨x,hx,y,hy,hxy⟩:=hcross a ⟨le_rfl,hab⟩
    obtain ⟨γ,-⟩:=CannonFiniteCarrier.path_in_open_enlargement (hconn a ⟨le_rfl,hab⟩)
      isOpen_thickening (self_subset_thickening hη _) hx hy
    exact ⟨range γ,hxy γ⟩
  obtain ⟨_,w,hw,he⟩:=modulus_minimum (fun i=>ball (q i) (2*mesh)) hcover hF hFn
  let J : κ → Finset ι:=fun d=>Finset.univ.filter (fun i=>dist (q i) (v d)<2*mesh+η+diam)
  let W : κ → ℝ:=fun d=>∑ i∈J d,w i
  have hW : ∀ d,0≤W d:=fun d=>Finset.sum_nonneg fun i _=>hw.1 i
  have hiff (d : κ) (t : ℝ) :
      (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty ↔
      ((((↑) : ℂ → OnePoint ℂ) ⁻¹' K d)∩sphere p t).Nonempty := by
    constructor
    · rintro ⟨x,⟨z,hz,rfl⟩,hx⟩
      exact ⟨z,hx,hz⟩
    · rintro ⟨z,hz,hzt⟩
      exact ⟨(z:OnePoint ℂ),⟨z,hzt,rfl⟩,hz⟩
  have hadm : ∀ t∈Icc a b,1≤∑ d,if ((((↑) : ℂ → OnePoint ℂ) ⁻¹' K d)∩sphere p t).Nonempty
      then W d else 0 := by
    intro t ht
    obtain ⟨x,hx,y,hy,hxy⟩:=hcross t ht
    have hh:=carrier_admissible_charging A K K id v q ((↑) '' sphere p t : Set (OnePoint ℂ))
      mesh η diam hη hdiam (fun _=>Subset.rfl) (hconn t ht) hx hy F hxy w hw
    simpa only [W,J,Finset.sum_filter,hiff] using hh
  have hrad:=CannonRadialEnergy.clipped_radial_energy
    (fun d=>((↑) : ℂ → OnePoint ℂ) ⁻¹' K d) c rad W good hr hW p hab hb hR hcell hbudget D hbad hadm
  have heW:=CannonTransfer.overlap_energy J (fun i=>w i) kr kc hrow (by
    intro i
    simpa only [J,Finset.mem_filter,Finset.mem_univ,true_and] using hcol i)
  have hnorm : ∑ i,(w i)^2=‖w‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs]
  calc
    _ ≤ 36*((25*(D:ℝ)+1)*R^2+(D:ℝ)*R^2)*∑ d,W d^2 := hrad
    _ ≤ 36*((25*(D:ℝ)+1)*R^2+(D:ℝ)*R^2)*((kr:ℝ)*kc*∑ i,(w i)^2) :=
      mul_le_mul_of_nonneg_left heW (by positivity)
    _ = _ := by rw [hnorm,he]; ring
end CannonCarrierCharging

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_LocalSubdisk
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators OnePoint

namespace CannonRadialEnergy

lemma local_subdisk (c p : ℂ) {r R K : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hnear : dist c p ≤ r+K*R) :
    ∃ q : ℂ,ball q (min r R)⊆ball c r ∧
      ball q (min r R)⊆ball p ((K+2)*R) := by
  let s:=min r R
  have hs : 0 ≤ s:=le_min hr hR
  have hsr : s ≤ r:=min_le_left _ _
  have hsR : s ≤ R:=min_le_right _ _
  have hn : ¬Disjoint (closedBall c (r-s)) (closedBall p (K*R+s)) := by
    rw [disjoint_closedBall_closedBall_iff (sub_nonneg.mpr hsr) (by positivity)]
    linarith
  obtain ⟨q,hqc,hqp⟩:=Set.not_disjoint_iff_nonempty_inter.mp hn
  refine ⟨q,?_,?_⟩
  · intro x hx
    have ht:=dist_triangle x q c
    have hx':=mem_ball.mp hx
    have hq':=mem_closedBall.mp hqc
    apply mem_ball.mpr
    linarith
  · intro x hx
    have ht:=dist_triangle x q p
    have hx':=mem_ball.mp hx
    have hq':=mem_closedBall.mp hqp
    apply mem_ball.mpr
    nlinarith

theorem local_disjoint_disk_square_budget {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (r : ι → ℝ) (p : ℂ) {R K : ℝ}
    (hr : ∀ i,0 ≤ r i) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hdisj : Pairwise (fun i j=> Disjoint (ball (c i) (r i)) (ball (c j) (r j))))
    (hnear : ∀ i,dist (c i) p ≤ r i+K*R) :
    (∑ i,(min (r i) R)^2) ≤ (K+2)^2*R^2 := by
  choose q hqc hqp using fun i=> local_subdisk (c i) p (hr i) hR hK (hnear i)
  have h:=disjoint_disk_square_budget q (fun i=> min (r i) R) p
    (fun i=> le_min (hr i) hR) (by positivity)
    (fun i j hij=> (hdisj hij).mono (hqc i) (hqc j)) hqp
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem active_local_disk_square_budget {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (r : ι → ℝ) (p : ℂ) (active : ι → Prop) [DecidablePred active]
    {R K : ℝ} (hr : ∀ i,0 ≤ r i) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hdisj : Pairwise (fun i j=> Disjoint (ball (c i) (r i)) (ball (c j) (r j))))
    (hnear : ∀ i,active i → dist (c i) p ≤ r i+K*R) :
    (∑ i,if active i then (min (r i) R)^2 else 0) ≤ (K+2)^2*R^2 := by
  have h:=local_disjoint_disk_square_budget (fun i : {i // active i}=> c i)
    (fun i=> r i) p (fun i=> hr i) hR hK
    (fun i j hij=> hdisj (Subtype.val_injective.ne hij)) (fun i=> hnear i i.property)
  have he : (∑ i ∈ Finset.univ.filter active,(min (r i) R)^2)=
      ∑ i : {i // active i},(min (r i) R)^2 :=
    Finset.sum_subtype _ (by simp) _
  rw [←he,Finset.sum_filter] at h
  exact h

end CannonRadialEnergy

namespace CannonLocalPacking
attribute [local instance] Classical.propDecidable

lemma compact_subset_closedBall_of_frontier_subset {K : Set ℂ} (hK : IsCompact K)
    (c : ℂ) (R : ℝ) (hfront : frontier K ⊆ closedBall c R) :
    K ⊆ closedBall c R := by
  intro z hz
  have hd : DiffContOnCl ℂ (fun w : ℂ=>w-c) K :=
    (differentiable_id.sub_const c).diffContOnCl
  have h:=Complex.norm_le_of_forall_mem_frontier_norm_le hK.isBounded hd
    (fun w hw=>by simpa only [mem_closedBall,dist_eq_norm] using hfront hw)
    (subset_closure hz)
  simpa only [mem_closedBall,dist_eq_norm] using h

lemma tile_ball_dichotomy {K : Set ℂ} (hK : IsClosed K) (p : ℂ) (R : ℝ)
    (hmeet : (K∩closedBall p R).Nonempty) :
    (frontier K∩closedBall p R).Nonempty ∨ closedBall p R ⊆ interior K := by
  by_cases hf : (frontier K∩closedBall p R).Nonempty
  · exact Or.inl hf
  right
  have hsub : closedBall p R ⊆ interior K∪Kᶜ := by
    intro x hx
    by_cases hxK : x∈K
    · left
      by_contra hn
      exact hf ⟨x,⟨subset_closure hxK,hn⟩,hx⟩
    · exact Or.inr hxK
  obtain hi|ho:=(convex_closedBall p R).isPreconnected.subset_or_subset
    isOpen_interior hK.isOpen_compl
    (disjoint_compl_right.mono interior_subset Subset.rfl) hsub
  · exact hi
  · obtain ⟨x,hxK,hxp⟩:=hmeet
    exact (ho hxp hxK).elim

lemma tile_max_disk_control {ν : Type*} (c : ν → ℂ) (r : ν → ℝ)
    (V : Set ν) (s : ν) {K : Set ℂ} (hK : IsCompact K)
    (hmax : ∀ j∈V,r j ≤ r s)
    (hpair : ∀ j∈V,dist (c j) (c s) ≤ r j+r s)
    (hfront : ∀ x∈frontier K,∃ j∈V,x∈closedBall (c j) (r j)) :
    K⊆closedBall (c s) (3*r s) := by
  apply compact_subset_closedBall_of_frontier_subset hK
  intro x hx
  obtain ⟨j,hj,hxj⟩:=hfront x hx
  have ht:=dist_triangle x (c j) (c s)
  have hm:=hmax j hj
  have hp:=hpair j hj
  have hxj':=mem_closedBall.mp hxj
  apply mem_closedBall.mpr
  linarith

lemma frontier_disk_charge {ν : Type*} (c : ν → ℂ) (r : ν → ℝ)
    (V : Set ν) (s : ν) (hs : s∈V) (p : ℂ) {R : ℝ}
    (hpair : ∀ j∈V,dist (c j) (c s) ≤ r j+r s)
    {K : Set ℂ} (hfront : ∀ x∈frontier K,∃ j∈V,x∈closedBall (c j) (r j))
    (hmeet : (frontier K∩closedBall p R).Nonempty) :
    ∃ j∈V,dist (c j) p ≤ r j+3*R ∧ min (r s) R ≤ min (r j) R := by
  obtain ⟨x,hxK,hxp⟩:=hmeet
  obtain ⟨j,hj,hxj⟩:=hfront x hxK
  have hxp':=mem_closedBall.mp hxp
  have hxj':=mem_closedBall.mp hxj
  by_cases hjR : r j ≤ R
  · refine ⟨s,hs,?_,le_rfl⟩
    have ht:=dist_triangle (c s) (c j) p
    have ht':=dist_triangle (c j) x p
    have hp:=hpair j hj
    rw [dist_comm (c j) (c s)] at hp
    rw [dist_comm (c j) x] at ht'
    linarith
  · refine ⟨j,hj,?_,?_⟩
    · have ht:=dist_triangle (c j) x p
      rw [dist_comm (c j) x] at ht
      have hR : 0 ≤ R:=(dist_nonneg.trans hxp')
      linarith
    · rw [min_eq_right (le_of_not_ge hjR)]
      exact min_le_right _ _

end CannonLocalPacking

namespace CannonLocalPacking
attribute [local instance] Classical.propDecidable

lemma sum_indicator_le_one {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    {A : ℝ} (hA : 0 ≤ A) (hP : ∀ i j,P i → P j → i=j) :
    (∑ i,if P i then A else 0) ≤ A := by
  classical
  by_cases h : ∃ i,P i
  · obtain ⟨i,hi⟩:=h
    have he : (∑ j,if P j then A else 0)=A := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hji
        have hj : ¬P j:=fun hj=>hji (hP j i hj hi)
        simp [hj]
      · simp
    exact he.le
  · have hn : ∀ i,¬P i:=by simpa only [not_exists] using h
    simpa [hn] using hA

lemma incidence_sum_le {κ ν : Type*} [Fintype κ] [Fintype ν] [DecidableEq ν]
    (V : κ → Finset ν) (g : ν → ℝ) (hg : ∀ j,0 ≤ g j) (D : ℕ)
    (hinc : ∀ j,(Finset.univ.filter (fun d=>j∈V d)).card ≤ D) :
    (∑ d,∑ j∈V d,g j) ≤ (D:ℝ)*∑ j,g j := by
  classical
  have hs (d : κ) : (∑ j∈V d,g j)=∑ j,if j∈V d then g j else 0 := by simp
  simp_rw [hs]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hinc j) (hg j)

theorem local_active_tile_square_budget {κ ν : Type*} [Fintype κ] [Fintype ν]
    [DecidableEq ν] (c : ν → ℂ) (r : ν → ℝ) (hr : ∀ j,0 ≤ r j)
    (V : κ → Finset ν) (s : κ → ν) (hs : ∀ d,s d∈V d)
    (K : κ → Set ℂ) (hclosed : ∀ d,IsClosed (K d))
    (htile : Pairwise (fun d e=>Disjoint (interior (K d)) (interior (K e))))
    (hpair : ∀ d,∀ j∈V d,dist (c j) (c (s d)) ≤ r j+r (s d))
    (hfront : ∀ d,∀ x∈frontier (K d),∃ j∈V d,x∈closedBall (c j) (r j))
    (hdisj : Pairwise (fun i j=>Disjoint (ball (c i) (r i)) (ball (c j) (r j))))
    (p : ℂ) {R : ℝ} (hR : 0 ≤ R) (D : ℕ)
    (hinc : ∀ j,(Finset.univ.filter (fun d=>j∈V d)).card ≤ D) :
    (∑ d,if (K d∩closedBall p R).Nonempty then (min (r (s d)) R)^2 else 0) ≤
      (25*(D:ℝ)+1)*R^2 := by
  classical
  let near : ν → Prop:=fun j=>dist (c j) p ≤ r j+3*R
  let g : ν → ℝ:=fun j=>if near j then (min (r j) R)^2 else 0
  let whole : κ → Prop:=fun d=>closedBall p R⊆interior (K d)
  have hg : ∀ j,0 ≤ g j:=by intro j; dsimp [g]; split_ifs <;> positivity
  have hnear : (∑ j,g j) ≤ 25*R^2 := by
    have hh:=CannonRadialEnergy.active_local_disk_square_budget c r p near hr hR
      (show (0:ℝ) ≤ 3 by norm_num) hdisj (fun _ hj=>hj)
    norm_num [g] at hh ⊢
    exact hh
  have hw : (∑ d,if whole d then R^2 else 0) ≤ R^2 := by
    apply sum_indicator_le_one whole (sq_nonneg R)
    intro d e hd he
    by_contra hde
    have hpd:=hd (mem_closedBall_self hR)
    have hpe:=he (mem_closedBall_self hR)
    exact Set.disjoint_left.mp (htile hde) hpd hpe
  have hf (d : κ) :
      (if (K d∩closedBall p R).Nonempty then (min (r (s d)) R)^2 else 0) ≤
        (∑ j∈V d,g j)+(if whole d then R^2 else 0) := by
    have hsg : 0 ≤ ∑ j∈V d,g j:=Finset.sum_nonneg (fun j _=>hg j)
    have hwi : 0 ≤ if whole d then R^2 else 0:=by split_ifs <;> positivity
    by_cases ha : (K d∩closedBall p R).Nonempty
    · rw [ite_eq_left ha]
      obtain hb|hb:=tile_ball_dichotomy (hclosed d) p R ha
      · obtain ⟨j,hj,hjn,hle⟩:=frontier_disk_charge c r (V d) (s d) (hs d) p
          (hpair d) (hfront d) hb
        have hle': (min (r (s d)) R)^2 ≤ (min (r j) R)^2:=
          pow_le_pow_left₀ (le_min (hr _) hR) hle 2
        have hgj : g j=(min (r j) R)^2:=ite_eq_left hjn
        have hsum:=Finset.single_le_sum (fun j _=>hg j) hj
        rw [hgj] at hsum
        exact (hle'.trans hsum).trans (le_add_of_nonneg_right hwi)
      · have hb' : whole d:=hb
        rw [ite_eq_left hb']
        have hle:=pow_le_pow_left₀ (le_min (hr (s d)) hR) (min_le_right (r (s d)) R) 2
        exact hle.trans (le_add_of_nonneg_left hsg)
    · rw [ite_eq_right ha]
      exact add_nonneg hsg hwi
  calc
    _ ≤ ∑ d,((∑ j∈V d,g j)+(if whole d then R^2 else 0)) :=
      Finset.sum_le_sum (fun d _=>hf d)
    _ = (∑ d,∑ j∈V d,g j)+(∑ d,if whole d then R^2 else 0) := Finset.sum_add_distrib
    _ ≤ (D:ℝ)*(∑ j,g j)+R^2 := add_le_add (incidence_sum_le V g hg D hinc) hw
    _ ≤ (D:ℝ)*(25*R^2)+R^2 := by gcongr
    _ = _ := by ring

end CannonLocalPacking

namespace CannonTileTopology
open CannonLocalPacking

attribute [local instance] Classical.propDecidable

theorem selected_tile_budget {κ ν : Type*} [Fintype κ] [Fintype ν] [DecidableEq ν]
    (V : κ → Finset ν) (hV : ∀ d,(V d).Nonempty) (pole : ν)
    (K : κ → Set ℂ) (hc : ∀ d,pole∉V d → IsCompact (K d))
    (hd : Pairwise fun d e=>Disjoint (interior (K d)) (interior (K e)))
    (c : ν → ℂ) (r : ν → ℝ) (hr : ∀ j,0 ≤ r j)
    (hdisj : Pairwise fun i j=>Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    (hfront : ∀ d,pole∉V d → ∀ x∈frontier (K d),∃ j∈V d,x∈closedBall (c j) (r j))
    (hpair : ∀ d,pole∉V d → ∀ i∈V d,∀ j∈V d,dist (c i) (c j) ≤ r i+r j)
    (D : ℕ) (hinc : ∀ j,(Finset.univ.filter (fun d=>j∈V d)).card≤D) :
    ∃ s : κ → ν,(∀ d,s d∈V d) ∧
      (∀ d,pole∉V d → K d⊆closedBall (c (s d)) (3*r (s d))) ∧
      (∀ p : ℂ,∀ R : ℝ,0≤R →
        (∑ d,if pole∉V d ∧ (K d∩closedBall p R).Nonempty then (min (r (s d)) R)^2 else 0)
          ≤(25*(D:ℝ)+1)*R^2) ∧
      (Finset.univ.filter (fun d=>¬pole∉V d)).card≤D := by
  classical
  have hm (d : κ) : ∃ j∈V d,∀ i∈V d,r i ≤ r j := Finset.exists_max_image (V d) r (hV d)
  choose s hs hm using hm
  refine ⟨s,hs,?_,?_,?_⟩
  · intro d hdp
    exact tile_max_disk_control c r (V d) (s d) (hc d hdp) (hm d)
      (fun j hj=>hpair d hdp j hj (s d) (hs d)) (hfront d hdp)
  · intro p R hR
    let good : κ → Prop:=fun d=>pole∉V d
    have hi (j : ν) :
        (Finset.univ.filter (fun d : {d // good d}=>j∈V d.val)).card≤D := by
      have he : (Finset.univ.filter (fun d : {d // good d}=>j∈V d.val)).card=
          (Finset.univ.filter (fun d : κ=>good d ∧ j∈V d)).card := by
        apply Finset.card_bij (fun d _=>d.val)
        · intro d hd
          simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hd ⊢
          exact ⟨d.property,hd⟩
        · intro d hd e he hde
          exact Subtype.ext hde
        · intro d hd
          simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hd
          exact ⟨⟨d,hd.1⟩,by simpa using hd.2,rfl⟩
      rw [he]
      apply (Finset.card_le_card (show Finset.univ.filter (fun d=>good d ∧ j∈V d)⊆
        Finset.univ.filter (fun d=>j∈V d) from ?_)).trans (hinc j)
      intro d hd
      simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
        (Finset.mem_filter.mp hd).2.2
    have hh:=local_active_tile_square_budget c r hr (fun d : {d // good d}=>V d.val)
      (fun d=>s d.val) (fun d=>hs d.val) (fun d=>K d.val) (fun d=>(hc d.val d.property).isClosed)
      (fun d e hde=>hd (Subtype.val_injective.ne hde))
      (fun d j hj=>hpair d.val d.property j hj (s d.val) (hs d.val))
      (fun d=>hfront d.val d.property) hdisj p hR D hi
    have he : (∑ d∈Finset.univ.filter good,
        if (K d∩closedBall p R).Nonempty then (min (r (s d)) R)^2 else 0)=
        ∑ d : {d // good d},if (K d.val∩closedBall p R).Nonempty then (min (r (s d.val)) R)^2 else 0 :=
      Finset.sum_subtype _ (by simp) _
    rw [←he,Finset.sum_filter] at hh
    simpa only [good,ite_and] using hh
  · simpa only [not_not] using hinc pole
end CannonTileTopology

namespace CannonTileTopology
open Topology CannonMobius

attribute [local instance] Classical.propDecidable

theorem pole_chart_tile_budget {κ ν : Type*} [Fintype κ] [Fintype ν] [DecidableEq ν]
    (V : κ → Finset ν) (hV : ∀ d,(V d).Nonempty) (pole : ν)
    (K : κ → Set (OnePoint ℂ)) (hclosed : ∀ d,IsClosed (K d))
    (hd : Pairwise fun d e=>Disjoint (interior (K d)) (interior (K e)))
    (z : ν → ℂ) (ρ : ν → ℝ) (hρ : ∀ j,0<ρ j)
    (hsep : ∀ i j,i≠j → ρ i+ρ j≤dist (z i) (z j))
    (hfront : ∀ d,frontier (K d)⊆⋃ j∈V d,((↑) '' closedBall (z j) (ρ j) : Set (OnePoint ℂ)))
    (hpair : ∀ d,∀ i∈V d,∀ j∈V d,i≠j → dist (z i) (z j)=ρ i+ρ j)
    (hpinc : ∀ d,(z pole:OnePoint ℂ)∈K d → pole∈V d)
    (N : OnePoint ℂ ≃ₜ OnePoint ℂ) (hN : N∈biholomorphic) (hpole : N (z pole)=∞)
    (D : ℕ) (hinc : ∀ j,(Finset.univ.filter (fun d=>j∈V d)).card≤D) :
    let T : κ → Set ℂ:=fun d=>((↑) : ℂ → OnePoint ℂ) ⁻¹' (N '' K d)
    ∃ c : κ → ℂ,∃ r : κ → ℝ,∃ s : κ → ν,
      (∀ d,s d∈V d) ∧ (∀ d,0 ≤ r d) ∧
      (∀ d,pole∉V d → T d⊆closedBall (c d) (3*r d)) ∧
      (∀ p : ℂ,∀ R : ℝ,0≤R →
        (∑ d,if pole∉V d ∧ (T d∩closedBall p R).Nonempty then (min (r d) R)^2 else 0)
          ≤(25*(D:ℝ)+1)*R^2) ∧
      (Finset.univ.filter (fun d=>¬pole∉V d)).card≤D := by
  classical
  dsimp only
  let T : κ → Set ℂ:=fun d=>((↑) : ℂ → OnePoint ℂ) ⁻¹' (N '' K d)
  obtain ⟨c₀,r₀,hr₀,hb₀,hc₀,hd₀⟩:=finite_packing_at_vertex z ρ hρ hsep N hN pole hpole
  let c : ν → ℂ:=fun j=>if h:j=pole then 0 else c₀ ⟨j,h⟩
  let r : ν → ℝ:=fun j=>if h:j=pole then 0 else r₀ ⟨j,h⟩
  have hr (j : ν) : 0 ≤ r j := by
    dsimp [r]
    split_ifs with h
    · exact le_rfl
    · exact (hr₀ ⟨j,h⟩).le
  have hc (j : ν) (hj : j≠pole) :
      N '' ((↑) '' closedBall (z j) (ρ j) : Set (OnePoint ℂ))=(↑) '' closedBall (c j) (r j) := by
    simpa only [c,r,dite_eq_right hj] using hc₀ ⟨j,hj⟩
  have hdisj : Pairwise fun i j=>Disjoint (ball (c i) (r i)) (ball (c j) (r j)) := by
    intro i j hij
    by_cases hi : i=pole
    · simp [r,hi]
    by_cases hj : j=pole
    · simp [r,hj]
    simpa only [c,r,dite_eq_right hi,dite_eq_right hj] using
      hd₀ (show (⟨i,hi⟩ : {j // j≠pole})≠⟨j,hj⟩ from fun h=>hij (congrArg Subtype.val h))
  have hTc (d : κ) (hdp : pole∉V d) : IsCompact (T d) := by
    apply compact_trace (N.isClosedMap _ (hclosed d))
    rintro ⟨x,hx,he⟩
    have hex : x=(z pole:OnePoint ℂ):=N.injective (he.trans hpole.symm)
    subst x
    exact hdp (hpinc d hx)
  have hTd : Pairwise fun d e=>Disjoint (interior (T d)) (interior (T e)) := by
    intro d e hde
    have hh := (hd hde).image N.injective.injOn (subset_univ _) (subset_univ _)
    rw [N.image_interior,N.image_interior] at hh
    have hh':=hh.preimage ((↑) : ℂ → OnePoint ℂ)
    rw [OnePoint.isOpenMap_coe.preimage_interior_eq_interior_preimage OnePoint.continuous_coe,
      OnePoint.isOpenMap_coe.preimage_interior_eq_interior_preimage OnePoint.continuous_coe] at hh'
    exact hh'
  have hTf (d : κ) (hdp : pole∉V d) :
      ∀ x∈frontier (T d),∃ j∈V d,x∈closedBall (c j) (r j) := by
    intro x hx
    rw [show frontier (T d)=((↑) : ℂ → OnePoint ℂ) ⁻¹' frontier (N '' K d) from trace_frontier _,
      ←N.image_frontier] at hx
    obtain ⟨y,hy,hey⟩:=hx
    obtain ⟨j,hj,u,hu,heu⟩:=mem_iUnion₂.mp (hfront d hy)
    have hjp : j≠pole:=fun h=>hdp (h ▸ hj)
    have hh : (x:OnePoint ℂ)∈N '' ((↑) '' closedBall (z j) (ρ j) : Set (OnePoint ℂ)):=
      ⟨y,⟨u,hu,heu⟩,hey⟩
    rw [hc j hjp] at hh
    obtain ⟨v,hv,hev⟩:=hh
    have hvx : v=x:=OnePoint.coe_injective hev
    exact ⟨j,hj,hvx ▸ hv⟩
  have hTp (d : κ) (hdp : pole∉V d) :
      ∀ i∈V d,∀ j∈V d,dist (c i) (c j) ≤ r i+r j := by
    intro i hi j hj
    by_cases hij : i=j
    · subst j
      simp only [dist_self]
      exact add_nonneg (hr i) (hr i)
    exact transformed_disks_touch N (hρ i) (hρ j) (hpair d i hi j hj hij)
      (hc i (fun h=>hdp (h ▸ hi))) (hc j (fun h=>hdp (h ▸ hj)))
  obtain ⟨s,hs,hcell,hbud,hbad⟩:=selected_tile_budget V hV pole T hTc hTd c r hr hdisj hTf hTp D hinc
  exact ⟨(fun d=>c (s d)),(fun d=>r (s d)),s,hs,(fun d=>hr (s d)),hcell,hbud,hbad⟩
end CannonTileTopology

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_SqDiffNormDiff
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
namespace CannonRadialWitness
open Set Metric

lemma sq_diff_le_of_norm_diff {u v η : ℝ} (hu : 0≤u) (hv : 0≤v)
    (hlo : -η≤u-v) (hhi : u-v≤η) (hs : u+v≤3) :
    -3*η≤u^2-v^2 ∧ u^2-v^2≤3*η := by
  have he : 0≤η:=by linarith
  have hsum : 0≤u+v:=by linarith
  constructor
  · nlinarith [mul_nonneg (show 0≤u-v+η by linarith) hsum,
      mul_nonneg he (show 0≤3-(u+v) by linarith)]
  · nlinarith [mul_nonneg (show 0≤η-(u-v) by linarith) hsum,
      mul_nonneg he (show 0≤3-(u+v) by linarith)]

lemma norm_one_sq (z : ℂ) : ‖z-1‖^2=‖z‖^2-2*z.re+1 := by
  simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,
    Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero]
  ring

theorem two_center_small {E : Set ℂ} (hE : IsPreconnected E) {x y : ℂ}
    (hx : x∈E) (hy : y∈E) (hxn : ‖x‖≤1) {η : ℝ} (hη : 0≤η) (hη1 : η≤1)
    (h0 : ∀ z∈E,|‖z‖-‖x‖|≤η)
    (h1 : ∀ z∈E,|‖z-1‖-‖x-1‖|≤η) :
    dist x y^2≤102*η := by
  have hn (z : ℂ) (hz : z∈E) : ‖z‖≤2 := by
    have hh:=(abs_le.mp (h0 z hz)).2
    linarith
  have hns (z : ℂ) (hz : z∈E) :
      -3*η≤‖z‖^2-‖x‖^2 ∧ ‖z‖^2-‖x‖^2≤3*η :=
    sq_diff_le_of_norm_diff (norm_nonneg _) (norm_nonneg _)
      (abs_le.mp (h0 z hz)).1 (abs_le.mp (h0 z hz)).2 (by linarith [hn z hz])
  have hn1x : ‖x-1‖≤2 := by
    have ht:=norm_sub_le x (1:ℂ)
    norm_num at ht
    linarith
  have hn1 (z : ℂ) (hz : z∈E) : ‖z-1‖≤3 := by
    have ht:=norm_sub_le z (1:ℂ)
    norm_num at ht
    linarith [hn z hz]
  have hns1 (z : ℂ) (hz : z∈E) :
      -5*η≤‖z-1‖^2-‖x-1‖^2 ∧ ‖z-1‖^2-‖x-1‖^2≤5*η := by
    have hd:=abs_le.mp (h1 z hz)
    have hs : ‖z-1‖+‖x-1‖≤5:=by linarith [hn1 z hz]
    have hsum : 0≤‖z-1‖+‖x-1‖:=by positivity
    constructor
    · nlinarith [mul_nonneg (show 0≤‖z-1‖-‖x-1‖+η by linarith) hsum,
        mul_nonneg hη (show 0≤5-(‖z-1‖+‖x-1‖) by linarith)]
    · nlinarith [mul_nonneg (show 0≤η-(‖z-1‖-‖x-1‖) by linarith) hsum,
        mul_nonneg hη (show 0≤5-(‖z-1‖+‖x-1‖) by linarith)]
  have hre (z : ℂ) (hz : z∈E) : -(4*η)≤z.re-x.re ∧ z.re-x.re≤4*η := by
    have hh:=hns z hz
    have hh1:=hns1 z hz
    rw [norm_one_sq z,norm_one_sq x] at hh1
    constructor <;> linarith
  have hres (z : ℂ) (hz : z∈E) : -3≤z.re+x.re ∧ z.re+x.re≤3 := by
    have hz':=abs_le.mp (Complex.abs_re_le_norm z)
    have hx':=abs_le.mp (Complex.abs_re_le_norm x)
    constructor <;> linarith [hn z hz]
  have hre2 (z : ℂ) (hz : z∈E) : -12*η≤z.re^2-x.re^2 ∧ z.re^2-x.re^2≤12*η := by
    have habs : |z.re^2-x.re^2|≤12*η := by
      calc
        _ = |z.re-x.re| * |z.re+x.re| := by rw [←abs_mul]; congr 1; ring
        _ ≤ (4*η)*3 := mul_le_mul (abs_le.mpr (hre z hz))
          (abs_le.mpr (hres z hz)) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    constructor <;> linarith [abs_le.mp habs]
  have him2 (z : ℂ) (hz : z∈E) : -15*η≤z.im^2-x.im^2 ∧ z.im^2-x.im^2≤15*η := by
    have hh:=hns z hz
    have hh':=hre2 z hz
    rw [←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq] at hh
    simp only [Complex.normSq_apply] at hh
    constructor <;> nlinarith
  have hw : ∃ w∈E,w.im=(x.im+y.im)/2 := by
    rcases le_total x.im y.im with hxy|hyx
    · exact hE.intermediate_value hx hy Complex.continuous_im.continuousOn
        (show (x.im+y.im)/2∈Icc x.im y.im by constructor <;> linarith)
    · exact hE.intermediate_value hy hx Complex.continuous_im.continuousOn
        (show (x.im+y.im)/2∈Icc y.im x.im by constructor <;> linarith)
  obtain ⟨w,hw,hwim⟩:=hw
  have himdiff : (x.im-y.im)^2≤90*η := by
    have hhy:=him2 y hy
    have hhw:=him2 w hw
    rw [hwim] at hhw
    nlinarith
  have hrediff : (x.re-y.re)^2≤12*η := by
    have hr:=hre y hy
    have hxre:=abs_le.mp (Complex.abs_re_le_norm x)
    have hyre:=abs_le.mp (Complex.abs_re_le_norm y)
    have hb : |y.re-x.re|≤3:=abs_le.mpr (by constructor <;> linarith [hn y hy])
    have hm:=mul_le_mul (abs_le.mpr hr) hb (abs_nonneg (y.re-x.re)) (by positivity : 0≤4*η)
    rw [←sq, sq_abs] at hm
    nlinarith
  rw [dist_eq_norm,←Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  nlinarith

theorem two_center_band {E : Set ℂ} (hE : IsPreconnected E) {x y : ℂ}
    (hx : x∈E) (hy : y∈E) (hxn : ‖x‖≤1) {η : ℝ} (hη : 0≤η) (hη1 : η≤1)
    (hxy : 102*η<dist x y^2) :
    ∃ c : ℂ,(c=0 ∨ c=1) ∧ ∃ a b : ℝ,0≤a ∧ a≤b ∧ b≤3 ∧ b-a=η ∧
      ∃ u∈E,∃ v∈E,dist u c≤a ∧ b≤dist v c := by
  have hn : ¬((∀ z∈E,|‖z‖-‖x‖|≤η) ∧ (∀ z∈E,|‖z-1‖-‖x-1‖|≤η)) := by
    intro h
    exact (not_lt_of_ge (two_center_small hE hx hy hxn hη hη1 h.1 h.2)) hxy
  have hw : ∃ c : ℂ,(c=0 ∨ c=1) ∧ dist x c≤2 ∧ ∃ z∈E,η < |dist z c-dist x c| := by
    push Not at hn
    by_cases h0 : ∀ z∈E,|‖z‖-‖x‖|≤η
    · obtain ⟨z,hz,hh⟩:=hn h0
      refine ⟨1,Or.inr rfl,?_,z,hz,?_⟩
      · have hh:=norm_sub_le x (1:ℂ)
        norm_num at hh
        rw [dist_eq_norm]
        linarith
      · simpa only [dist_eq_norm] using hh
    · push Not at h0
      obtain ⟨z,hz,hh⟩:=h0
      exact ⟨0,Or.inl rfl,by simpa only [dist_zero_right] using hxn.trans (by norm_num),
        z,hz,by simpa only [dist_zero_right] using hh⟩
  obtain ⟨c,hc,hxc,z,hz,hh⟩:=hw
  refine ⟨c,hc,?_⟩
  rcases lt_abs.mp hh with hp|hm
  · exact ⟨dist x c,dist x c+η,dist_nonneg,by linarith,by linarith,by ring,
      x,hx,z,hz,le_rfl,by linarith⟩
  · exact ⟨dist x c-η,dist x c,by linarith [dist_nonneg (x:=z) (y:=c)],
      by linarith,by linarith,by ring,z,hz,x,hx,by linarith,le_rfl⟩

lemma normalized_dist (p q u v : ℂ) {R : ℝ} (hpq : dist p q=R) :
    dist ((u-p)/(q-p)) ((v-p)/(q-p))=dist u v/R := by
  rw [dist_eq_norm,←sub_div]
  have he : (u-p)-(v-p)=u-v:=by ring
  rw [he,norm_div,←dist_eq_norm,←dist_eq_norm,dist_comm q p,hpq]

theorem two_center_band_scaled {E : Set ℂ} (hE : IsPreconnected E) {x y p q : ℂ}
    (hx : x∈E) (hy : y∈E) {R η : ℝ} (hR : 0<R) (hpq : dist p q=R)
    (hxp : dist x p≤R) (hη : 0≤η) (hη1 : η≤1)
    (hxy : 102*η*R^2<dist x y^2) :
    ∃ c : ℂ,(c=p ∨ c=q) ∧ ∃ a b : ℝ,0≤a ∧ a≤b ∧ b≤3*R ∧ b-a=η*R ∧
      ∃ u∈E,∃ v∈E,dist u c≤a ∧ b≤dist v c := by
  let f : ℂ → ℂ:=fun z=>(z-p)/(q-p)
  have hf : Continuous f:=(continuous_id.sub continuous_const).div_const _
  have hfp : f p=0:=by simp [f]
  have hpq0 : q-p≠0:=by
    intro h
    have hh : q=p:=sub_eq_zero.mp h
    simp [hh] at hpq
    linarith
  have hfq : f q=1:=by simp [f,hpq0]
  have hfd (u v : ℂ) : dist (f u) (f v)=dist u v/R:=normalized_dist p q u v hpq
  have hxn : ‖f x‖≤1:=by
    rw [←dist_zero_right,←hfp,hfd]
    exact (div_le_one hR).mpr hxp
  have hxy' : 102*η<dist (f x) (f y)^2 := by
    rw [hfd,div_pow]
    exact (lt_div_iff₀ (sq_pos_of_pos hR)).mpr hxy
  obtain ⟨c,hc,a,b,ha,hab,hb,hw,u,⟨u',hu,rfl⟩,v,⟨v',hv,rfl⟩,huc,hvc⟩:=
    two_center_band (hE.image f hf.continuousOn) (mem_image_of_mem f hx)
      (mem_image_of_mem f hy) hxn hη hη1 hxy'
  have hband (c' : ℂ) (he : f c'=c) :
      ∃ a b : ℝ,0≤a ∧ a≤b ∧ b≤3*R ∧ b-a=η*R ∧
        ∃ u∈E,∃ v∈E,dist u c'≤a ∧ b≤dist v c' := by
    refine ⟨a*R,b*R,mul_nonneg ha hR.le,mul_le_mul_of_nonneg_right hab hR.le,
      mul_le_mul_of_nonneg_right hb hR.le,?_,u',hu,v',hv,?_,?_⟩
    · rw [←sub_mul,hw]
    · rw [←he,hfd] at huc
      exact (div_le_iff₀ hR).mp huc
    · rw [←he,hfd] at hvc
      exact (le_div_iff₀ hR).mp hvc
  rcases hc with rfl|rfl
  · exact ⟨p,Or.inl rfl,hband p hfp⟩
  · exact ⟨q,Or.inr rfl,hband q hfq⟩

end CannonRadialWitness

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_TracePreconnected
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonRadialWitness
open Set Metric Topology CannonMobius
open scoped OnePoint

lemma trace_preconnected {S : Set Sphere} (hS : IsPreconnected S) (hinf : ∞∉S) :
    IsPreconnected (((↑) : ℂ → Sphere) ⁻¹' S) := by
  apply OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
  have he : ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' S)=S := by
    apply image_preimage_eq_of_subset
    intro y hy
    exact OnePoint.ne_infty_iff_exists.mp (fun he=>hinf (he ▸ hy))
  rwa [he]

theorem spherical_two_center_band {S : Set Sphere} (hS : IsPreconnected S)
    {x p q : ℂ} {y : Sphere} (hx : (x:Sphere)∈S) (hy : y∈S)
    {R η : ℝ} (hR : 0<R) (hpq : dist p q=R) (hxp : dist x p≤R)
    (hη : 0≤η) (hη1 : η≤1) (hxy : 102*η*R^2<dist (x:Sphere) y^2) :
    ∃ c : ℂ,(c=p ∨ c=q) ∧ ∃ a b : ℝ,0≤a ∧ a≤b ∧ b≤3*R ∧ b-a=η*R ∧
      ∃ u∈S,∃ v∈S,u∈((↑) '' closedBall c a : Set Sphere) ∧
        v∉((↑) '' ball c b : Set Sphere) := by
  by_cases hinf : ∞∈S
  · refine ⟨p,Or.inl rfl,R,R+η*R,hR.le,?_,?_,by ring,(x:Sphere),hx,∞,hinf,⟨x,hxp,rfl⟩,?_⟩
    · nlinarith
    · nlinarith
    · rintro ⟨z,_hz,he⟩
      exact OnePoint.coe_ne_infty z he
  · obtain ⟨y',rfl⟩:=OnePoint.ne_infty_iff_exists.mp (show y≠∞ from fun he=>hinf (he ▸ hy))
    have hxy' : 102*η*R^2<dist x y'^2 := by
      apply hxy.trans_le
      exact pow_le_pow_left₀ dist_nonneg (coe_dist_le x y') 2
    obtain ⟨c,hc,a,b,ha,hab,hb,hw,u,hu,v,hv,hu',hv'⟩:=two_center_band_scaled
      (trace_preconnected hS hinf) hx hy hR hpq hxp hη hη1 hxy'
    refine ⟨c,hc,a,b,ha,hab,hb,hw,(u:Sphere),hu,(v:Sphere),hv,⟨u,hu',rfl⟩,?_⟩
    rintro ⟨z,hz,hez⟩
    have hzv : z=v:=OnePoint.coe_injective hez
    subst z
    exact not_lt_of_ge hv' hz

lemma continuum_point_at_radius {S : Set Sphere} (hS : IsPreconnected S)
    {p : ℂ} (hp : (p:Sphere)∈S) (hinf : ∞∈S) {R : ℝ} (hR : 0≤R) :
    ∃ q : ℂ,(q:Sphere)∈S ∧ dist p q=R := by
  let f : C(Sphere,Sphere):=ContinuousMap.id Sphere
  have h1 : f (p:Sphere)∈((↑) '' closedBall p R : Set Sphere):=⟨p,mem_closedBall_self hR,rfl⟩
  have h2 : f ∞∉((↑) '' ball p R : Set Sphere) := by
    rintro ⟨z,_hz,he⟩
    exact OnePoint.coe_ne_infty z he
  obtain ⟨x,hx,z,hz,hzx⟩:=CannonCarrierCharging.spherical_radial_level_preimage f S hS p hp hinf h1 h2 R ⟨le_rfl,le_rfl⟩
  refine ⟨z,?_,?_⟩
  · exact hzx ▸ hx
  · simpa only [mem_sphere,dist_comm] using hz
end CannonRadialWitness

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_ThreeMarksAvoidTwo
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
namespace CannonFiniteNormalization
open Set Metric

variable {X Y : Type*} [MetricSpace X]

lemma three_marks_avoid_two_points (v : Fin 3 → X) {sep : ℝ}
    (hv : ∀ i j,i≠j → sep≤dist (v i) (v j)) (x y : X) :
    ∃ i,sep/2≤dist x (v i) ∧ sep/2≤dist y (v i) := by
  classical
  by_contra hn
  have hc (i : Fin 3) : dist x (v i) < sep/2 ∨ dist y (v i) < sep/2 := by
    by_cases hi : sep/2≤dist x (v i)
    · exact Or.inr (lt_of_not_ge (fun hh=>hn ⟨i,hi,hh⟩))
    · exact Or.inl (lt_of_not_ge hi)
  let b : Fin 3 → Bool:=fun i=>decide (dist x (v i) < sep/2)
  have hb : Function.Injective b := by
    intro i j hij
    by_contra hne
    have hsv:=hv i j hne
    have hd (z : X) (hi : dist z (v i) < sep/2) (hj : dist z (v j) < sep/2) : False := by
      have ht:=dist_triangle (v i) z (v j)
      rw [dist_comm (v i) z] at ht
      linarith
    have heq : (dist x (v i) < sep/2)↔(dist x (v j) < sep/2) := by
      simpa only [b,decide_eq_decide] using hij
    by_cases hi : dist x (v i) < sep/2
    · exact hd x hi (heq.mp hi)
    · exact hd y ((hc i).resolve_left hi) ((hc j).resolve_left (fun hj=>hi (heq.mpr hj)))
  have hh:=Fintype.card_le_of_injective b hb
  norm_num at hh

end CannonFiniteNormalization

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Topology_ThreeSeparation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonFiniteNormalization
open Set Metric Topology CannonMobius
open scoped OnePoint

lemma three_separation {X : Type*} [MetricSpace X] (v : Fin 3 → X)
    (hv : Function.Injective v) :
    ∃ s : ℝ,0 < s ∧ ∀ i j,i≠j → s≤dist (v i) (v j) := by
  let s:=min (dist (v 0) (v 1)) (min (dist (v 0) (v 2)) (dist (v 1) (v 2)))
  have hpos (i j : Fin 3) (hij : i≠j) : 0<dist (v i) (v j):=dist_pos.mpr (hv.ne hij)
  refine ⟨s,lt_min (hpos 0 1 (by decide)) (lt_min (hpos 0 2 (by decide)) (hpos 1 2 (by decide))),?_⟩
  have h01 : s≤dist (v 0) (v 1):=min_le_left _ _
  have h02 : s≤dist (v 0) (v 2):=(min_le_right _ _).trans (min_le_left _ _)
  have h12 : s≤dist (v 1) (v 2):=(min_le_right _ _).trans (min_le_right _ _)
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact h01
  · exact h02
  · rwa [dist_comm]
  · exact h12
  · rwa [dist_comm]
  · rwa [dist_comm]

theorem uniform_relative_chart_selection :
    ∃ C : ℝ,1≤C ∧ ∀ {X : Type*},∀ [MetricSpace X],
    ∀ (f : X → Sphere) (v : Fin 3 → X) (s : ℝ),0 < s →
      (∀ i j,i≠j → s≤dist (v i) (v j)) → (∀ i,f (v i)=std i) →
    ∀ (o b : X) (R : ℝ), R ≤ s / 2 → R≤dist o b →
      ∃ i : Fin 3,R≤dist o (v i) ∧ ∃ u : X,R≤dist o u ∧
        ∃ x p : ℂ,markedChart i (f o)=(x:Sphere) ∧
          markedChart i (f u)=(p:Sphere) ∧ dist x p≤C*dist (f o) (f b) := by
  obtain ⟨t,ht,hstd⟩:=three_separation std std_injective
  let δ:=t/4
  have hδ : 0<δ:=by dsimp [δ]; positivity
  obtain ⟨B,hB,hbound⟩:=coordinate_bound_away_pole hδ
  let C:=max 1 (max (B^2+4) ((B+4)/δ))
  have hC : 1≤C:=le_max_left _ _
  have hC1 : B^2+4≤C:=(le_max_left _ _).trans (le_max_right _ _)
  have hC2 : (B+4)/δ≤C:=(le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro X _ f v s hs hv hmark o b R hRs hb
  obtain ⟨i,hi,hfi⟩:=three_marks_two_metrics v std hv hstd o (f o)
  have hdist (y : Sphere) : dist (markedChart i y) ∞=dist y (std i) := by
    rw [←markedChart_pole i]
    exact (markedChart_isometry i).dist_eq _ _
  have hxo : markedChart i (f o)≠∞ := by
    intro he
    have hh:=hdist (f o)
    rw [he,dist_self] at hh
    linarith
  obtain ⟨x,hx⟩:=OnePoint.ne_infty_iff_exists.mp hxo
  have hxn : ‖x‖≤B := by
    apply hbound
    rw [hx,hdist]
    exact (by dsimp [δ]; linarith : δ≤t/2).trans hfi
  by_cases hsmall : dist (f o) (f b)<δ
  · have hbfar : δ≤dist (markedChart i (f b)) ∞ := by
      rw [hdist]
      have hh:=dist_triangle (f o) (f b) (std i)
      dsimp [δ] at *
      linarith
    have hbfin : markedChart i (f b)≠∞ := by intro he; rw [he,dist_self] at hbfar; linarith
    obtain ⟨p,hp⟩:=OnePoint.ne_infty_iff_exists.mp hbfin
    refine ⟨i,hRs.trans hi,b,hb,x,p,hx.symm,hp.symm,?_⟩
    have hpn : ‖p‖≤B:=hbound p (by rwa [hp])
    calc
      dist x p ≤ (B^2+4)*dist (x:Sphere) (p:Sphere):=coordinate_comparison (by linarith) hxn hpn
      _ = (B^2+4)*dist (f o) (f b):=by rw [hx,hp,(markedChart_isometry i).dist_eq]
      _ ≤ C*dist (f o) (f b):=mul_le_mul_of_nonneg_right hC1 dist_nonneg
  · obtain ⟨j,hj,hij⟩:=three_marks_avoid_two_points v hv o (v i)
    have hne : i≠j := by intro he; rw [he,dist_self] at hij; linarith
    obtain ⟨p,hp,hpn⟩:=markedChart_other i j hne
    refine ⟨i,hRs.trans hi,v j,hRs.trans hj,x,p,hx.symm,by rw [hmark,hp],?_⟩
    calc
      dist x p ≤ ‖x‖+‖p‖:=dist_le_norm_add_norm _ _
      _ ≤ B+4:=add_le_add hxn hpn
      _ = ((B+4)/δ)*δ:=by field_simp
      _ ≤ ((B+4)/δ)*dist (f o) (f b):=mul_le_mul_of_nonneg_left (le_of_not_gt hsmall) (by positivity)
      _ ≤ C*dist (f o) (f b):=mul_le_mul_of_nonneg_right hC2 dist_nonneg
end CannonFiniteNormalization

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_Modulus_PreimageCarrierPostcompose
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonCarrierCharging
open Set Metric Topology CannonMobius CannonUniformization CannonRadialWitness
open scoped OnePoint

lemma preimage_carrier_postcompose {X Y Z κ : Type*}
    (A : κ → Set X) (K : κ → Set Y) (f : X → Y) (N : Y → Z)
    (hpre : ∀ S : Set Y,f ⁻¹' S ⊆ ⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val) :
    ∀ S : Set Z,(N ∘ f) ⁻¹' S ⊆ ⋃(d : {d : κ // (S∩N '' K d).Nonempty}),A d.val := by
  intro S x hx
  obtain ⟨d,hd⟩:=mem_iUnion.mp (hpre (N ⁻¹' S) hx)
  obtain ⟨y,hy,hyk⟩:=d.property
  exact mem_iUnion.mpr ⟨⟨d.val,⟨N y,hy,⟨y,hyk,rfl⟩⟩⟩,hd⟩

theorem relative_radial_carrier_witness :
    ∃ C : ℝ,1 ≤ C ∧ ∀ {X κ : Type*},∀ [MetricSpace X],
    ∀ (L σ : ℝ),
      (∀ o u v : X,∀ s : ℝ,0 < s → dist o u ≤ s → dist o v ≤ s →
        JoinedIn (closedBall o (L*s)) u v) →
      (∀ o u v : X,∀ s : ℝ,0 < s → s ≤ dist o u → s ≤ dist o v →
        JoinedIn (ball o (σ*s))ᶜ u v) →
    ∀ (A : κ → Set X) (K : κ → Set Sphere) (f : C(X,Sphere)),
      (∀ S : Set Sphere,f ⁻¹' S ⊆ ⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val) →
    ∀ (v : Fin 3 → X) (s : ℝ),0 < s →
      (∀ i j,i≠j → s ≤ dist (v i) (v j)) → (∀ i,f (v i)=std i) →
    ∀ (o a₀ b₀ : X) (r R ε η : ℝ),0 < r → 0<R → R  ≤  s/2 →
      dist o a₀ ≤ r → R ≤ dist o b₀ →
      0<dist (f o) (f b₀) → 0<ε → 0 ≤ η → η ≤ 1 → 102*η*C^2<ε^2 →
      ε*dist (f o) (f b₀)<dist (f o) (f a₀) →
    ∃ i : Fin 3,∃ p : ℂ,∃ a b : ℝ,0 ≤ a ∧ a ≤ b ∧
      b ≤ 3*(C*dist (f o) (f b₀)) ∧ b-a=η*(C*dist (f o) (f b₀)) ∧
      ∀ t∈Icc a b,
        ∃ x∈⋃(d : {d : κ // (((↑) '' sphere p t : Set Sphere)∩markedChart i '' K d).Nonempty}),A d.val,
        ∃ y∈⋃(d : {d : κ // (((↑) '' sphere p t : Set Sphere)∩markedChart i '' K d).Nonempty}),A d.val,
          ∀ γ : Path x y,range γ∈annulusFamily o (L*r) (σ*R) := by
  obtain ⟨C,hC,hsel⟩:=CannonFiniteNormalization.uniform_relative_chart_selection
  refine ⟨C,hC,?_⟩
  intro X κ _ L σ hinner houter A K f hpre v s hs hv hmark o a₀ b₀ r R ε η hr hR hRs ha₀ hb₀ hdb hε hη hη1 hηε hdiff
  obtain ⟨i,hi,u,hu,x,p,hx,hp,hxp⟩:=hsel f v s hs hv hmark o b₀ R hRs hb₀
  let g : C(X,Sphere):=⟨fun y=>markedChart i (f y),(markedChart i).continuous.comp f.continuous⟩
  have hgpole : g (v i)=∞:=by change markedChart i (f (v i))=∞; rw [hmark,markedChart_pole]
  have hiE:=hinner o o a₀ r hr (by simpa using hr.le) ha₀
  have hoF:=houter o u (v i) R hR hu hi
  let γ : Path o a₀:=hiE.somePath
  let ζ : Path u (v i):=hoF.somePath
  let E:=range γ
  let F:=range ζ
  have hE : IsPreconnected E:=isPreconnected_range γ.continuous
  have hF : IsPreconnected F:=isPreconnected_range ζ.continuous
  have hEa : a₀∈E:=⟨1,γ.target⟩
  have hEo : o∈E:=⟨0,γ.source⟩
  have hFu : u∈F:=⟨0,ζ.source⟩
  have hFv : v i∈F:=⟨1,ζ.target⟩
  have hEin : E ⊆ closedBall o (L*r):=by rintro y ⟨t,rfl⟩; exact hiE.somePath_mem t
  have hFout : F ⊆ (ball o (σ*R))ᶜ:=by rintro y ⟨t,rfl⟩; exact hoF.somePath_mem t
  have hgF : IsPreconnected (g '' F):=hF.image g g.continuous.continuousOn
  have hFp : (p:Sphere)∈g '' F:=⟨u,hFu,hp⟩
  have hFinf : ∞∈g '' F:=⟨v i,hFv,hgpole⟩
  let S:=C*dist (f o) (f b₀)
  have hS : 0<S:=mul_pos (by linarith) hdb
  obtain ⟨q,hq,hpq⟩:=continuum_point_at_radius hgF hFp hFinf hS.le
  have hxy : 102*η*S^2<dist (x:Sphere) (g a₀)^2 := by
    have he : dist (x:Sphere) (g a₀)=dist (f o) (f a₀) := by
      rw [←hx]
      exact (markedChart_isometry i).dist_eq _ _
    rw [he]
    have hh:=mul_lt_mul_of_pos_right hηε (sq_pos_of_pos hdb)
    have hh' : (ε*dist (f o) (f b₀))^2<dist (f o) (f a₀)^2:=
      pow_lt_pow_left₀ hdiff (by positivity) (by decide)
    dsimp [S]
    nlinarith [hh']
  obtain ⟨c,hc,a,b,ha,hab,hb,hw,uE,huE,vE,hvE,huE',hvE'⟩:=spherical_two_center_band
    (hE.image g g.continuous.continuousOn) (show (x:Sphere)∈g '' E from ⟨o,hEo,hx⟩)
    (mem_image_of_mem g hEa) hS hpq hxp hη hη1 hxy
  have hcF : (c:Sphere)∈g '' F:=by rcases hc with rfl|rfl; exact hFp; exact hq
  obtain ⟨uF,huF,hguF⟩:=hcF
  obtain ⟨uE,huE,rfl⟩:=huE
  obtain ⟨vE,hvE,rfl⟩:=hvE
  refine ⟨i,c,a,b,ha,hab,hb,hw,?_⟩
  apply spherical_continua_carrier_crossing g A (fun d=>markedChart i '' K d)
    (preimage_carrier_postcompose A K f (markedChart i) hpre) E F hE hF
    o (L*r) (σ*R) hEin hFout c a b
    ⟨uE,huE,vE,hvE,huE',hvE'⟩
  refine ⟨uF,huF,v i,hFv,?_,?_⟩
  · exact ⟨c,mem_closedBall_self ha,hguF.symm⟩
  · rw [hgpole]
    exact OnePoint.infty_notMem_image_coe
end CannonCarrierCharging

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_FaceHullCompact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding CannonTileTopology
open scoped OnePoint

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)]

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma faceHull_compact (z : ℂ → ℂ) (d : Faces F) : IsCompact (faceHull F z d) :=
  ((faceVertices F d).finite_toSet.image z).isCompact_convexHull ℝ

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.hull_regular {d : Faces F} (C : FacialCycle F d) (z : ℂ → ℂ)
    (hpos : 0<area (z C.a) (z C.b) (z C.c)) :
    closure (interior (faceHull F z d))=faceHull F z d := by
  rw [C.hull_eq,convexHull_interior hpos,convexHull_closure_inside hpos]

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma sphereTile_regular (z : ℂ → ℂ) (out d : Faces F)
    (hcycles : ∀ e : Faces F,∃ C : FacialCycle F e,0<area (z C.a) (z C.b) (z C.c)) :
    closure (interior (sphereTile F z out d))=sphereTile F z out d := by
  obtain ⟨C,hC⟩:=hcycles d
  have hc:=faceHull_compact z d
  have hr:=C.hull_regular z hC
  unfold sphereTile
  split_ifs with h
  · subst d
    rw [interior_compl,coe_closure_interior hc hr,closure_compl,coe_image_interior]
  · exact coe_regular hc hr

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma sphereTile_interiors_disjoint (z : ℂ → ℂ) (out : Faces F)
    (hcycles : ∀ e : Faces F,∃ C : FacialCycle F e,0<area (z C.a) (z C.b) (z C.c))
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out) :
    Pairwise fun d e=>Disjoint (interior (sphereTile F z out d)) (interior (sphereTile F z out e)) := by
  have ho (d : Faces F) (hd : d≠out) :
      Disjoint (interior (sphereTile F z out d)) (interior (sphereTile F z out out)) := by
    obtain ⟨C,hC⟩:=hcycles out
    have hs : faceHull F z d⊆faceHull F z out := by
      rw [←hfill]
      exact subset_iUnion (fun e : {e : Faces F // e≠out}=>faceHull F z e.val) ⟨d,hd⟩
    simp only [sphereTile,ite_eq_right hd,ite_true,coe_image_interior,interior_compl,
      coe_closure_interior (faceHull_compact z out) (C.hull_regular z hC)]
    apply Set.disjoint_left.mpr
    rintro p ⟨q,hq,rfl⟩ hpo
    exact hpo ⟨q,hs (interior_subset hq),rfl⟩
  intro d e hde
  by_cases hd : d=out
  · subst d
    exact (ho e hde.symm).symm
  by_cases he : e=out
  · subst e
    exact ho d hd
  simp only [sphereTile,ite_eq_right hd,ite_eq_right he,coe_image_interior]
  exact (hI d e hd he hde).image OnePoint.coe_injective.injOn (subset_univ _) (subset_univ _)

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma sphereTile_frontier_disks (z : ℂ → ℂ) (r : ℂ → ℝ)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1))
    (hcycles : ∀ e : Faces F,∃ C : FacialCycle F e,0<area (z C.a) (z C.b) (z C.c)) (out d : Faces F) :
    frontier (sphereTile F z out d)⊆⋃ v∈(faceVertices F d : Set ℂ),
      ((↑) : ℂ → OnePoint ℂ) '' closedBall (z v) (r v) := by
  have he : frontier (sphereTile F z out d)=((↑) : ℂ → OnePoint ℂ) '' frontier (faceHull F z d) := by
    obtain ⟨C,hC⟩:=hcycles d
    unfold sphereTile
    split_ifs with h
    · subst d
      rw [frontier_compl,coe_interior_frontier (faceHull_compact z out) (C.hull_regular z hC)]
    · exact coe_frontier (faceHull_compact z d)
  rw [he]
  rintro p ⟨q,hq,rfl⟩
  obtain ⟨C,hC⟩:=hcycles d
  obtain ⟨u,hu,v,hv,huv,hq⟩:=C.frontier_edges z hC hq
  rcases segment_two_closedBalls (C.developed_length hu hv huv z r hlen) hq with h|h
  · exact mem_iUnion₂.mpr ⟨u,hu,⟨q,h,rfl⟩⟩
  · exact mem_iUnion₂.mpr ⟨v,hv,⟨q,h,rfl⟩⟩
end CannonEmbeddedArc.Arc

namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding CannonTileTopology
open scoped OnePoint

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)]

omit [DecidableEq ι] [Fintype (Faces F)] in
lemma packing_center_tile_incidence
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (r : ℂ → ℝ) (hr : ∀ v,0 < r v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1))
    (hsep : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → r u+r v≤dist (z u) (z v))
    (hcycles : ∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c))
    (out : Faces F)
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out)
    {v : ℂ} (hv : Vertex F v) (d : Faces F)
    (hvd : (z v:OnePoint ℂ)∈sphereTile F z out d) : v∈faceVertices F d := by
  by_contra hn
  obtain ⟨e,heo,hve⟩:=vertex_inner_face (out:=out) hF Q hQ hK hv
  have hpe : (z v:OnePoint ℂ)∈sphereTile F z out e := by
    rw [sphereTile,ite_eq_right heo]
    exact ⟨z v,subset_convexHull ℝ _ ⟨v,hve,rfl⟩,rfl⟩
  have hde : d≠e:=fun h=>hn (h ▸ hve)
  have hf:=(regular_tiles_inter_frontier (sphereTile_regular z out d hcycles)
    (sphereTile_regular z out e hcycles)
    (sphereTile_interiors_disjoint z out hcycles hI hfill hde) hvd hpe).1
  obtain ⟨j,hj,q,hq,he⟩:=mem_iUnion₂.mp (sphereTile_frontier_disks z r hlen hcycles out d hf)
  have hqv : q=z v:=OnePoint.coe_injective he
  subst q
  have hne : v≠j:=fun h=>hn (h ▸ hj)
  have hs:=hsep v hv j ((mem_faceVertices F d j).mp hj).1 hne
  have hd:=mem_closedBall.mp hq
  linarith [hr v]
end CannonEmbeddedArc.Arc

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_PackingNormalizedTileBudget
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding CannonTileTopology
open scoped OnePoint BigOperators

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)]

theorem packing_normalized_tile_budget [DecidableEq ι] [Nonempty ι]
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (ρ : ℂ → ℝ) (hρ : ∀ v,0<ρ v)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=ρ (F i 0)+ρ (F i 1))
    (hsep : ∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → ρ u+ρ v≤dist (z u) (z v))
    (hcycles : ∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c))
    (out : Faces F)
    (hI : ∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e)))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out)
    (pole : ℂ) (hpv : Vertex F pole)
    (N : OnePoint ℂ ≃ₜ OnePoint ℂ) (hN : N∈CannonMobius.biholomorphic) (hpole : N (z pole)=∞)
    (D : ℕ) (hdeg : ∀ v : ℂ,Nat.card {i : ι | v∈range (F i)}≤D) :
    let T : Faces F → Set ℂ:=fun d=>((↑) : ℂ → OnePoint ℂ) ⁻¹' (N '' sphereTile F z out d)
    ∃ c : Faces F → ℂ,∃ r : Faces F → ℝ,∃ s : Faces F → ℂ,
      (∀ d,s d∈faceVertices F d) ∧ (∀ d,0 ≤ r d) ∧
      (∀ d,pole∉faceVertices F d → T d⊆closedBall (c d) (3*r d)) ∧
      (∀ p : ℂ,∀ R : ℝ,0≤R →
        (∑ d,if pole∉faceVertices F d ∧ (T d∩closedBall p R).Nonempty then (min (r d) R)^2 else 0)
          ≤(25*(D:ℝ)+1)*R^2) ∧
      (Finset.univ.filter (fun d=>¬pole∉faceVertices F d)).card≤D := by
  classical
  let ν:=GraphVertices F
  let _ : Fintype ν:=Fintype.ofFinite ν
  let V : Faces F → Finset ν:=fun d=>Finset.univ.filter (fun j=>j.val∈faceVertices F d)
  have hmem (d : Faces F) (j : ν) : j∈V d ↔ j.val∈faceVertices F d:=by simp [V]
  have hV (d : Faces F) : (V d).Nonempty := by
    obtain ⟨C,_⟩:=hcycles d
    have hC : C.a∈faceVertices F d:=by rw [C.vertices]; simp
    exact ⟨⟨C.a,((mem_faceVertices F d C.a).mp hC).1⟩,(hmem _ _).mpr hC⟩
  have hf (d : Faces F) : frontier (sphereTile F z out d)⊆
      ⋃ j∈V d,((↑) '' closedBall (z j.val) (ρ j.val) : Set (OnePoint ℂ)) := by
    intro x hx
    obtain ⟨j,hj,hxj⟩:=mem_iUnion₂.mp (sphereTile_frontier_disks z ρ hlen hcycles out d hx)
    exact mem_iUnion₂.mpr ⟨⟨j,((mem_faceVertices F d j).mp hj).1⟩,(hmem _ _).mpr hj,hxj⟩
  have hp (d : Faces F) (i : ν) (hi : i∈V d) (j : ν) (hj : j∈V d) (hij : i≠j) :
      dist (z i.val) (z j.val)=ρ i.val+ρ j.val := by
    obtain ⟨C,_⟩:=hcycles d
    obtain ⟨k,hk⟩:=C.pair_edge ((hmem _ _).mp hi) ((hmem _ _).mp hj) (Subtype.val_injective.ne hij)
    exact hk.developed_length z ρ (hlen k)
  have hpinc (d : Faces F) (hp : (z pole:OnePoint ℂ)∈sphereTile F z out d) : (⟨pole,hpv⟩ : ν)∈V d :=
    (hmem _ _).mpr (packing_center_tile_incidence hF Q hQ hK z ρ hρ hlen hsep hcycles out hI hfill hpv d hp)
  have hinc (j : ν) : (Finset.univ.filter (fun d : Faces F=>j∈V d)).card≤D := by
    simpa only [hmem] using face_incidence_card_le hF Q hQ hK D hdeg j.val
  obtain ⟨c,r,s,hs,hr,hcell,hbud,hbad⟩:=pole_chart_tile_budget V hV (⟨pole,hpv⟩ : ν)
    (sphereTile F z out) (sphereTile_closed z out)
    (sphereTile_interiors_disjoint z out hcycles hI hfill)
    (fun j=>z j.val) (fun j=>ρ j.val) (fun j=>hρ j.val)
    (fun i j hij=>hsep i.val i.property j.val j.property (Subtype.val_injective.ne hij))
    hf hp hpinc N hN hpole D hinc
  refine ⟨c,r,(fun d=>(s d).val),(fun d=>(hmem _ _).mp (hs d)),hr,?_,?_,?_⟩
  · simpa only [hmem] using hcell
  · simpa only [hmem] using hbud
  · simpa only [hmem] using hbad
end CannonEmbeddedArc.Arc

end
end

end OAI
end

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_SelectedFaceChargingCounts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonMobius.sphereBorelSpace _root_.OAI.CannonMobius.sphereMeasurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence

attribute [local instance] Classical.propDecidable
variable {X ι : Type*} [MetricSpace X] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {H : ι → Arc ℂ} [Fintype (Faces H)]

lemma selected_face_charging_counts
    (hH : Pairwise fun i j=>Compatible (H i) (H j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (H i) ⊆ ⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q}))
    (D : ℕ) (hdeg : ∀ v : ℂ,Nat.card {i : ι | v∈range (H i)} ≤ D)
    (e : ℂ → X) (sel : Faces H → ℂ) (hsel : ∀ d,sel d∈faceVertices H d)
    (T : Finset X) (mesh L : ℝ) (kr kc : ℕ)
    (hrow : ∀ x : X,(T.filter (fun y=>dist x y<(L+3)*mesh)).card ≤ kr)
    (hcol : ∀ x : X,Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<(L+3)*mesh} ≤ kc) :
    (∀ d : Faces H,(Finset.univ.filter (fun i : T=>dist i.val (e (sel d))<2*mesh+mesh+L*mesh)).card ≤ kr) ∧
    (∀ i : T,(Finset.univ.filter (fun d : Faces H=>dist i.val (e (sel d))<2*mesh+mesh+L*mesh)).card ≤ D*kc) := by
  classical
  have he : 2*mesh+mesh+L*mesh=(L+3)*mesh:=by ring
  constructor
  · intro d
    apply (Finset.card_le_card_of_injOn (fun i : T=>i.val) (t:=T.filter (fun y=>dist (e (sel d)) y<(L+3)*mesh))
      (by
        intro i hi
        exact Finset.mem_filter.mpr ⟨i.property,by simpa only [he,dist_comm] using (Finset.mem_filter.mp hi).2⟩)
      (fun i _ j _ hij=>Subtype.ext hij)).trans (hrow _)
  · intro i
    let S:=Finset.univ.filter (fun d : Faces H=>dist i.val (e (sel d))<2*mesh+mesh+L*mesh)
    have hImg : (S.image sel).card ≤ kc := by
      have hfin : {v : ℂ | Vertex H v ∧ dist (e v) i.val<(L+3)*mesh}.Finite:=
        (finite_vertex_set H).subset (fun _ h=>h.1)
      have hsub : (S.image sel : Set ℂ) ⊆ {v : ℂ | Vertex H v ∧ dist (e v) i.val<(L+3)*mesh} := by
        rintro v hv
        obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hv
        refine ⟨((mem_faceVertices H d (sel d)).mp (hsel d)).1,?_⟩
        simpa only [he,dist_comm] using (Finset.mem_filter.mp hd).2
      have hh:=Nat.card_mono hfin hsub
      have hh' : (S.image sel).card ≤ Nat.card {v : ℂ | Vertex H v ∧ dist (e v) i.val<(L+3)*mesh}:=by
        simpa [Nat.card_eq_fintype_card] using hh
      exact hh'.trans (hcol _)
    apply (Finset.card_le_mul_card_image S D (f:=sel) ?_).trans (Nat.mul_le_mul_left D hImg)
    intro v hv
    apply (Finset.card_le_card (show S.filter (fun d=>sel d=v) ⊆
      Finset.univ.filter (fun d : Faces H=>v∈faceVertices H d) from ?_)).trans
        (face_incidence_card_le hH Q hQ hK D hdeg v)
    intro d hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rw [←(Finset.mem_filter.mp hd).2]
    exact hsel d
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding CannonMobius
open CannonCarrierCharging CannonCells CannonUniformization
open scoped OnePoint BigOperators

attribute [local instance] Classical.propDecidable
variable {X ι : Type*} [MetricSpace X] [LocallyPathConnectedSpace X]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {H : ι → Arc ℂ} [Fintype (Faces H)]

theorem packing_radial_modulus_bound
    (hH : Pairwise fun i j=>Compatible (H i) (H j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (H i) ⊆ ⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q}))
    (D : ℕ) (hdeg : ∀ v : ℂ,Nat.card {i : ι | v∈range (H i)} ≤ D)
    (e : ℂ → X) (he : Continuous e)
    (z : ℂ → ℂ) (ρ : ℂ → ℝ) (hρ : ∀ v,0<ρ v)
    (hlen : ∀ i,dist (z (H i 0)) (z (H i 1))=ρ (H i 0)+ρ (H i 1))
    (hsep : ∀ u,Vertex H u → ∀ v,Vertex H v → u≠v → ρ u+ρ v ≤ dist (z u) (z v))
    (hcycles : ∀ d : Faces H,∃ C : FacialCycle H d,0<area (z C.a) (z C.b) (z C.c))
    (out : Faces H)
    (hI : ∀ d e : Faces H,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull H z d)) (interior (faceHull H z e)))
    (hfill : (⋃ d : {d : Faces H // d≠out},faceHull H z d.val)=faceHull H z out)
    (pole : ℂ) (hpv : Vertex H pole)
    (N : Sphere ≃ₜ Sphere) (hN : N∈biholomorphic) (hpole : N (z pole)=∞)
    (T : Finset X) (mesh L : ℝ) (hm : 0 < mesh)
    (hcover : ∀ x : X,∃ y∈T,dist x y ≤ mesh)
    (hdiam : ∀ d,∀ x∈compactifiedFace H e d,∀ y∈compactifiedFace H e d,dist x y ≤ L*mesh)
    (kr kc : ℕ)
    (hrow : ∀ x : X,(T.filter (fun y=>dist x y<(L+3)*mesh)).card ≤ kr)
    (hcol : ∀ x : X,Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<(L+3)*mesh} ≤ kc)
    (hc : ∀ S : Set Sphere,IsPreconnected S →
      IsPreconnected (⋃(d : {d : Faces H // (S∩sphereTile H z out d).Nonempty}),compactifiedFace H e d.val))
    (F : Set (Set X)) (hFn : ∀ E∈F,E.Nonempty)
    (p : ℂ) (a b R : ℝ) (hab : a ≤ b) (hb : b ≤ R) (hR : 0 ≤ R)
    (hcross : ∀ t∈Icc a b,
      ∃ x∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩N '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val,
      ∃ y∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩N '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val,
        ∀ γ : Path x y,range γ∈F) :
    (b-a)^2 ≤ 36*(26*(D:ℝ)+1)*R^2*(kr:ℝ)*(D*kc:ℕ)*
      modulus (fun i : T=>ball i.val (2*mesh)) F := by
  classical
  obtain ⟨c,rad,sel,hsel,hrad,hcell,hbudget,hbad⟩:=packing_normalized_tile_budget
    hH Q hQ hK z ρ hρ hlen hsep hcycles out hI hfill pole hpv N hN hpole D hdeg
  obtain ⟨hrow',hcol'⟩:=selected_face_charging_counts hH Q hQ hK D hdeg e sel hsel T mesh L kr kc hrow hcol
  have hconn : ∀ t∈Icc a b,IsPreconnected
      (⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩N '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val) := by
    intro t _
    exact spherical_circle_carriers_preconnected (compactifiedFace H e) (fun d=>N '' sphereTile H z out d)
      (normalized_carrier (compactifiedFace H e) (sphereTile H z out) hc N) p t
  exact clipped_spherical_carrier_modulus (compactifiedFace H e) (fun d=>N '' sphereTile H z out d)
    (fun d=>e (sel d)) (fun i : T=>i.val) mesh mesh (L*mesh) hm
    (fun d x hx=>hdiam d x hx (e (sel d)) (compactifiedFace_vertex e he (hsel d))) F hFn
    (by
      intro x
      obtain ⟨y,hy,hxy⟩:=hcover x
      refine ⟨⟨y,hy⟩,?_⟩
      change dist x y<2*mesh
      linarith)
    c rad (fun d=>pole∉faceVertices H d) hrad p hab hb hR D hcell (by
      refine le_trans (Finset.sum_le_sum (fun d _=>?_)) (hbudget p R hR)
      by_cases hd : pole∉faceVertices H d ∧ (((↑) : ℂ → Sphere) ⁻¹' (N '' sphereTile H z out d)∩closedBall p R).Nonempty <;> simp only [hd,ite_false,le_refl])
    (by
      convert hbad using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ext d
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]) hconn hcross kr (D*kc) hrow' hcol'
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding CannonMobius
open CannonCarrierCharging CannonCells CannonUniformization
open scoped OnePoint BigOperators

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [LocallyPathConnectedSpace X]

theorem packing_relative_modulus_cost_oai
    (LI σ : ℝ)
    (hinner : ∀ o u v : X,∀ s : ℝ,0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn (closedBall o (LI*s)) u v)
    (houter : ∀ o u v : X,∀ s : ℝ,0 < s → s ≤ dist o u → s ≤ dist o v →
      JoinedIn (ball o (σ*s))ᶜ u v) :
    ∃ V : ℝ → ℝ,(∀ ε,0<ε → 0<V ε) ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι],
    ∀ (H : ι → Arc ℂ) [Fintype (Faces H)],
    Pairwise (fun i j=>Compatible (H i) (H j)) →
    ∀ (Q : Finset (ℂ × ℂ)),(∀ i,range (H i) ⊆ ⋃p∈Q,segment ℝ p.1 p.2) →
    (∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q})) →
    ∀ (D : ℕ),(∀ v : ℂ,Nat.card {i : ι | v∈range (H i)} ≤ D) →
    ∀ (e : ℂ → X),Continuous e →
    ∀ (z : ℂ → ℂ) (ρ : ℂ → ℝ),(∀ v,0<ρ v) →
    (∀ i,dist (z (H i 0)) (z (H i 1))=ρ (H i 0)+ρ (H i 1)) →
    (∀ u,Vertex H u → ∀ v,Vertex H v → u≠v → ρ u+ρ v ≤ dist (z u) (z v)) →
    (∀ d : Faces H,∃ C : FacialCycle H d,0<area (z C.a) (z C.b) (z C.c)) →
    ∀ (out : Faces H),
    (∀ d e : Faces H,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull H z d)) (interior (faceHull H z e))) →
    ((⋃ d : {d : Faces H // d≠out},faceHull H z d.val)=faceHull H z out) →
    ∀ (N : Sphere ≃ₜ Sphere),N∈biholomorphic →
    ∀ (T : Finset X) (mesh L : ℝ),0 < mesh →
    (∀ x : X,∃ y∈T,dist x y ≤ mesh) →
    (∀ d,∀ x∈compactifiedFace H e d,∀ y∈compactifiedFace H e d,dist x y ≤ L*mesh) →
    ∀ (kr kc : ℕ),
    (∀ x : X,(T.filter (fun y=>dist x y<(L+3)*mesh)).card ≤ kr) →
    (∀ x : X,Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<(L+3)*mesh} ≤ kc) →
    (∀ S : Set Sphere,IsPreconnected S →
      IsPreconnected (⋃(d : {d : Faces H // (S∩sphereTile H z out d).Nonempty}),compactifiedFace H e d.val)) →
    ∀ (g : C(X,Sphere)),
    (∀ S : Set Sphere,g ⁻¹' S ⊆
      ⋃(d : {d : Faces H // (S∩N '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val) →
    ∀ (v : Fin 3 → ℂ) (s : ℝ),0 < s → (∀ i,Vertex H (v i)) →
      (∀ i j,i≠j → s ≤ dist (e (v i)) (e (v j))) →
      (∀ i,g (e (v i))=std i) → (∀ i,N (z (v i))=std i) →
    ∀ (o a₀ b₀ : X) (r R ε : ℝ),0 < r → 0<R → R ≤ s/2 →
      dist o a₀ ≤ r → R ≤ dist o b₀ →
      0<dist (g o) (g b₀) → 0<ε →
      ε*dist (g o) (g b₀)<dist (g o) (g a₀) →
    V ε ≤ 324*(26*(D:ℝ)+1)*(kr:ℝ)*(D*kc:ℕ)*
      modulus (fun i : T=>ball i.val (2*mesh)) (annulusFamily o (LI*r) (σ*R)) := by
  obtain ⟨C,hC,hwit⟩:=relative_radial_carrier_witness
  have hCp : 0<C:=by linarith
  let η : ℝ → ℝ:=fun ε=>min 1 (ε^2/(204*C^2))
  have hηp (ε : ℝ) (hε : 0<ε) : 0<η ε:=by dsimp [η]; positivity
  refine ⟨fun ε=>(η ε)^2,fun ε hε=>sq_pos_of_pos (hηp ε hε),?_⟩
  intro ι _ _ _ H _ hH Q hQ hK D hdeg e he z ρ hρ hlen hsep hcycles out hI hfill N hN
    T mesh L hm hcover hdiam kr kc hrow hcol hc g hpre v s hs hv hvs hmark hNm
    o a₀ b₀ r R ε hr hR hRs ha₀ hb₀ hdb hε hdiff
  have hη1 : η ε ≤ 1:=min_le_left _ _
  have hηε : 102*η ε*C^2<ε^2 := by
    have hh : η ε*(204*C^2) ≤ ε^2 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right 1 (ε^2/(204*C^2)))
    nlinarith [sq_pos_of_pos hε]
  obtain ⟨i,p,a,b,ha,hab,hb,hw,hcross⟩:=hwit LI σ hinner houter
    (compactifiedFace H e) (fun d=>N '' sphereTile H z out d) g hpre
    (fun i=>e (v i)) s hs hvs hmark o a₀ b₀ r R ε (η ε) hr hR hRs ha₀ hb₀ hdb hε
    (hηp ε hε).le hη1 hηε hdiff
  let NN : Sphere ≃ₜ Sphere:=N.trans (markedChart i)
  have hNN : NN∈biholomorphic := by
    change markedChart i*N∈biholomorphic
    exact biholomorphic.mul_mem (markedChart_biholomorphic i) hN
  have hNp : NN (z (v i))=∞ := by
    change markedChart i (N (z (v i)))=∞
    rw [hNm,markedChart_pole]
  let S:=C*dist (g o) (g b₀)
  have hS : 0<S:=mul_pos hCp hdb
  have hcross' : ∀ t∈Icc a b,
      ∃ x∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩NN '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val,
      ∃ y∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩NN '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val,
        ∀ γ : Path x y,range γ∈annulusFamily o (LI*r) (σ*R) := by
    have heq (d : Faces H) : NN '' sphereTile H z out d=markedChart i '' (N '' sphereTile H z out d) := by
      rw [image_image]
      rfl
    intro t ht
    obtain ⟨x,hx,y,hy,hpaths⟩:=hcross t ht
    have hmem (x : X)
        (hx : x∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩markedChart i '' (N '' sphereTile H z out d)).Nonempty}),compactifiedFace H e d.val) :
        x∈⋃(d : {d : Faces H // (((↑) '' sphere p t : Set Sphere)∩NN '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val := by
      obtain ⟨d,hd⟩:=mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨⟨d.val,?_⟩,hd⟩
      rw [heq]
      exact d.property
    exact ⟨x,hmem x hx,y,hmem y hy,hpaths⟩
  have hbound:=packing_radial_modulus_bound hH Q hQ hK D hdeg e he z ρ hρ hlen hsep hcycles
    out hI hfill (v i) (hv i) NN hNN hNp T mesh L hm hcover hdiam kr kc hrow hcol hc
    (annulusFamily o (LI*r) (σ*R))
    (fun E hE=>by
      obtain ⟨x,y,γ,hγ,hrest⟩:=hE
      subst E
      exact ⟨x,0,γ.source⟩)
    p a b (3*S) hab hb (by positivity) hcross'
  have hh : S^2*(η ε)^2 ≤ S^2*(324*(26*(D:ℝ)+1)*(kr:ℝ)*(D*kc:ℕ)*
      modulus (fun i : T=>ball i.val (2*mesh)) (annulusFamily o (LI*r) (σ*R))) := by
    calc S^2*(η ε)^2 = (b-a)^2 := by rw [hw]; dsimp [S]; ring
         _ ≤ _ := hbound
         _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hS)).mp (by simpa only [mul_comm] using hh)
end CannonEmbeddedArc.Arc

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CannonEmbeddedArc.Arc.packing_relative_modulus_cost_oai.{u_1} := @OAI.CannonEmbeddedArc.Arc.packing_relative_modulus_cost_oai.{u_1}
