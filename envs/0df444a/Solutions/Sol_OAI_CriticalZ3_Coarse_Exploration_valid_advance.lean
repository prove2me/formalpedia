-- Prove2me | solution 1 for OAI.CriticalZ3.Coarse.Exploration.valid_advance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:47:49.464591+00:00
-- url     : https://prove2.me/submissions/07cad607-7dc5-402d-9b1c-8d11c7499e4a

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Exploration.lean:L202-L283
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Coarse.Exploration.valid_advance. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals
import Definitions.Def_OAI_Probability_CriticalZ3_Exploration
import Theorems.Thm_OAI_CriticalZ3_Coarse_block_disjoint

-- ---- from OAI.Probability.CriticalZ3.ProductCylinder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! Exact reduction of finite cylinder observables under the infinite Bernoulli law. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace ProductCylinder
universe u
variable {E F : Type u}

theorem map_restrict (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) :
    (law p).map J.restrict = finiteLaw J p := Measure.infinitePi_map_restrict _

theorem cylinder_probability (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (J → Bool)) :
    law p (J.restrict ⁻¹' A) = finiteLaw J p A := by
  rw [←map_restrict,Measure.map_apply (Finset.measurable_restrict _) (Set.toFinite A).measurableSet]

theorem probability_determined (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (E → Bool)) (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    law p A = finiteLaw J p {ξ | extend J ξ ∈ A} := by
  rw [←cylinder_probability]
  congr 1
  ext ω
  exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
universe u
variable {E : Type u}

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

end ProductCylinder

end OAI

-- ---- from OAI.Probability.CriticalZ3.LatticeGraph ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open Classical MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory

namespace LatticeGraph
variable (G : LatticeGraph)

theorem bondAdj_determined (ω ω' : BondConfig)
    (h : ∀ e ∈ G.edges, ω' e = ω e) (x y : G.Node) :
    G.BondAdj ω' x y ↔ G.BondAdj ω x y := by
  constructor <;> rintro ⟨e,he,hxy,ho⟩
  · exact ⟨e,he,hxy,(h e he) ▸ ho⟩
  · exact ⟨e,he,hxy,(h e he).symm ▸ ho⟩

theorem bondConn_determined (ω ω' : BondConfig)
    (h : ∀ e ∈ G.edges, ω' e = ω e) (x y : G.Node) :
    G.BondConn ω' x y ↔ G.BondConn ω x y := by
  have he : G.BondAdj ω' = G.BondAdj ω := by
    funext a b; exact propext (G.bondAdj_determined ω ω' h a b)
  simp only [BondConn,he]

theorem siteConn_determined (ω ω' : SiteConfig)
    (h : ∀ x ∈ G.vertices, ω' x = ω x) (x y : G.Node) :
    G.SiteConn ω' x y ↔ G.SiteConn ω x y := by
  have he : (fun z : G.Node => ω' z.1) = fun z => ω z.1 := by
    funext z; exact h z.1 z.2
  simp only [SiteConn,he]

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.LatticePaths ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

namespace Model
end Model

namespace Box
end Box

namespace LatticeGraph
variable (G : LatticeGraph)
theorem conn_determined (m : Model) (ω ω' : m.Config)
    (h : ∀ e ∈ G.bits m, ω' e = ω e) (x y : G.Node) :
    G.Conn m ω' x y ↔ G.Conn m ω x y := by
  cases m
  · exact G.bondConn_determined ω ω' h x y
  · exact G.siteConn_determined ω ω' h x y

theorem meets_determined (m : Model) (o : G.Node) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) (G.bits m) (fun ω => G.Meets m ω o T) := by
  intro ω ω' h
  apply propext
  simp only [Meets,G.conn_determined m ω ω' h]

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ShellProbability ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3.LatticeGraph
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

namespace FiniteAssociation
open Classical
variable {E : Type}

end FiniteAssociation

namespace ProductCylinder
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

theorem probability_congr_parameters (J : Finset E)
    (p q : E → Set.Icc (0 : ℝ) 1) (hpq : ∀ e ∈ J, p e = q e)
    (A : Set (E → Bool)) (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A)) :
    (law p).real A = (law q).real A := by
  simp only [Measure.real_def,probability_determined J _ A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))]
  congr 2
  unfold finiteLaw
  congr 1
  funext e
  rw [hpq e e.2]

end ProductCylinder

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

end InfiniteConditioning

namespace CriticalZ3.LatticeGraph
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

end OAI

-- ---- from OAI.Probability.CriticalZ3.Coarse ----
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace Coarse
theorem interface_comm (r : ℕ) (v w : Point) : interface r v w = interface r w v := by
  ext e
  simp only [mem_interface,or_comm]

end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace LatticeGraph

end LatticeGraph

namespace Coarse
theorem block_subset_exposed_insert (m : Model) (r : ℕ) {D : Finset Point}
    {v a : Point} (ha : a ∈ D) : block m r v a ⊆ exposed m r (insert v D) := by
  intro e he
  rw [block,Finset.mem_union] at he
  rcases he with he|he
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨v,Finset.mem_insert_self _ _,he⟩))
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨(v,a),Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _,Finset.mem_insert_of_mem ha⟩,he⟩)

theorem exposed_mono (m : Model) (r : ℕ) {D D' : Finset Point} (h : D ⊆ D') :
    exposed m r D ⊆ exposed m r D' := by
  intro e he
  simp only [exposed,Finset.mem_union,Finset.mem_biUnion,Finset.mem_product] at he ⊢
  rcases he with (he|⟨v,hv,he⟩)|⟨⟨v,w⟩,⟨hv,hw⟩,he⟩
  · exact Or.inl (Or.inl he)
  · exact Or.inl (Or.inr ⟨v,h hv,he⟩)
  · exact Or.inr ⟨(v,w),⟨h hv,h hw⟩,he⟩

theorem extendGraph_bits (m : Model) (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) :
    (extendGraph r G v x hv).bits m = G.bits m ∪ block m r x v := by
  cases m
  · dsimp [LatticeGraph.bits,extendGraph,block,Box.bits,linkBits]
    rw [interface_comm r x v,Finset.union_assoc]
  · simp only [LatticeGraph.bits,extendGraph,block,Box.bits,linkBits,Finset.union_empty]

end Coarse
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Exploration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

namespace Packet
variable {r : ℕ}
theorem event_determined (t : Packet r) (m : Model) :
    ProductCylinder.DeterminedBy (F := Prop) (t.graph.bits m) (fun ω => ω ∈ t.event m) :=
  t.graph.meets_determined m _ _

theorem child_bits (t : Packet r) (x : Point) (m : Model) :
    (t.child x).graph.bits m = t.graph.bits m ∪ block m r x t.vertex :=
  extendGraph_bits m r t.graph t.vertex x t.contains
end Packet

namespace Exploration
variable {m : Model} {r : ℕ}
end Exploration
end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

theorem outward_injective : Function.Injective outward := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [outward,PlanarBoundary.outward]

namespace Exploration
variable {m : Model} {r : ℕ}

theorem queue_visited (s : Exploration m r) {t : Packet r} (ht : t ∈ s.queue) :
    t.vertex ∈ s.visited :=
  Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩))

theorem processed_visited (s : Exploration m r) : s.processed ⊆ s.visited := Finset.subset_union_left

theorem candidates_distinct (s : Exploration m r) (t : Packet r) :
    ((s.candidates t).map Packet.vertex).Nodup := by
  have hh : ((List.ofFn (fun d : Direction => t.child (t.vertex+outward d))).map Packet.vertex).Nodup := by
    rw [List.map_ofFn]
    apply List.nodup_ofFn.mpr
    intro a b hab
    exact outward_injective (add_left_cancel hab)
  exact (List.filter_sublist.map Packet.vertex).nodup hh

theorem advance_empty (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) (h : s.queue = []) : s.advance q δ ω = s := by
  cases s with
  | mk history processed queue good bad =>
    cases history
    simp_all only [advance,after,reveal,History.observe,Finset.union_empty,Exploration.mk.injEq,History.mk.injEq,true_and,and_true]
    funext e
    exact ite_eq_right (Finset.notMem_empty e)

theorem current_support {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    t.graph.bits m ⊆ s.history.known ∪ s.reveal := by
  intro e he
  have hh := hs.support t (by simp [hq]) he
  rcases Finset.mem_union.mp hh with hh|hh
  · exact Finset.mem_union_left _ hh
  · by_cases hk : e ∈ s.history.known
    · exact Finset.mem_union_left _ hk
    · exact Finset.mem_union_right _ (by simpa only [reveal,hq,Finset.mem_sdiff] using ⟨hh,hk⟩)

theorem later_disjoint {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {u : Packet r} (hu : u ∈ ts) : Disjoint s.reveal (u.graph.bits m) := by
  have htq : t ∈ s.queue := by simp [hq]
  have huq : u ∈ s.queue := by simp [hq,hu]
  have htu : t.vertex ≠ u.vertex := by
    have hn := hs.distinct
    rw [hq,List.map_cons,List.nodup_cons] at hn
    intro he
    exact hn.1 (he ▸ List.mem_map.mpr ⟨u,hu,rfl⟩)
  have hd := block_disjoint m r (hs.unprocessed t htq) (hs.unprocessed u huq)
    (hs.parents t htq) (hs.parents u huq) htu
  apply Finset.disjoint_left.mpr
  intro e he hu
  have hr : e ∈ block m r t.vertex t.parent ∧ e ∉ s.history.known := by
    simpa only [reveal,hq,Finset.mem_sdiff] using he
  rcases Finset.mem_union.mp (hs.support u huq hu) with hu|hu
  · exact hr.2 hu
  · exact Finset.disjoint_left.mp hd hr.1 hu

theorem later_probability {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {u : Packet r} (hu : u ∈ ts) (ω : m.Config) :
    (ProductCylinder.law ((s.after ω).parameter q)).real (u.event m) =
      (ProductCylinder.law (s.history.parameter q)).real (u.event m) := by
  apply ProductCylinder.probability_congr_parameters (u.graph.bits m) _ _ _ _ (u.event_determined m)
  intro e he
  rw [after,History.parameter_observe]
  exact ite_eq_right (fun hh => Finset.disjoint_left.mp (later_disjoint hs hq hu) hh he)

theorem valid_advance {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (ω : m.Config) : (s.advance q δ ω).Valid q δ := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    have htq : t ∈ s.queue := by simp [hq]
    have hnot : t.vertex ∉ ts.map Packet.vertex := by
      have hh := hs.distinct
      rw [hq,List.map_cons,List.nodup_cons] at hh
      exact hh.1
    have htail : (ts.map Packet.vertex).Nodup := by
      have hh := hs.distinct
      rw [hq,List.map_cons,List.nodup_cons] at hh
      exact hh.2
    have hp : (s.advance q δ ω).processed = insert t.vertex s.processed := by simp [advance,hq]
    have hn : (s.advance q δ ω).queue = ts ++ if s.Accept q δ t ω then s.candidates t else [] := by
      simp [advance,hq]
    have hvu {u : Packet r} (hu : u ∈ s.candidates t) :
        u.vertex ≠ t.vertex ∧ u.vertex ∉ s.processed := by
      have hh := (mem_candidates s t u).mp hu |>.2
      exact ⟨fun he => hh (he ▸ s.queue_visited htq),fun he => hh (s.processed_visited he)⟩
    have hold {u : Packet r} (hu : u ∈ ts) : u.vertex ≠ t.vertex ∧ u.vertex ∉ s.processed := by
      exact ⟨fun he => hnot (he ▸ List.mem_map.mpr ⟨u,hu,rfl⟩),
        hs.unprocessed u (by simp [hq,hu])⟩
    have hmembers {u : Packet r} (hu : u ∈ (s.advance q δ ω).queue) :
        u ∈ ts ∨ (s.Accept q δ t ω ∧ u ∈ s.candidates t) := by
      rw [hn,List.mem_append] at hu
      rcases hu with hu|hu
      · exact Or.inl hu
      · split_ifs at hu with ha
        · exact Or.inr ⟨ha,hu⟩
        · exact False.elim (List.not_mem_nil hu)
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · rw [hp]; exact Finset.mem_insert_of_mem hs.root_processed
    · rw [hn,List.map_append]
      split_ifs with ha
      · apply htail.append (s.candidates_distinct t)
        apply List.disjoint_left.mpr
        intro v hv hu
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hu
        have hh := (mem_candidates s t z).mp hz |>.2
        exact hh (Finset.mem_union_right _ (List.mem_toFinset.mpr (by rw [hq,List.map_cons]; exact List.mem_cons_of_mem _ hv)))
      · simpa only [List.map_nil,List.append_nil] using htail
    · intro u hu
      rw [hp,Finset.mem_insert]
      rcases hmembers hu with hu|⟨_,hu⟩
      · exact not_or.mpr (hold hu)
      · exact not_or.mpr (hvu hu)
    · intro u hu
      rw [hp]
      rcases hmembers hu with hu|⟨_,hu⟩
      · exact Finset.mem_insert_of_mem (hs.parents u (by simp [hq,hu]))
      · obtain ⟨⟨d,rfl⟩,_⟩ := (mem_candidates s t u).mp hu
        exact Finset.mem_insert_self _ _
    · rw [hp]
      dsimp only [advance,after,History.observe]
      simp only [Finset.subset_iff,Finset.mem_union]
      intro e he
      rcases he with hk|hr
      · exact exposed_mono m r (Finset.subset_insert _ _) (hs.exposed hk)
      · apply block_subset_exposed_insert m r (hs.parents t htq)
        exact (Finset.mem_sdiff.mp (by simpa only [reveal,hq] using hr)).1
    · intro u hu
      dsimp only [advance,after,History.observe]
      simp only [Finset.subset_iff,Finset.mem_union]
      rcases hmembers hu with hu|⟨_,hu⟩
      · intro e he
        rcases Finset.mem_union.mp (hs.support u (by simp [hq,hu]) he) with he|he
        · exact Or.inl (Or.inl he)
        · exact Or.inr he
      · obtain ⟨⟨d,rfl⟩,_⟩ := (mem_candidates s t u).mp hu
        intro e he
        rw [Packet.child_bits,Finset.mem_union] at he
        rcases he with he|he
        · exact Or.inl (Finset.mem_union.mp (current_support hs hq he))
        · exact Or.inr he
    · intro u hu
      rcases hmembers hu with hu|⟨ha,hu⟩
      · change 1-δ < (ProductCylinder.law ((s.after ω).parameter q)).real (u.event m)
        rw [later_probability hs hq hu ω]
        exact hs.promise u (by simp [hq,hu])
      · exact ha.2 u hu
end Exploration
end Coarse
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse OAI.CriticalZ3.Coarse.Exploration
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.Coarse.Exploration.valid_advance := @_root_.OAI.CriticalZ3.Coarse.Exploration.valid_advance
