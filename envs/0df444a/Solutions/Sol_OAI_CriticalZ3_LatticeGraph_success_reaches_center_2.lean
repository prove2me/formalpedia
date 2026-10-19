-- Prove2me | solution 2 for OAI.CriticalZ3.LatticeGraph.success_reaches_center
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:29:50.968967+00:00
-- url     : https://prove2.me/submissions/85d0fc9d-d543-4ea0-8929-65e96d222456

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/SeedTrials.lean:L131-L158
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.success_reaches_center. The node keeps its source
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
import Theorems.Thm_OAI_CriticalZ3_Box_connected
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_lift_path

-- ---- from OAI.Probability.CriticalZ3.BoxGeometry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3

open Classical

namespace Box

theorem neighbor_coordinates {x y : Vertex} (h : NearestNeighbor x y) :
    ∃ i, |y i-x i| = 1 ∧ ∀ k, k ≠ i → y k = x k := by
  obtain ⟨i, h | h⟩ := h
  · subst y
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]
  · subst x
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]

theorem neighbor_distance {x y : Vertex} (h : NearestNeighbor x y) (i : Fin 3) :
    |y i-x i| ≤ 1 := by
  obtain ⟨k,hk,he⟩ := neighbor_coordinates h
  by_cases hik : i = k
  · simp [hik,hk]
  · simp [he i hik]

theorem neighbor_in_expand (B : Box) {x y : Vertex}
    (hx : B.Contains x) (hxy : NearestNeighbor x y) : (B.expand 1).Contains y := by
  intro i
  have hi := hx i
  have hd := neighbor_distance hxy i
  rw [abs_le] at hd
  change B.lower i-1 ≤ y i ∧ y i ≤ B.upper i+1
  omega

theorem seed_contains_entry (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) {z : Vertex} (hz : C.Contains z) :
    (cube (C.seedCenter m z) m).Contains z := by
  rw [contains_cube]
  intro i
  have hi := hz i
  have hwi := hw i
  dsimp [seedCenter]
  rw [abs_le]
  omega

end Box
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
theorem conn_iff (m : Model) (ω : m.Config) (x y : G.Node) :
    G.Conn m ω x y ↔ G.Open m ω x ∧ Relation.ReflTransGen (G.Adj m ω) x y := by
  cases m
  · exact ⟨fun h => ⟨trivial,h⟩,fun h => h.2⟩
  · rfl

theorem adj_open (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Open m ω x ∧ G.Open m ω y := by
  cases m
  · exact ⟨trivial,trivial⟩
  · exact h.2

theorem conn_open (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Conn m ω x y) :
    G.Open m ω x ∧ G.Open m ω y := by
  obtain ⟨hx,h⟩ := (G.conn_iff m ω x y).mp h
  refine ⟨hx,?_⟩
  induction h with
  | refl => exact hx
  | tail _ hab _ => exact (G.adj_open m hab).2

theorem conn_trans (m : Model) {ω : m.Config} {x y z : G.Node}
    (h : G.Conn m ω x y) (h' : G.Conn m ω y z) : G.Conn m ω x z := by
  exact (G.conn_iff m ω x z).mpr ⟨((G.conn_iff m ω x y).mp h).1,
    ((G.conn_iff m ω x y).mp h).2.trans ((G.conn_iff m ω y z).mp h').2⟩

theorem conn_adj (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Conn m ω x y := (G.conn_iff m ω x y).mpr ⟨(G.adj_open m h).1,.single h⟩

theorem incidence_internal {B : Box} {x y : Vertex} {e : Bond}
    (hx : B.Contains x) (hy : B.Contains y) (he : Incidence e x y) : e ∈ B.bonds := by
  rw [Box.mem_bonds]
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨hx,hy⟩
  · exact ⟨hy,hx⟩

theorem open_box_adj (m : Model) {B : Box} (hB : G.ContainsBox B)
    {ω : m.Config} (ho : ∀ e ∈ B.bits m, ω e = true) {x y : G.Node}
    (hx : B.Contains x.1) (hy : B.Contains y.1) (hxy : NearestNeighbor x.1 y.1) :
    G.Adj m ω x y := by
  obtain ⟨e,he⟩ := neighbor_incidence hxy
  have heb := incidence_internal hx hy he
  cases m
  · exact ⟨e,hB.2 heb,he,ho e heb⟩
  · exact ⟨⟨e,hB.2 heb,he⟩,ho x.1 ((B.mem_vertices x.1).mpr hx),
      ho y.1 ((B.mem_vertices y.1).mpr hy)⟩

theorem open_box_conn (m : Model) {B : Box} (hB : G.ContainsBox B)
    {ω : m.Config} (ho : ∀ e ∈ B.bits m, ω e = true) {x y : G.Node}
    (hx : B.Contains x.1) (hy : B.Contains y.1) : G.Conn m ω x y := by
  apply (G.conn_iff m ω x y).mpr
  constructor
  · cases m
    · trivial
    · exact ho x.1 ((B.mem_vertices x.1).mpr hx)
  · apply G.lift_path (r := B.Within)
      (fun _ _ h => G.containsBox_node hB h.2.2)
      (fun x y h => G.open_box_adj m hB ho h.2.1 h.2.2 h.1)
    exact B.connected hx hy

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.EntryLayers ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

theorem neighborBond_incidence {x y : Vertex} (h : NearestNeighbor x y) :
    Incidence (neighborBond x y) x y := by
  simp only [neighborBond,dite_eq_left h]
  exact (LatticeGraph.neighbor_incidence h).choose_spec

namespace Box

theorem entry_spec {C : Box} {y : Vertex} (h : C.Exterior y) :
    C.Contains (C.entry y) ∧ NearestNeighbor y (C.entry y) := by
  simp only [entry,dite_eq_left h]
  exact h.2.choose_spec

theorem exterior_expand {C : Box} {y : Vertex} (h : C.Exterior y) :
    (C.expand 1).Contains y := by
  obtain ⟨z,hz,hzy⟩ := h.2
  apply C.neighbor_in_expand hz
  obtain ⟨i,hi | hi⟩ := hzy
  · exact ⟨i,Or.inr hi⟩
  · exact ⟨i,Or.inl hi⟩

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

theorem outsideReach_conn (m : Model) {C : Box} {ω : m.Config} {o y : G.Node}
    (h : G.OutsideReach m C ω o y) : G.Conn m ω o y :=
  (G.conn_iff m ω o y).mpr ⟨h.2.1,Relation.ReflTransGen.mono (fun _ _ (hh : G.OutsideAdj m C ω _ _) => hh.2.2) o y h.2.2⟩

end LatticeGraph
end CriticalZ3

namespace CriticalZ3.LatticeGraph
open Classical
variable (G : LatticeGraph)

end CriticalZ3.LatticeGraph

end OAI

-- ---- from OAI.Probability.CriticalZ3.SeedTrials ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical
namespace Box

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

/-- A successful exterior trial supplies a path for both bond and site percolation. -/
theorem success_reaches_center (m : Model) (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    {ω : m.Config} {o y : G.Node} (hy : y.1 ∈ G.entrants m C ω o)
    (hs : ∀ e ∈ C.successBits r m y.1, ω e = true) :
    ∃ v : G.Node, v.1 = C.relayCenter r y.1 ∧ G.Conn m ω o v := by
  obtain ⟨hey,hreach⟩ := (G.mem_entrants m C ω o y).mp hy
  have hCg : G.ContainsBox C := hC.mono G (fun _ => C.contains_expand 1)
  have hUg : G.ContainsBox (C.seedBox r y.1) := hCg.mono G (C.seedBox_contained r hw y.1)
  have hz := (Box.entry_spec hey).1
  let z : G.Node := ⟨C.entry y.1,G.containsBox_node hCg hz⟩
  let v : G.Node := ⟨C.relayCenter r y.1,
    G.containsBox_node hUg (Box.center_mem_cube _ _)⟩
  have heo : ∀ e ∈ (C.seedBox r y.1).bits m, ω e = true := by
    intro e he
    cases m
    · exact hs e (Finset.mem_insert_of_mem he)
    · exact hs e he
  have hyz : G.Adj m ω y z := by
    have hi := neighborBond_incidence (Box.entry_spec hey).2
    have heb := incidence_internal (Box.exterior_expand hey) (C.contains_expand 1 hz) hi
    cases m
    · exact ⟨C.entryBit .bond y.1,hC.2 heb,hi,hs _ (Finset.mem_insert_self _ _)⟩
    · exact ⟨⟨neighborBond y.1 z.1,hC.2 heb,hi⟩,(G.conn_open .site (G.outsideReach_conn .site hreach)).2,
        heo _ ((Box.mem_vertices _ _).mpr (C.seed_contains_entry r hw hz))⟩
  refine ⟨v,rfl,G.conn_trans m (G.outsideReach_conn m hreach) ?_⟩
  exact G.conn_trans m (G.conn_adj m hyz) (G.open_box_conn m hUg heo
    (C.seed_contains_entry r hw hz) (Box.center_mem_cube _ _))

end LatticeGraph
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.success_reaches_center := @_root_.OAI.CriticalZ3.LatticeGraph.success_reaches_center
