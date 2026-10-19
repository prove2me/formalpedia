-- Prove2me | solution 2 for OAI.CriticalZ3.LatticeGraph.seedReaches_conn
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:51:05.701486+00:00
-- url     : https://prove2.me/submissions/31d81254-9799-440e-8d4d-7950651c0f7f

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/SeedQuality.lean:L83-L111
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.seedReaches_conn. The node keeps its source
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
import Theorems.Thm_OAI_CriticalZ3_Box_connected
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_lift_path

-- ---- from OAI.Probability.CriticalZ3.Basic ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uOmega uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory
open _root_.MeasureTheory ProbabilityTheory

namespace CriticalZ3

/-! Finite alterations, tail invariance, and the infinite seed limit. -/

open Filter
open scoped Topology

theorem cube_mono (c : Vertex) : Monotone (cube c) := by
  intro m n h x hx
  rw [mem_cube] at hx ⊢
  intro i
  have hn : (m : ℤ) ≤ n := by exact_mod_cast h
  obtain ⟨h₁,h₂⟩ := hx i
  constructor <;> omega

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

theorem conn_trans (m : Model) {ω : m.Config} {x y z : G.Node}
    (h : G.Conn m ω x y) (h' : G.Conn m ω y z) : G.Conn m ω x z := by
  exact (G.conn_iff m ω x z).mpr ⟨((G.conn_iff m ω x y).mp h).1,
    ((G.conn_iff m ω x y).mp h).2.trans ((G.conn_iff m ω y z).mp h').2⟩

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

-- ---- from OAI.Probability.CriticalZ3.SeedQuality ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Model

end Model

namespace Box

theorem contains_cube_iff {c x : Vertex} {n : ℕ} : (cube c n).Contains x ↔ x ∈ CriticalZ3.cube c n :=
  mem_cube.symm

end Box

namespace Model

end Model

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

theorem basicAdj_lift {B : Box} (hB : G.ContainsBox B) {ω : m.Config} {x y : G.Node}
    (hx : B.Contains x.1) (hy : B.Contains y.1) (hxy : m.BasicAdj ω x.1 y.1) : G.Adj m ω x y := by
  cases m
  · rcases hxy with ⟨i,hi,ho⟩ | ⟨i,hi,ho⟩
    · have he : Incidence (x.1,i) x.1 y.1 := Or.inl ⟨rfl,hi⟩
      exact ⟨(x.1,i),hB.2 (incidence_internal hx hy he),he,ho⟩
    · have he : Incidence (y.1,i) x.1 y.1 := Or.inr ⟨rfl,hi⟩
      exact ⟨(y.1,i),hB.2 (incidence_internal hx hy he),he,ho⟩
  · obtain ⟨e,he⟩ := neighbor_incidence hxy.1
    exact ⟨⟨e,hB.2 (incidence_internal hx hy he),he⟩,hxy.2⟩

/-- Exact finite-graph continuation of the quarter-face seed event. -/
theorem seedReaches_conn {c : Vertex} {a b : ℕ} (hab : a ≤ b)
    (hB : G.ContainsBox (Box.cube c b)) (T : Set Vertex) {ω : m.Config}
    {v : G.Node} (hv : v.1 = c)
    (hO : ω ∈ allValue ((Box.cube c a).bits m) true)
    (hE : ω ∈ m.SeedReaches c a b T) : G.Meets m ω v T := by
  obtain ⟨x,hxa,hxo,y,hy,hpath⟩ := hE
  have hxb := cube_mono c hab hxa
  have hyb : y ∈ cube c b := by
    induction hpath with
    | refl => exact hxb
    | tail _ hab _ => exact hab.2.1
  let x' : G.Node := ⟨x,G.containsBox_node hB (Box.contains_cube_iff.mpr hxb)⟩
  let y' : G.Node := ⟨y,G.containsBox_node hB (Box.contains_cube_iff.mpr hyb)⟩
  have hxy : G.Conn m ω x' y' := by
    refine (G.conn_iff m ω x' y').mpr ⟨?_,?_⟩
    · cases m <;> exact hxo
    · apply G.lift_path (r := Within (cube c b) (m.BasicAdj ω)) ?_ ?_ hpath
      · intro x y h
        exact G.containsBox_node hB (Box.contains_cube_iff.mpr h.2.1)
      · intro x y h
        exact G.basicAdj_lift m hB (Box.contains_cube_iff.mpr h.1)
          (Box.contains_cube_iff.mpr h.2.1) h.2.2
  have hA : G.ContainsBox (Box.cube c a) := hB.mono G (fun _ h =>
    Box.contains_cube_iff.mpr (cube_mono c hab (Box.contains_cube_iff.mp h)))
  refine ⟨y',hy,G.conn_trans m ?_ hxy⟩
  apply G.open_box_conn m hA hO
  · rw [hv]; exact Box.center_mem_cube _ _
  · exact Box.contains_cube_iff.mpr hxa

end LatticeGraph
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

end LatticeGraph
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.seedReaches_conn := @_root_.OAI.CriticalZ3.LatticeGraph.seedReaches_conn
