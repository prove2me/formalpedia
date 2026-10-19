-- Prove2me | solution 1 for OAI.CriticalZ3.Coarse.initial_valid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:58:40.577173+00:00
-- url     : https://prove2.me/submissions/d4012e24-240b-4789-96c0-559cb4b65096

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ExplorationConnectivity.lean:L164-L188
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Coarse.initial_valid. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationInvariant
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationConnectivity
import Theorems.Thm_OAI_CriticalZ3_Box_connected
import Theorems.Thm_OAI_CriticalZ3_Coarse_cube_unique
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_lift_path
import Theorems.Thm_OAI_CriticalZ3_quarterFace_subset_boundary
import Theorems.Thm_OAI_InfiniteConditioning_map_replace

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

theorem measurableSet_determined (J : Finset E) (A : Set (E → Bool))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) : MeasurableSet A := by
  have he : A = J.restrict ⁻¹' {ξ | extend J ξ ∈ A} := by
    ext ω
    exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])
  rw [he]
  exact (Finset.measurable_restrict _) (Set.toFinite _).measurableSet

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

-- ---- from OAI.Probability.CriticalZ3.Symmetry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

namespace CriticalZ3
open Classical

theorem mem_internalBonds {D : Set Vertex} {hD : D.Finite} {e : Bond} :
    e ∈ internalBonds D hD ↔ e.1 ∈ D ∧ step e.1 e.2 ∈ D := by
  simp [internalBonds]

theorem bondWithin_congr {D : Set Vertex} {hD : D.Finite} {ω ω' : BondConfig}
    (hω : ∀ e ∈ internalBonds D hD, ω' e = ω e) :
    Within D (BondOpen ω') = Within D (BondOpen ω) := by
  funext x y
  apply propext
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · simp only [Within,hx,hy,true_and,BondOpen]
    apply or_congr
    · apply exists_congr
      intro i
      by_cases he : y = step x i
      · rw [hω (x,i) (mem_internalBonds.mpr ⟨hx,he ▸ hy⟩)]
      · simp [he]
    · apply exists_congr
      intro i
      by_cases he : x = step y i
      · rw [hω (y,i) (mem_internalBonds.mpr ⟨hy,he ▸ hx⟩)]
      · simp [he]
  all_goals simp [Within,hx,hy]

theorem siteWithin_congr {D : Set Vertex} {hD : D.Finite} {ω ω' : SiteConfig}
    (hω : ∀ x ∈ hD.toFinset, ω' x = ω x) :
    Within D (SiteOpen ω') = Within D (SiteOpen ω) := by
  funext x y
  apply propext
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · simp only [Within,hx,hy,true_and,SiteOpen,hω x (hD.mem_toFinset.mpr hx),
      hω y (hD.mem_toFinset.mpr hy)]
  all_goals simp [Within,hx,hy]

theorem bondSeedReaches_determined (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    ∀ ω ω', (∀ e ∈ internalBonds (cube c n) (cube_finite c n), ω' e = ω e) →
      (ω' ∈ bondSeedReaches c m n T ↔ ω ∈ bondSeedReaches c m n T) := by
  intro ω ω' hω
  simp only [bondSeedReaches,Set.mem_ofPred_eq,bondWithin_congr hω]

theorem siteSeedReaches_determined (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    ∀ ω ω', (∀ e ∈ (cube_finite c n).toFinset, ω' e = ω e) →
      (ω' ∈ siteSeedReaches c m n T ↔ ω ∈ siteSeedReaches c m n T) := by
  intro ω ω' hω
  simp only [siteSeedReaches,Set.mem_ofPred_eq,siteWithin_congr hω]
  apply exists_congr
  intro x
  by_cases hx : x ∈ cube c m
  · simp only [hx,true_and,hω x ((cube_finite c n).mem_toFinset.mpr (cube_mono c hmn hx))]
  · simp only [hx,false_and]

end CriticalZ3

namespace CriticalZ3
open Classical

namespace SignedSymmetry

end SignedSymmetry
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

theorem adj_symm (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Adj m ω y x := by
  cases m
  · obtain ⟨e,he,hi,ho⟩ := h; exact ⟨e,he,incidence_symm hi,ho⟩
  · exact ⟨G.graph.adj_symm h.1,h.2.2,h.2.1⟩

theorem conn_open (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Conn m ω x y) :
    G.Open m ω x ∧ G.Open m ω y := by
  obtain ⟨hx,h⟩ := (G.conn_iff m ω x y).mp h
  refine ⟨hx,?_⟩
  induction h with
  | refl => exact hx
  | tail _ hab _ => exact (G.adj_open m hab).2

theorem conn_symm (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Conn m ω x y) :
    G.Conn m ω y x := by
  refine (G.conn_iff m ω y x).mpr ⟨(G.conn_open m h).2,?_⟩
  have hh := (G.conn_iff m ω x y).mp h |>.2
  clear h
  induction hh with
  | refl => exact .refl
  | tail _ hab ih => exact ih.head (G.adj_symm m hab)

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

-- ---- from OAI.Probability.CriticalZ3.Conditioning ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

universe uF

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

/-! The exact revealed-history law used by the adaptive queue.  In particular,
classifications depending only on revealed values do not change fresh bits. -/
namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

omit [Countable E] in
theorem measurable_replace (J : Finset E) (ξ : E → Bool) : Measurable (replace J ξ) := by
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ J
  · simp only [replace, ite_eq_left he]; exact measurable_const
  · simp only [replace, ite_eq_right he]; exact measurable_pi_apply e

theorem measurableSet_pattern (J : Finset E) (ξ : E → Bool) : MeasurableSet (pattern J ξ) := by
  simp only [pattern, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_pi_apply e) measurable_const))

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E I : Type}

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

/-- A reveal has no effect on any observable determined by disjoint bits. -/
theorem fixed_determined_probability (p : E → Set.Icc (0 : ℝ) 1)
    (J K : Finset E) (hJK : Disjoint J K) (ξ : E → Bool) (A : Set (E → Bool))
    (hA : ProductCylinder.DeterminedBy (F := Prop) K (fun ω => ω ∈ A)) :
    (ProductCylinder.law (fixedParameter p J ξ)).real A = (ProductCylinder.law p).real A := by
  have hAm := ProductCylinder.measurableSet_determined K A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))
  rw [←map_replace,Measure.real_def,Measure.map_apply (measurable_replace _ _) hAm]
  have heq : replace J ξ ⁻¹' A = A := by
    ext ω
    apply eq_iff_iff.mp (hA ω (replace J ξ ω) ?_)
    intro e he
    apply ite_eq_right
    exact fun heJ => Finset.disjoint_left.mp hJK heJ he
  rw [heq]
  rfl

variable [Countable E]

theorem ae_fixed_pattern (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    ∀ᵐ ω ∂ProductCylinder.law (fixedParameter p J ξ), ω ∈ pattern J ξ := by
  rw [←map_replace]
  apply (ae_map_iff (measurable_replace J ξ).aemeasurable
    (measurableSet_pattern J ξ)).mpr
  exact Filter.Eventually.of_forall (fun ω e he => ite_eq_left he)

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

end InfiniteConditioning

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

theorem cube_bonds_eq (c : Vertex) (r : ℕ) :
    (cube c r).bonds = internalBonds (CriticalZ3.cube c r) (cube_finite c r) := by
  ext e
  simp only [mem_bonds,mem_internalBonds,contains_cube_iff]

theorem cube_sites_eq (c : Vertex) (r : ℕ) :
    (cube c r).vertices = (cube_finite c r).toFinset := by
  ext e
  simp only [mem_vertices,Set.Finite.mem_toFinset,contains_cube_iff]
end Box

namespace Model

theorem seedReaches_determined (m : Model) (c : Vertex) (a b : ℕ) (hab : a ≤ b) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) ((Box.cube c b).bits m)
      (fun ω => ω ∈ m.SeedReaches c a b T) := by
  intro ω ω' h
  apply propext
  cases m
  · rw [seedReaches_bond]
    apply bondSeedReaches_determined c a b T ω ω'
    simpa only [Box.bits,Box.cube_bonds_eq] using h
  · apply siteSeedReaches_determined c a b hab T ω ω'
    simpa only [Box.bits,Box.cube_sites_eq] using h
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

-- ---- from OAI.Probability.CriticalZ3.Extension ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uOmega

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace MeasureTheory
open scoped _root_.MeasureTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] {μ : _root_.MeasureTheory.Measure Ω} [_root_.MeasureTheory.IsFiniteMeasure μ]
theorem finite_measureReal_mono_ae {A B : Set Ω} (h : A ≤ᵐ[μ] B) :
    μ.real A ≤ μ.real B :=
  ENNReal.toReal_le_toReal (_root_.MeasureTheory.measure_ne_top μ A) (_root_.MeasureTheory.measure_ne_top μ B) |>.mpr (_root_.MeasureTheory.measure_mono_ae h)
end MeasureTheory

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

namespace CriticalZ3
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Coarse ----
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace Coarse
theorem Q_disjoint (r : ℕ) {v w : Point} (h : v ≠ w) : Disjoint (Q r v).vertices (Q r w).vertices := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h (cube_unique r ((Box.mem_vertices _ _).mp hx) ((Box.mem_vertices _ _).mp hy))

theorem interface_comm (r : ℕ) (v w : Point) : interface r v w = interface r w v := by
  ext e
  simp only [mem_interface,or_comm]

theorem internal_not_interface (r : ℕ) {u v w : Point} (hvw : v ≠ w) :
    Disjoint (Q r u).bonds (interface r v w) := by
  refine Finset.disjoint_left.mpr ?_
  intro e he hi
  have hh := (Box.mem_bonds _ _).mp he
  rw [mem_interface] at hi
  rcases hi with hi|hi
  · exact hvw ((cube_unique r hi.1 hh.1).trans (cube_unique r hh.2 hi.2))
  · exact hvw ((cube_unique r hi.2 hh.2).trans (cube_unique r hh.1 hi.1))

end Coarse
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace LatticeGraph

end LatticeGraph

namespace Coarse
theorem bits_disjoint (m : Model) (r : ℕ) {v w : Point} (h : v ≠ w) :
    Disjoint ((Q r v).bits m) ((Q r w).bits m) := by
  cases m
  · apply Finset.disjoint_left.mpr
    intro e he hf
    exact h (cube_unique r ((Box.mem_bonds _ _).mp he).1 ((Box.mem_bonds _ _).mp hf).1)
  · exact Q_disjoint r h

theorem bits_link_disjoint (m : Model) (r : ℕ) (u : Point) {v w : Point} (h : v ≠ w) :
    Disjoint ((Q r u).bits m) (linkBits m r v w) := by
  cases m
  · exact internal_not_interface r h
  · exact Finset.disjoint_empty_right _

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
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

namespace Packet
variable {r : ℕ}
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
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

theorem outward_injective : Function.Injective outward := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [outward,PlanarBoundary.outward]

theorem neighbor_ne (v : Point) (d : Direction) : v+outward d ≠ v := by
  intro h
  have hh : outward d = 0 := add_left_cancel (h.trans (add_zero v).symm)
  fin_cases d <;> norm_num [outward,PlanarBoundary.outward] at hh

namespace Exploration
variable {m : Model} {r : ℕ}

end Exploration
end Coarse
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ExplorationConnectivity ----
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace LatticeGraph

theorem Subgraph.containsBox {G H : LatticeGraph} (h : G.Subgraph H) {B : Box}
    (hB : G.ContainsBox B) : H.ContainsBox B :=
  ⟨hB.1.trans h.1,hB.2.trans h.2⟩

theorem seedReaches_witness (G : LatticeGraph) (m : Model) {c : Vertex} {a b : ℕ}
    (hab : a ≤ b) (hB : G.ContainsBox (Box.cube c b)) {T : Set Vertex} {ω : m.Config}
    (hE : ω ∈ m.SeedReaches c a b T) :
    ∃ x y : G.Node, x.1 ∈ cube c a ∧ y.1 ∈ T ∧ G.Conn m ω x y := by
  obtain ⟨x,hxa,hxo,y,hy,hpath⟩ := hE
  have hxb := cube_mono c hab hxa
  have hyb : y ∈ cube c b := by
    induction hpath with
    | refl => exact hxb
    | tail _ hab _ => exact hab.2.1
  let x' : G.Node := ⟨x,G.containsBox_node hB (Box.contains_cube_iff.mpr hxb)⟩
  let y' : G.Node := ⟨y,G.containsBox_node hB (Box.contains_cube_iff.mpr hyb)⟩
  refine ⟨x',y',hxa,hy,(G.conn_iff m ω x' y').mpr ⟨?_,?_⟩⟩
  · cases m <;> exact hxo
  · apply G.lift_path (r := Within (cube c b) (m.BasicAdj ω)) ?_ ?_ hpath
    · intro x y h
      exact G.containsBox_node hB (Box.contains_cube_iff.mpr h.2.1)
    · intro x y h
      exact G.basicAdj_lift m hB (Box.contains_cube_iff.mpr h.1)
        (Box.contains_cube_iff.mpr h.2.1) h.2.2
end LatticeGraph

namespace Coarse

theorem facing_neighbor (r : ℕ) (d : Direction) {y : Vertex}
    (hy : y ∈ QuarterFace (center r (outward d)) (10*r) (facingFace d)) :
    ∃ z : Vertex, (Q r 0).Contains z ∧ NearestNeighbor z y := by
  have hQ := (quarterFace_subset_boundary _ _ _ hy).1
  rw [mem_cube] at hQ
  have h0 := hQ 0
  have h1 := hQ 1
  have h2 := hQ 2
  have hface := hy.1
  have hr : (0:ℤ) ≤ r := Int.natCast_nonneg _
  fin_cases d <;>
    simp [facingFace,center,outward,PlanarBoundary.outward] at hface h0 h1 h2
  · refine ⟨step y 1,?_,1,Or.inr rfl⟩
    intro i
    fin_cases i <;> simp [Q,Box.cube,center,step] <;> omega
  · let z := Function.update y 0 (y 0-1)
    refine ⟨z,?_,0,Or.inl ?_⟩
    · intro i
      fin_cases i <;> simp [Q,Box.cube,center,z] <;> omega
    · ext i
      by_cases hi : i = 0
      · subst i; simp [z,step]
      · simp [z,step,hi,Ne.symm hi]
  · let z := Function.update y 1 (y 1-1)
    refine ⟨z,?_,1,Or.inl ?_⟩
    · intro i
      fin_cases i <;> simp [Q,Box.cube,center,z] <;> omega
    · ext i
      by_cases hi : i = 1
      · subst i; simp [z,step]
      · simp [z,step,hi,Ne.symm hi]
  · refine ⟨step y 0,?_,0,Or.inr rfl⟩
    intro i
    fin_cases i <;> simp [Q,Box.cube,center,step] <;> omega

theorem root_internal_disjoint (m : Model) (r : ℕ) (d : Direction) :
    Disjoint (rootBits m r) ((Q r (outward d)).bits m) := by
  rw [rootBits,Finset.disjoint_union_left]
  constructor
  · exact bits_disjoint m r (Ne.symm (by simpa only [zero_add] using neighbor_ne 0 d))
  · apply Finset.disjoint_left.mpr
    intro e he hi
    obtain ⟨j,_,he⟩ := Finset.mem_biUnion.mp he
    exact Finset.disjoint_left.mp
      (bits_link_disjoint m r (outward d) (Ne.symm (by simpa only [zero_add] using neighbor_ne 0 j))) hi he

theorem initial_seed_event (m : Model) (r a : ℕ) (ha : a ≤ 4*r) (d : Direction)
    {ω : m.Config} (hO : ω ∈ allValue (rootBits m r) true)
    (hE : ω ∈ m.SeedReaches (center r (outward d)) a (10*r)
      (QuarterFace (center r (outward d)) (10*r) (facingFace d))) :
    ω ∈ ((rootPacket r).child (outward d)).event m := by
  let t := (rootPacket r).child (outward d)
  let G := t.graph
  have hB : G.ContainsBox (Q r (outward d)) := t.contains
  have hroot : G.ContainsBox (Q r 0) :=
    (extendGraph_subgraph r (rootPacket r).graph 0 (outward d) (rootPacket r).contains).containsBox
      (rootPacket r).contains
  obtain ⟨x,y,hxa,hy,hxy⟩ := G.seedReaches_witness m (by omega) hB hE
  obtain ⟨z,hz,hzy⟩ := facing_neighbor r d hy
  let z' : G.Node := ⟨z,G.containsBox_node hroot hz⟩
  let o : G.Node := ⟨0,t.root_mem⟩
  have hrootOpen : ∀ e ∈ (Q r 0).bits m, ω e = true :=
    fun e he => hO e (Finset.mem_union_left _ he)
  have hoz : G.Conn m ω o z' := G.open_box_conn m hroot hrootOpen (zero_in_Q r) hz
  have hzy' : G.Adj m ω z' y := by
    obtain ⟨e,he⟩ := LatticeGraph.neighbor_incidence hzy
    have hi : e ∈ interface r 0 (outward d) := by
      rw [mem_interface]
      have hyQ : (Q r (outward d)).Contains y.1 :=
        Box.contains_cube_iff.mpr (quarterFace_subset_boundary _ _ _ hy).1
      rcases he with ⟨he0,he1⟩ | ⟨he0,he1⟩
      · exact Or.inl ⟨he0 ▸ hz,he1 ▸ hyQ⟩
      · exact Or.inr ⟨he0 ▸ hyQ,he1 ▸ hz⟩
    have hedge : e ∈ G.edges := Finset.mem_union_right _ hi
    cases m
    · exact ⟨e,hedge,he,hO e (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨d,Finset.mem_univ _,hi⟩))⟩
    · exact ⟨⟨e,hedge,he⟩,(G.conn_open .site hoz).2,(G.conn_open .site hxy).2⟩
  refine ⟨x,Box.contains_cube_iff.mpr (cube_mono _ ha hxa),?_⟩
  exact G.conn_trans m hoz (G.conn_trans m (G.conn_adj m hzy') (G.conn_symm m hxy))

theorem initial_promise {m : Model} (sc : ScaleData m) (d : Direction) :
    1-sc.δ < (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real
      (((rootPacket sc.r).child (outward d)).event m) := by
  let E := m.SeedReaches (center sc.r (outward d)) sc.seed (10*sc.r)
    (QuarterFace (center sc.r (outward d)) (10*sc.r) (facingFace d))
  have ha : sc.seed ≤ 4*sc.r := by have := sc.seed_R; have := sc.large_r; omega
  have hdet := m.seedReaches_determined (center sc.r (outward d)) sc.seed (10*sc.r)
    (by omega) (QuarterFace (center sc.r (outward d)) (10*sc.r) (facingFace d))
  have heq : (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real E =
      (ProductCylinder.law (fun _ : m.Bit => sc.q)).real E :=
    fixed_determined_probability _ _ _ (root_internal_disjoint m sc.r d) _ _ hdet
  have hle : (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real E ≤
      (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real
        (((rootPacket sc.r).child (outward d)).event m) := by
    apply finite_measureReal_mono_ae
    filter_upwards [ae_fixed_pattern (fun _ : m.Bit => sc.q) (rootBits m sc.r) (fun _ => true)] with ω hω
    exact fun hE => initial_seed_event m sc.r sc.seed ha d hω hE
  have hh := sc.faces (10*sc.r) (by simp) (center sc.r (outward d)) (facingFace d)
  rw [heq] at hle
  exact (sub_lt_sub_left sc.γδ 1).trans (hh.trans_le hle)

theorem initial_valid {m : Model} (sc : ScaleData m) : (initial m sc.r).Valid sc.q sc.δ := by
  constructor
  · exact Finset.mem_singleton_self _
  · change ((List.ofFn (fun d : Direction => (rootPacket sc.r).child (outward d))).map Packet.vertex).Nodup
    rw [List.map_ofFn]
    exact List.nodup_ofFn.mpr outward_injective
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    simpa only [initial,Packet.child,Finset.mem_singleton,zero_add] using neighbor_ne 0 d
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact Finset.mem_singleton_self _
  · intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    rw [Packet.child_bits]
    apply Finset.union_subset_union ?_ (Finset.Subset.refl _)
    change (LatticeGraph.ofBox (Q sc.r 0)).bits m ⊆ rootBits m sc.r
    have he : (LatticeGraph.ofBox (Q sc.r 0)).bits m = (Q sc.r 0).bits m := by cases m <;> rfl
    rw [he]
    exact Finset.subset_union_left
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact initial_promise sc d

end Coarse
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.Coarse.initial_valid := @_root_.OAI.CriticalZ3.Coarse.initial_valid
