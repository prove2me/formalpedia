-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.exists_shell
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:47:33.270418+00:00
-- url     : https://prove2.me/submissions/4fc40b53-8fcf-433b-b33d-7d4cc58b692c

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ShellProbability.lean:L83-L130
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.exists_shell. The node keeps its source
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
import Theorems.Thm_OAI_CriticalZ3_Box_exterior_neighbor_unique
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_first_entry
import Theorems.Thm_OAI_InfiniteConditioning_disjoint_blocks_probability
import Theorems.Thm_OAI_InfiniteConditioning_map_replace
import Theorems.Thm_OAI_InfiniteConditioning_select_probability_lower
import Theorems.Thm_OAI_ShellEstimates_exists_layer

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

theorem determinedBy_eq_extend {J : Finset E} {f : (E → Bool) → F}
    (hf : DeterminedBy J f) (ω : E → Bool) : f ω = f (extend J (J.restrict ω)) := by
  apply hf
  intro e he
  simp [extend,he,Finset.restrict]

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

-- ---- from OAI.Probability.CriticalZ3.LatticeGraph ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open Classical MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory

theorem incidence_neighbor {e : Bond} {x y : Vertex} (h : Incidence e x y) :
    NearestNeighbor x y := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨e.2,Or.inl rfl⟩
  · exact ⟨e.2,Or.inr rfl⟩

namespace LatticeGraph
variable (G : LatticeGraph)

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.BoxGeometry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3

open Classical

namespace Box

theorem expand_mono (B : Box) {j k : ℕ} (hjk : j ≤ k) {x : Vertex}
    (h : (B.expand j).Contains x) : (B.expand k).Contains x := by
  intro i
  have hi := h i
  change B.lower i-j ≤ x i ∧ x i ≤ B.upper i+j at hi
  change B.lower i-k ≤ x i ∧ x i ≤ B.upper i+k
  omega

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

theorem adj_neighbor (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    NearestNeighbor x.1 y.1 := by
  cases m
  · obtain ⟨e,_,he,_⟩ := h; exact incidence_neighbor he
  · obtain ⟨⟨e,_,he⟩,_⟩ := h; exact incidence_neighbor he

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.EntryLayers ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

theorem step_ge (x : Vertex) (i : Fin 3) : x ≤ step x i := by
  intro j; simp only [step]; split_ifs <;> omega

theorem step_direction_injective (x : Vertex) : Function.Injective (step x) := by
  intro i j h
  by_contra hij
  have hh := congrFun h i
  simp only [step,ite_true,ite_eq_right (Ne.symm hij),add_zero] at hh
  omega

theorem step_no_reverse (x y : Vertex) (i j : Fin 3)
    (h : y = step x i) : x ≠ step y j := by
  intro hh
  have hle : y i ≤ x i := by rw [hh]; exact step_ge y j i
  have hlt : x i < y i := by simp [h,step]
  exact not_lt_of_ge hle hlt

theorem incidence_unique {e f : Bond} {x y : Vertex}
    (he : Incidence e x y) (hf : Incidence f x y) : e = f := by
  rcases he with ⟨hx,hy⟩ | ⟨hy,hx⟩ <;> rcases hf with ⟨hx',hy'⟩ | ⟨hy',hx'⟩
  · apply Prod.ext
    · exact hx.symm.trans hx'
    · apply step_direction_injective x
      simpa only [←hx,←hx'] using hy.symm.trans hy'
  · exact False.elim (step_no_reverse x y e.2 f.2 (by simpa [←hx] using hy)
      (by simpa [←hy'] using hx'))
  · exact False.elim (step_no_reverse y x e.2 f.2 (by simpa [←hy] using hx)
      (by simpa [←hx'] using hy'))
  · apply Prod.ext
    · exact hy.symm.trans hy'
    · apply step_direction_injective y
      simpa only [←hy,←hy'] using hx.symm.trans hx'

theorem neighborBond_incidence {x y : Vertex} (h : NearestNeighbor x y) :
    Incidence (neighborBond x y) x y := by
  simp only [neighborBond,dite_eq_left h]
  exact (LatticeGraph.neighbor_incidence h).choose_spec

theorem neighborBond_eq {e : Bond} {x y : Vertex} (he : Incidence e x y) :
    neighborBond x y = e := incidence_unique (neighborBond_incidence (incidence_neighbor he)) he

namespace Box

theorem entry_spec {C : Box} {y : Vertex} (h : C.Exterior y) :
    C.Contains (C.entry y) ∧ NearestNeighbor y (C.entry y) := by
  simp only [entry,dite_eq_left h]
  exact h.2.choose_spec

theorem entry_eq {C : Box} {y z : Vertex} (hy : ¬C.Contains y)
    (hz : C.Contains z) (h : NearestNeighbor y z) : C.entry y = z := by
  have hey : C.Exterior y := ⟨hy,z,hz,h⟩
  exact C.exterior_neighbor_unique hy (entry_spec hey).1 hz (entry_spec hey).2 h

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

theorem meets_entrants_nonempty (m : Model) {C : Box} {ω : m.Config} {o : G.Node}
    (ho : ¬C.Contains o.1) (h : G.Meets m ω o {x | C.Contains x}) :
    (G.entrants m C ω o).Nonempty := by
  obtain ⟨z,hz,hz'⟩ := h
  obtain ⟨y,w,hy,_,_⟩ := G.first_entry m ho hz hz'
  exact ⟨y.1,hy⟩

theorem entryBit_open (m : Model) {C : Box} {ω : m.Config} {y z : G.Node}
    (hy : ¬C.Contains y.1) (hz : C.Contains z.1) (h : G.Adj m ω y z) :
    ω (C.entryBit m y.1) = true := by
  have he := C.entry_eq hy hz (G.adj_neighbor m h)
  cases m
  · obtain ⟨e,_,hi,ho⟩ := h
    simpa only [Box.entryBit,he,neighborBond_eq hi] using ho
  · simpa only [Box.entryBit,he] using h.2.2

theorem entryBits_card (m : Model) (C : Box) (ω : m.Config) (o : G.Node) :
    (G.entryBits m C ω o).card ≤ (G.entrants m C ω o).card := Finset.card_image_le

theorem blocked_not_meets (m : Model) {C : Box} {ω : m.Config} {o : G.Node}
    (ho : ¬C.Contains o.1) (hb : G.Blocked m C ω o) :
    ¬G.Meets m ω o {x | C.Contains x} := by
  rintro ⟨z,hz,hp⟩
  obtain ⟨y,w,hy,hw,hyw⟩ := G.first_entry m ho hz hp
  have hyout := ((G.mem_entrants m C ω o y).mp hy).1.1
  have hopen := G.entryBit_open m hyout hw hyw
  have hclosed := hb (C.entryBit m y.1) (Finset.mem_image.mpr ⟨y.1,hy,rfl⟩)
  exact Bool.noConfusion (hopen.symm.trans hclosed)

/-- The shell blocking events are disjoint for the actual induced-outside
paths. This is the pathwise argument, not a probabilistic assumption. -/
theorem blocked_earlier_entrants (m : Model) {B : Box} {i j : ℕ} (hij : i < j)
    {ω : m.Config} {o : G.Node} (ho : ¬(B.expand j).Contains o.1)
    (hb : G.Blocked m (B.expand j) ω o) : G.entrants m (B.expand i) ω o = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hyG : y ∈ G.vertices := (Finset.mem_filter.mp hy).1
  obtain ⟨hey,hry⟩ := (G.mem_entrants m (B.expand i) ω o ⟨y,hyG⟩).mp hy
  have hyj : (B.expand j).Contains y := by
    have he := Box.exterior_expand hey
    rw [Box.expand_expand] at he
    exact B.expand_mono (by omega) he
  exact G.blocked_not_meets m ho hb ⟨⟨y,hyG⟩,hyj,G.outsideReach_conn m hry⟩

end LatticeGraph
end CriticalZ3

namespace CriticalZ3.LatticeGraph
open Classical
variable (G : LatticeGraph)

theorem outsideAdj_determined (m : Model) (C : Box) (ω ω' : m.Config)
    (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e) (x y : G.Node) :
    G.OutsideAdj m C ω' x y ↔ G.OutsideAdj m C ω x y := by
  have hh (ω ω' : m.Config) (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e)
      (ha : G.OutsideAdj m C ω' x y) : G.OutsideAdj m C ω x y := by
    refine ⟨ha.1,ha.2.1,?_⟩
    cases m
    · obtain ⟨e,he,hi,ho⟩ := ha.2.2
      refine ⟨e,he,hi,?_⟩
      have hem : e ∈ G.outsideBits .bond C := by
        apply Finset.mem_filter.mpr
        refine ⟨he,?_⟩
        rcases hi with ⟨hx,hy⟩ | ⟨hy,hx⟩
        · exact ⟨hx ▸ ha.1,hy ▸ ha.2.1⟩
        · exact ⟨hy ▸ ha.2.1,hx ▸ ha.1⟩
      rw [←h e hem]; exact ho
    · exact ⟨ha.2.2.1,(h x.1 (Finset.mem_filter.mpr ⟨x.2,ha.1⟩)) ▸ ha.2.2.2.1,
        (h y.1 (Finset.mem_filter.mpr ⟨y.2,ha.2.1⟩)) ▸ ha.2.2.2.2⟩
  exact ⟨hh ω ω' h, hh ω' ω (fun e he => (h e he).symm)⟩

theorem outsideReach_determined (m : Model) (C : Box) (ω ω' : m.Config)
    (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e) (o y : G.Node) :
    G.OutsideReach m C ω' o y ↔ G.OutsideReach m C ω o y := by
  by_cases ho : C.Contains o.1
  · simp only [OutsideReach,ho,not_true_eq_false,false_and]
  have hr : G.OutsideAdj m C ω' = G.OutsideAdj m C ω := by
    funext x y; exact propext (G.outsideAdj_determined m C ω ω' h x y)
  have hop : G.Open m ω' o ↔ G.Open m ω o := by
    cases m
    · rfl
    · change (ω' o.1 = true) ↔ (ω o.1 = true)
      rw [h o.1 (Finset.mem_filter.mpr ⟨o.2,ho⟩)]
  simp only [OutsideReach,hr,hop]

theorem entrants_determined (m : Model) (C : Box) (o : G.Node) :
    ProductCylinder.DeterminedBy (G.outsideBits m C) (fun ω => G.entrants m C ω o) := by
  intro ω ω' h
  ext y
  simp only [entrants,Finset.mem_filter,G.outsideReach_determined m C ω ω' h]

theorem entryBits_determined (m : Model) (C : Box) (o : G.Node) :
    ProductCylinder.DeterminedBy (G.outsideBits m C) (fun ω => G.entryBits m C ω o) := by
  intro ω ω' h
  simp only [entryBits,G.entrants_determined m C o ω ω' h]

theorem entryBit_not_outside (m : Model) {C : Box} {y : Vertex} (hy : C.Exterior y) :
    C.entryBit m y ∉ G.outsideBits m C := by
  intro he
  have hentry := (Box.entry_spec hy).1
  cases m
  · have hi := neighborBond_incidence (Box.entry_spec hy).2
    obtain ⟨_,hout,hout'⟩ := Finset.mem_filter.mp he
    rcases hi with ⟨_,hz⟩ | ⟨hz,_⟩
    · exact hout' (hz ▸ hentry)
    · exact hout (hz ▸ hentry)
  · exact (Finset.mem_filter.mp he).2 hentry

theorem entryBits_disjoint_outside (m : Model) (C : Box) (ω : m.Config) (o : G.Node) :
    Disjoint (G.entryBits m C ω o) (G.outsideBits m C) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
  have hyG : y ∈ G.vertices := (Finset.mem_filter.mp hy).1
  exact G.entryBit_not_outside m ((G.mem_entrants m C ω o ⟨y,hyG⟩).mp hy).1 he'

end CriticalZ3.LatticeGraph

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

omit [Countable E] in
theorem pattern_extend_iff (J : Finset E) (a : J → Bool) (ω : E → Bool) :
    ω ∈ pattern J (ProductCylinder.extend J a) ↔ J.restrict ω = a := by
  constructor
  · intro h; funext e
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left e.2] using h e e.2
  · intro h e he
    have hh := congrFun h ⟨e,he⟩
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left he] using hh

theorem measurableSet_select (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) :
    MeasurableSet {ω | ω ∈ A (J.restrict ω)} := by
  have heq : {ω | ω ∈ A (J.restrict ω)} =
      ⋃ a : J → Bool, pattern J (ProductCylinder.extend J a) ∩ A a := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,pattern_extend_iff]
    exact ⟨fun h => ⟨J.restrict ω,rfl,h⟩, fun ⟨a,ha,h⟩ => ha.symm ▸ h⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun a => (measurableSet_pattern _ _).inter (hA a))

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

theorem single_probability (p : E → Set.Icc (0 : ℝ) 1) (e : E) (b : Bool) :
    (ProductCylinder.law p).real {ω | ω e = b} = bitProbability (p e) b := by
  have h := Measure.infinitePi_map_eval (fun e : E => bernoulliMeasure true false (p e)) e
  have hm : Measurable (fun ω : E → Bool => ω e) := measurable_pi_apply e
  have he : {ω : E → Bool | ω e = b} = (fun ω => ω e) ⁻¹' {b} := rfl
  rw [he,Measure.real_def,←Measure.map_apply hm (measurableSet_singleton _)]
  change ((Measure.infinitePi (fun e : E => bernoulliMeasure true false (p e))).map
    (fun ω => ω e) {b}).toReal = _
  rw [h]
  change (bernoulliMeasure true false (p e)).real {b} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton _)]
  cases b <;> simp [bitProbability,unitInterval.coe_symm_eq]

theorem finite_pattern_probability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (ξ : E → Bool) :
    (ProductCylinder.law p).real (pattern J ξ) = ∏ e ∈ J, bitProbability (p e) (ξ e) := by
  classical
  have hd : Pairwise (fun e f : E => Disjoint ({e} : Finset E) {f}) := by
    intro e f h; simpa using h
  have hdet (e : E) : ProductCylinder.DeterminedBy (F := Prop) {e}
      (fun ω : E → Bool => ω e = ξ e) := by
    intro ω ω' h
    dsimp only
    rw [h e (Finset.mem_singleton_self e)]
  have h := disjoint_blocks_probability p (fun e : E => {e}) hd
    (fun e => {ω | ω e = ξ e}) hdet J
  simpa only [pattern,Set.mem_ofPred_eq,single_probability] using h

theorem allValue_determined (J : Finset E) (b : Bool) :
    ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ allValue J b) := by
  intro ω ω' h
  apply propext
  constructor <;> intro hh e he
  · rw [←h e he]; exact hh e he
  · rw [h e he]; exact hh e he

theorem measurableSet_allValue (J : Finset E) (b : Bool) : MeasurableSet (allValue J b) :=
  ProductCylinder.measurableSet_determined J _
    (fun ω ω' h => eq_iff_iff.mp (allValue_determined J b ω ω' h))

theorem allValue_probability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (b : Bool) :
    (ProductCylinder.law p).real (allValue J b) = ∏ e ∈ J, bitProbability (p e) b :=
  finite_pattern_probability p J (fun _ => b)

theorem allValue_probability_constant (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (q : Set.Icc (0 : ℝ) 1) (hp : ∀ e ∈ J, p e = q) (b : Bool) :
    (ProductCylinder.law p).real (allValue J b) = (bitProbability q b)^J.card := by
  rw [allValue_probability]
  calc
    _ = ∏ _e ∈ J, bitProbability q b := Finset.prod_congr rfl (fun e he => by rw [hp e he])
    _ = _ := by rw [Finset.prod_const]

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

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

end InfiniteConditioning

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

theorem shell_blocking_lower (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (C : Box) (o : G.Node) (q : Set.Icc (0 : ℝ) 1) {p₀ : ℝ}
    (hq : (q : ℝ) ≤ p₀) (hp₀ : p₀ < 1) (L : ℕ)
    (hp : ∀ y, C.Exterior y → p (C.entryBit m y) = q) :
    (1-p₀)^L * (ProductCylinder.law p).real
      {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L} ≤
    (ProductCylinder.law p).real
      {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L ∧
        G.Blocked m C ω o} := by
  let J := G.outsideBits m C
  let ξ (a : J → Bool) := ProductCylinder.extend J a
  let P (a : J → Bool) := 0 < (G.entrants m C (ξ a) o).card ∧
    (G.entrants m C (ξ a) o).card < L
  let A (a : J → Bool) := allValue (G.entryBits m C (ξ a) o) false
  have h := select_probability_lower p J P A (fun a => measurableSet_allValue _ _) (b := (1-p₀)^L) ?_
  · have hY (ω : m.Config) : G.entrants m C ω o = G.entrants m C (ξ (J.restrict ω)) o :=
      ProductCylinder.determinedBy_eq_extend (G.entrants_determined m C o) ω
    have hK (ω : m.Config) : G.entryBits m C ω o = G.entryBits m C (ξ (J.restrict ω)) o :=
      ProductCylinder.determinedBy_eq_extend (G.entryBits_determined m C o) ω
    have heP : {ω | P (J.restrict ω)} =
        {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L} := by
      ext ω; simp only [P,Set.mem_ofPred_eq]; rw [←hY ω]
    have heA : {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} =
        {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L ∧
          G.Blocked m C ω o} := by
      ext ω
      simp only [P,A,allValue,Blocked,Set.mem_ofPred_eq]
      rw [←hY ω,←hK ω]
      exact and_assoc
    rwa [heP,heA] at h
  · intro a ha
    rw [fixed_determined_probability p J (G.entryBits m C (ξ a) o)
      (G.entryBits_disjoint_outside m C (ξ a) o).symm _ _ (allValue_determined _ _)]
    rw [allValue_probability_constant p _ q ?_ false]
    · change (1-p₀)^L ≤ (1-(q : ℝ))^(G.entryBits m C (ξ a) o).card
      have h0 : 0 ≤ 1-p₀ := by linarith
      have h1 : 1-(q : ℝ) ≤ 1 := by linarith [q.property.1]
      calc
        _ ≤ (1-(q : ℝ))^L := pow_le_pow_left₀ h0 (by linarith) L
        _ ≤ _ := pow_le_pow_of_le_one (by linarith [q.property.2]) h1
          ((G.entryBits_card m C (ξ a) o).trans (Nat.le_of_lt ha.2))
    · intro e he
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
      have hyG : y ∈ G.vertices := (Finset.mem_filter.mp hy).1
      exact hp y ((G.mem_entrants m C (ξ a) o ⟨y,hyG⟩).mp hy).1

theorem measurableSet_shell_blocked (C : Box) (o : G.Node) (L : ℕ) :
    MeasurableSet {ω | 0 < (G.entrants m C ω o).card ∧
      (G.entrants m C ω o).card < L ∧ G.Blocked m C ω o} := by
  let J := G.outsideBits m C
  let ξ (a : J → Bool) := ProductCylinder.extend J a
  let A (a : J → Bool) : Set m.Config := if 0 < (G.entrants m C (ξ a) o).card ∧
      (G.entrants m C (ξ a) o).card < L then allValue (G.entryBits m C (ξ a) o) false else ∅
  have h := measurableSet_select J A (fun a => by
    dsimp only [A]; split_ifs
    · exact measurableSet_allValue _ _
    · exact MeasurableSet.empty)
  have he : {ω | ω ∈ A (J.restrict ω)} = {ω | 0 < (G.entrants m C ω o).card ∧
      (G.entrants m C ω o).card < L ∧ G.Blocked m C ω o} := by
    ext ω
    have hY := ProductCylinder.determinedBy_eq_extend (G.entrants_determined m C o) ω
    have hK := ProductCylinder.determinedBy_eq_extend (G.entryBits_determined m C o) ω
    change G.entrants m C ω o = G.entrants m C (ξ (J.restrict ω)) o at hY
    change G.entryBits m C ω o = G.entryBits m C (ξ (J.restrict ω)) o at hK
    simp only [A,←hY,←hK,Set.mem_ofPred_eq,Blocked,allValue]
    split_ifs with hh
    · tauto
    · simp only [Set.mem_empty_iff_false]; tauto
  rwa [he] at h

/-- Deterministic shell selection for the finite graph in bond and site percolation. -/
theorem exists_shell (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (B : Box) (o : G.Node) (q : Set.Icc (0 : ℝ) 1) {p₀ : ℝ}
    (hq : (q : ℝ) ≤ p₀) (hp₀ : p₀ < 1) (L a R : ℕ) (haR : a < R)
    (ho : ¬(B.expand R).Contains o.1)
    (hp : ∀ j ∈ Finset.Ico a R, ∀ y, (B.expand j).Exterior y →
      p ((B.expand j).entryBit m y) = q) :
    ∃ j ∈ Finset.Ico a R, (ProductCylinder.law p).real
      {ω | G.Meets m ω o {x | B.Contains x} ∧ (G.entrants m (B.expand j) ω o).card < L} ≤
      1/((1-p₀)^L*(R-a : ℕ)) := by
  let I := ↥(Finset.Ico a R)
  have : Nonempty I := ⟨⟨a,Finset.mem_Ico.mpr ⟨le_rfl,haR⟩⟩⟩
  let Q (i : I) : Set m.Config :=
    {ω | G.Meets m ω o {x | B.Contains x} ∧ (G.entrants m (B.expand i.1) ω o).card < L}
  let A (i : I) : Set m.Config :=
    {ω | 0 < (G.entrants m (B.expand i.1) ω o).card ∧
      (G.entrants m (B.expand i.1) ω o).card < L ∧ G.Blocked m (B.expand i.1) ω o}
  have hoi (i : I) : ¬(B.expand i.1).Contains o.1 := fun h =>
    ho (B.expand_mono (Nat.le_of_lt (Finset.mem_Ico.mp i.2).2) h)
  have hAd : Pairwise (fun i j : I => Disjoint (A i) (A j)) := by
    intro i j hij
    have hi : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    apply Set.disjoint_left.mpr
    intro ω hωi hωj
    rcases lt_or_gt_of_ne hi with hlt | hlt
    · have he := G.blocked_earlier_entrants m hlt (hoi j) hωj.2.2
      have hpos := hωi.1
      rw [he,Finset.card_empty] at hpos
      exact Nat.not_lt_zero _ hpos
    · have he := G.blocked_earlier_entrants m hlt (hoi i) hωi.2.2
      have hpos := hωj.1
      rw [he,Finset.card_empty] at hpos
      exact Nat.not_lt_zero _ hpos
  have hblock (i : I) : (1-p₀)^L * (ProductCylinder.law p).real (Q i) ≤
      (ProductCylinder.law p).real (A i) := by
    have hsub : Q i ⊆ {ω | 0 < (G.entrants m (B.expand i.1) ω o).card ∧
        (G.entrants m (B.expand i.1) ω o).card < L} := by
      intro ω hω
      refine ⟨Finset.card_pos.mpr (G.meets_entrants_nonempty m (hoi i) ?_),hω.2⟩
      obtain ⟨z,hz,hconn⟩ := hω.1
      exact ⟨z,B.contains_expand i.1 hz,hconn⟩
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (pow_nonneg (by linarith) _)).trans
      (G.shell_blocking_lower m p (B.expand i.1) o q hq hp₀ L (hp i.1 i.2))
  obtain ⟨i,hi⟩ := ShellEstimates.exists_layer (ProductCylinder.law p) Q A
    (fun i => G.measurableSet_shell_blocked m (B.expand i.1) o L) hAd
    (pow_pos (by linarith) L) hblock
  refine ⟨i.1,i.2,?_⟩
  simpa only [I,Fintype.card_coe,Nat.card_Ico] using hi

end CriticalZ3.LatticeGraph

namespace FiniteAssociation
open Classical
variable {E : Type}

end FiniteAssociation

namespace ProductCylinder
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

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

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.exists_shell := @_root_.OAI.CriticalZ3.LatticeGraph.exists_shell
