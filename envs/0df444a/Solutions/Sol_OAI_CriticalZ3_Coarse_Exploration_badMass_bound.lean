-- Prove2me | solution 1 for OAI.CriticalZ3.Coarse.Exploration.badMass_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:49:33.22129+00:00
-- url     : https://prove2.me/submissions/d870e358-4de6-4cf0-86ef-c45101d07f09

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ExplorationInvariant.lean:L110-L174
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Coarse.Exploration.badMass_bound. The node keeps its source
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
import Theorems.Thm_OAI_AdaptiveReveals_Scheme_badMass_eq_probability
import Theorems.Thm_OAI_CriticalZ3_Coarse_cube_unique
import Theorems.Thm_OAI_CriticalZ3_Coarse_extendGraph_pair
import Theorems.Thm_OAI_CriticalZ3_Coarse_internal_pair_not_exposed
import Theorems.Thm_OAI_CriticalZ3_ScaleData_relay_in_frame
import Theorems.Thm_OAI_InfiniteConditioning_conditional_failure_mass
import Theorems.Thm_OAI_InfiniteConditioning_map_replace

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

-- ---- from OAI.Probability.CriticalZ3.Symmetry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

namespace CriticalZ3
open Classical

end CriticalZ3

namespace CriticalZ3
open Classical

namespace SignedSymmetry

theorem cube_map (S : SignedSymmetry) (c x : Vertex) (n : ℕ) :
    x ∈ cube c n ↔ S.vertex x ∈ cube (S.vertex c) n := by
  simp only [mem_cube]
  have he (i : Fin 3) :
      (S.vertex c i - (n:ℤ) ≤ S.vertex x i ∧ S.vertex x i ≤ S.vertex c i + (n:ℤ)) ↔
      (c (S.perm i)-(n:ℤ) ≤ x (S.perm i) ∧ x (S.perm i) ≤ c (S.perm i)+(n:ℤ)) := by
    dsimp [vertex]
    cases S.signs i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  simp_rw [he]
  constructor
  · intro h i; exact h _
  · intro h i; simpa only [Equiv.apply_symm_apply] using h (S.perm.symm i)

end SignedSymmetry
end CriticalZ3

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
theorem conn_iff (m : Model) (ω : m.Config) (x y : G.Node) :
    G.Conn m ω x y ↔ G.Open m ω x ∧ Relation.ReflTransGen (G.Adj m ω) x y := by
  cases m
  · exact ⟨fun h => ⟨trivial,h⟩,fun h => h.2⟩
  · rfl

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

theorem measurableSet_meets (m : Model) (o : G.Node) (T : Set Vertex) :
    MeasurableSet {ω | G.Meets m ω o T} :=
  ProductCylinder.measurableSet_determined _ _ (fun ω ω' h =>
    eq_iff_iff.mp (G.meets_determined m o T ω ω' h))

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

omit [Countable E] in
theorem replace_eq_of_pattern {J : Finset E} {ξ ω : E → Bool} (h : ω ∈ pattern J ξ) :
    replace J ξ ω = ω := by
  funext e
  by_cases he : e ∈ J
  · exact (ite_eq_left he).trans (h e he).symm
  · exact ite_eq_right he

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

-- ---- from OAI.Probability.CriticalZ3.ConditionalQuality ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

theorem conditional_failure_bound (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (H C : Set (E → Bool))
    (hH : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ H))
    (hC : MeasurableSet C) {δ ε : ℝ} (hδ : 0 < δ)
    (hfail : (ProductCylinder.law p).real (H ∩ Cᶜ) ≤ ε) :
    (ProductCylinder.law p).real {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} ≤ ε/δ := by
  apply (le_div_iff₀ hδ).mpr
  simpa only [mul_comm] using (conditional_failure_mass p J H C hH hC hδ.le).trans hfail

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

end Box

namespace Model

end Model

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

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

-- ---- from OAI.Probability.CriticalZ3.Coarse ----
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace Coarse
theorem zero_outside_pair (r : ℕ) {v w : Point} (hv : v ≠ 0) (hw : w ≠ 0) :
    (0:Vertex) ∉ PairRegion r v w := by
  rintro (h|h)
  · exact hv (cube_unique r h (zero_in_Q r))
  · exact hw (cube_unique r h (zero_in_Q r))

theorem relay_cube_eq (c : Vertex) (n : ℕ) : LatticeRelay.Cube c n = cube c n := by
  ext x
  rw [mem_cube]
  constructor <;> intro h i
  · have hh := h i
    change |x i-c i| ≤ (n:ℤ) at hh
    rw [abs_le] at hh
    omega
  · have hh := h i
    change |x i-c i| ≤ (n:ℤ)
    rw [abs_le]
    omega

theorem image_cube (S : SignedSymmetry) (c : Vertex) (n : ℕ) : S.vertex '' cube c n = cube (S.vertex c) n := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (S.cube_map c y n).mp hy
  · intro hx
    exact ⟨S.vertex.symm x,(S.cube_map c _ n).mpr (by simpa only [Equiv.apply_symm_apply] using hx),S.vertex.apply_symm_apply x⟩

theorem prism_eq_cubes (r : ℕ) : LatticeRelay.Prism r =
    LatticeRelay.Cube 0 (10*r) ∪ LatticeRelay.Cube (LatticeRelay.axisCenter (20*(r:ℤ)+1)) (10*r) := by
  ext x
  have hr : (0:ℤ) ≤ r := Int.natCast_nonneg _
  constructor
  · intro hx
    by_cases h : x 0 ≤ 10*(r:ℤ)
    · left
      intro i
      by_cases hi : i = 0
      · subst i
        change |x 0-0| ≤ _
        rw [sub_zero,abs_le]
        exact ⟨hx.1,h⟩
      · simpa only [Pi.zero_apply,sub_zero] using hx.2.2 i hi
    · right
      intro i
      by_cases hi : i = 0
      · subst i
        change |x 0-(20*(r:ℤ)+1)| ≤ _
        change |x 0-(20*(r:ℤ)+1)| ≤ 10*(r:ℤ)
        rw [abs_le]
        have hh := hx.2.1
        omega
      · simpa only [LatticeRelay.axisCenter,hi,ite_false,sub_zero] using hx.2.2 i hi
  · rintro (hx|hx)
    · have hh := hx 0
      change |x 0-0| ≤ 10*(r:ℤ) at hh
      rw [sub_zero,abs_le] at hh
      refine ⟨hh.1,by omega,?_⟩
      intro i _
      simpa only [Pi.zero_apply,sub_zero] using hx i
    · have hh := hx 0
      change |x 0-(20*(r:ℤ)+1)| ≤ 10*(r:ℤ) at hh
      rw [abs_le] at hh
      refine ⟨by omega,by omega,?_⟩
      intro i hi
      simpa only [LatticeRelay.axisCenter,hi,ite_false,sub_zero] using hx i

theorem frame_prism (r : ℕ) (v : Point) (d : Direction) :
    (frame r v d).vertex '' LatticeRelay.Prism r = PairRegion r v (v+outward d) := by
  rw [prism_eq_cubes,Set.image_union]
  have he : (10:ℤ)*r = (10*r:ℕ) := by push_cast; rfl
  rw [he,relay_cube_eq,relay_cube_eq,image_cube,image_cube,frame_zero,frame_next]
  ext x
  simp only [Set.mem_union,PairRegion,Set.mem_ofPred_eq,Q,Box.contains_cube_iff]

theorem neighboring_relay {model : Model} (s : ScaleData model) (G : LatticeGraph)
    (p : model.Bit → Set.Icc (0:ℝ) 1) (v : Point) (d : Direction)
    (hG : G.ContainsSet (PairRegion s.r v (v+outward d)))
    (hp : model.UniformOn p s.q (PairRegion s.r v (v+outward d)))
    (o : G.Node) (ho : o.1 ∉ PairRegion s.r v (v+outward d)) :
    (ProductCylinder.law p).real {ω | G.Meets model ω o {x | (B s.r v).Contains x} ∧
      ¬G.Meets model ω o {x | (B s.r (v+outward d)).Contains x}} ≤ 13*s.η := by
  have h := s.relay_in_frame G p (frame s.r v d) (by rwa [frame_prism]) (by rwa [frame_prism]) o
    (by rwa [frame_prism])
  simpa only [frame_zero,frame_next,B,Box.contains_cube_iff,Set.ofPred_mem_eq] using h
end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace LatticeGraph

theorem conn_inclusion {G H : LatticeGraph} (h : G.Subgraph H) (m : Model) {ω : m.Config}
    {x y : G.Node} (hc : G.Conn m ω x y) :
    H.Conn m ω ⟨x.1,h.1 x.2⟩ ⟨y.1,h.1 y.2⟩ := by
  rw [G.conn_iff] at hc
  rw [H.conn_iff]
  refine ⟨?_,hc.2.lift (fun z : G.Node => (⟨z.1,h.1 z.2⟩ : H.Node)) ?_⟩
  · cases m <;> exact hc.1
  · intro a b hab
    cases m
    · obtain ⟨e,he,hi,ho⟩ := hab
      exact ⟨e,h.2 he,hi,ho⟩
    · obtain ⟨⟨e,he,hi⟩,ha,hb⟩ := hab
      exact ⟨⟨e,h.2 he,hi⟩,ha,hb⟩

theorem meets_inclusion {G H : LatticeGraph} (h : G.Subgraph H) (m : Model) {ω : m.Config}
    {o : G.Node} {T : Set Vertex} (hc : G.Meets m ω o T) :
    H.Meets m ω ⟨o.1,h.1 o.2⟩ T := by
  obtain ⟨y,hy,hc⟩ := hc
  exact ⟨⟨y.1,h.1 y.2⟩,hy,conn_inclusion h m hc⟩

end LatticeGraph

namespace Coarse
end Coarse
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.AdaptiveReveals ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uF

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace AdaptiveReveals
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning
variable {E V S : Type} [Countable E] [DecidableEq V]

namespace Scheme
variable (P : Scheme E V S)

end Scheme
end AdaptiveReveals

namespace InfiniteConditioning
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

namespace History
omit [Countable E] in
theorem freeze_determined (h : History E) {J R : Finset E} {F : Sort uF}
    (f : (E → Bool) → F) (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hJ : J ⊆ h.known ∪ R) :
    ∀ ω ω', (∀ e ∈ R, ω' e = ω e) → f (h.freeze ω') = f (h.freeze ω) := by
  intro ω ω' he
  apply hf
  intro e heJ
  by_cases hk : e ∈ h.known
  · simp only [freeze,replace,ite_eq_left hk]
  · have hr := (Finset.mem_union.mp (hJ heJ)).resolve_left hk
    simp only [freeze,replace,ite_eq_right hk,he e hr]

omit [Countable E] in
theorem observe_outcome (h : History E) {J R : Finset E} {F : Sort uF}
    (f : (E → Bool) → F) (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hJ : J ⊆ h.known ∪ R) (hR : Disjoint R h.known) (ω : E → Bool) :
    f (h.observe R ω).values = f (h.freeze ω) := by
  apply hf
  intro e he
  rcases Finset.mem_union.mp (hJ he) with hk|hr
  · have hn : e ∉ R := fun hh => Finset.disjoint_left.mp hR hh hk
    simp only [observe,freeze,replace,ite_eq_right hn,ite_eq_left hk]
  · have hn : e ∉ h.known := fun hh => Finset.disjoint_left.mp hR hr hh
    simp only [observe,freeze,replace,ite_eq_right hn,ite_eq_left hr]

theorem ae_freeze (h : History E) (q : Set.Icc (0:ℝ) 1) :
    ∀ᵐ ω ∂ProductCylinder.law (h.parameter q), h.freeze ω = ω := by
  filter_upwards [ae_fixed_pattern (fun _ => q) h.known h.values] with ω hω
  exact replace_eq_of_pattern hω

theorem probability_freeze (h : History E) (q : Set.Icc (0:ℝ) 1) (A : Set (E → Bool)) :
    (ProductCylinder.law (h.parameter q)).real {ω | h.freeze ω ∈ A} =
      (ProductCylinder.law (h.parameter q)).real A := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [h.ae_freeze q] with ω hω
  show (h.freeze ω ∈ A) = (ω ∈ A)
  rw [hω]
end History
end InfiniteConditioning

end OAI

-- ---- from OAI.Probability.CriticalZ3.Exploration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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
theorem measurableSet_event (t : Packet r) (m : Model) : MeasurableSet (t.event m) :=
  t.graph.measurableSet_meets m _ _

theorem event_determined (t : Packet r) (m : Model) :
    ProductCylinder.DeterminedBy (F := Prop) (t.graph.bits m) (fun ω => ω ∈ t.event m) :=
  t.graph.meets_determined m _ _

end Packet

namespace Exploration
variable {m : Model} {r : ℕ}
theorem reveal_disjoint (s : Exploration m r) : Disjoint s.reveal s.history.known := by
  cases h : s.queue with
  | nil => simp only [reveal,h]; exact Finset.disjoint_empty_left _
  | cons t ts => simp only [reveal,h]; exact Finset.sdiff_disjoint

end Exploration
end Coarse
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

namespace Exploration
variable {m : Model} {r : ℕ}

theorem processed_visited (s : Exploration m r) : s.processed ⊆ s.visited := Finset.subset_union_left

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

end Exploration
end Coarse
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ExplorationInvariant ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem after_determined (s : Exploration m r) :
    ProductCylinder.DeterminedBy s.reveal (s.after) := by
  intro ω ω' he
  unfold after History.observe
  congr 1
  funext e
  by_cases hr : e ∈ s.reveal
  · simp only [replace,ite_eq_left hr,he e hr]
  · simp only [replace,ite_eq_right hr]

theorem markedBad_determined (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    ProductCylinder.DeterminedBy s.reveal (s.markedBad q δ) := by
  intro ω ω' he
  have h := s.after_determined ω ω' he
  have ha (t : Packet r) : s.Accept q δ t ω' ↔ s.Accept q δ t ω := by simp only [Accept,h]
  cases hq : s.queue <;> simp only [markedBad,hq,ha]

theorem badMass_eq (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    (scheme (r := r) q δ).badMass s =
      (ProductCylinder.law (s.history.parameter q)).real {ω | s.markedBad q δ ω = true} := by
  rw [AdaptiveReveals.Scheme.badMass_eq_probability]
  congr 2
  ext ω
  change (s.markedBad q δ (ProductCylinder.extend s.reveal (s.reveal.restrict ω)) = true) ↔ _
  rw [←ProductCylinder.determinedBy_eq_extend (s.markedBad_determined q δ) ω]

theorem frozenEvent_determined {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    ProductCylinder.DeterminedBy (F := Prop) s.reveal (fun ω => ω ∈ s.frozenEvent t) :=
  s.history.freeze_determined _ (t.event_determined m) (by
    simpa only [Finset.subset_iff,Finset.mem_union] using current_support hs hq)

theorem frozenEvent_probability (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (t : Packet r) :
    (ProductCylinder.law (s.history.parameter q)).real (s.frozenEvent t) =
      (ProductCylinder.law (s.history.parameter q)).real (t.event m) :=
  s.history.probability_freeze q (t.event m)

theorem accept_current_iff {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) (ω : m.Config) :
    (s.after ω).values ∈ t.event m ↔ ω ∈ s.frozenEvent t := by
  exact Eq.to_iff (s.history.observe_outcome _ (t.event_determined m)
    (by simpa only [Finset.subset_iff,Finset.mem_union] using current_support hs hq) s.reveal_disjoint ω)

theorem relay_failure (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) {t : Packet sc.r} {ts : List (Packet sc.r)} (hq : s.queue = t::ts)
    (d : Direction) (hx : t.vertex+outward d ∉ s.visited) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      (s.frozenEvent t ∩ ((t.child (t.vertex+outward d)).event m)ᶜ) ≤ 13*sc.η := by
  have htq : t ∈ s.queue := by simp [hq]
  have hv := hs.unprocessed t htq
  have hxD : t.vertex+outward d ∉ s.processed := fun hh => hx (s.processed_visited hh)
  have hv0 : t.vertex ≠ 0 := fun he => hv (he ▸ hs.root_processed)
  have hx0 : t.vertex+outward d ≠ 0 := fun he => hxD (he ▸ hs.root_processed)
  have hfresh : m.UniformOn (s.history.parameter sc.q) sc.q
      (PairRegion sc.r t.vertex (t.vertex+outward d)) := by
    intro e he
    apply ite_eq_right
    intro hk
    exact internal_pair_not_exposed m sc.r hs.root_processed hv hxD he (hs.exposed hk)
  have hrelay := neighboring_relay sc (t.child (t.vertex+outward d)).graph
    (s.history.parameter sc.q) t.vertex d
    (extendGraph_pair sc.r t.graph t.vertex _ t.contains) hfresh
    ⟨0,(t.child (t.vertex+outward d)).root_mem⟩ (zero_outside_pair sc.r hv0 hx0)
  have hi : t.event m ∩ ((t.child (t.vertex+outward d)).event m)ᶜ ⊆
      {ω | (t.child (t.vertex+outward d)).graph.Meets m ω
        ⟨0,(t.child (t.vertex+outward d)).root_mem⟩ {y | (B sc.r t.vertex).Contains y} ∧
          ¬(t.child (t.vertex+outward d)).graph.Meets m ω
        ⟨0,(t.child (t.vertex+outward d)).root_mem⟩ {y | (B sc.r (t.vertex+outward d)).Contains y}} := by
    intro ω hω
    exact ⟨LatticeGraph.meets_inclusion (extendGraph_subgraph sc.r t.graph t.vertex _ t.contains) m hω.1,hω.2⟩
  have heq : (ProductCylinder.law (s.history.parameter sc.q)).real
      (s.frozenEvent t ∩ ((t.child (t.vertex+outward d)).event m)ᶜ) =
      (ProductCylinder.law (s.history.parameter sc.q)).real
      (t.event m ∩ ((t.child (t.vertex+outward d)).event m)ᶜ) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [s.history.ae_freeze sc.q] with ω hω
    change ((s.history.freeze ω ∈ t.event m) ∧ _) = ((ω ∈ t.event m) ∧ _)
    rw [hω]
  rw [heq]
  exact (measureReal_mono hi).trans hrelay

theorem badMass_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) :
    (scheme (r := sc.r) sc.q sc.δ).badMass s ≤ CriticalScales.contourError := by
  rw [badMass_eq]
  cases hq : s.queue with
  | nil => simpa only [markedBad,hq,Bool.false_eq_true,Set.ofPred_false,measureReal_empty] using
      CriticalScales.contourError_pos.le
  | cons t ts =>
    let μ := ProductCylinder.law (s.history.parameter sc.q)
    let H := s.frozenEvent t
    let T (d : Direction) : Set m.Config :=
      {ω | ω ∈ H ∧ t.vertex+outward d ∉ s.visited ∧
        (ProductCylinder.law ((s.after ω).parameter sc.q)).real
          ((t.child (t.vertex+outward d)).event m) ≤ 1-sc.δ}
    have hH := frozenEvent_determined hs hq
    have hHm : MeasurableSet H := ProductCylinder.measurableSet_determined _ _
      (fun ω ω' he => Eq.to_iff (hH ω ω' he))
    have hHprob : μ.real Hᶜ < sc.δ := by
      rw [measureReal_compl hHm,probReal_univ]
      have hh := hs.promise t (by simp [hq])
      have he := s.frozenEvent_probability sc.q t
      change μ.real H = μ.real (t.event m) at he
      rw [he]
      linarith
    have hT (d : Direction) : μ.real (T d) ≤ (13*sc.η)/sc.δ := by
      by_cases hx : t.vertex+outward d ∉ s.visited
      · have hh := conditional_failure_bound (s.history.parameter sc.q) s.reveal H
          ((t.child (t.vertex+outward d)).event m) hH
          ((t.child (t.vertex+outward d)).measurableSet_event m) sc.δ_range.1
          (relay_failure sc hs hq d hx)
        have he : T d = {ω | ω ∈ H ∧ conditionalProbability (s.history.parameter sc.q)
            s.reveal ((t.child (t.vertex+outward d)).event m) ω ≤ 1-sc.δ} := by
          ext ω
          simp only [T,hx,not_false_eq_true,true_and,Set.mem_ofPred_eq,after,History.parameter_observe,
            conditionalProbability]
        rwa [he]
      · have he : T d = ∅ := by ext ω; simp only [T,hx,false_and,and_false,Set.mem_ofPred_eq,Set.mem_empty_iff_false]
        rw [he,measureReal_empty]
        exact div_nonneg (mul_nonneg (by norm_num) sc.η_range.1.le) sc.δ_range.1.le
    have hb : {ω | s.markedBad sc.q sc.δ ω = true} ⊆ Hᶜ ∪ ⋃ d, T d := by
      intro ω hω
      have hn : ¬s.Accept sc.q sc.δ t ω := by
        simpa only [Set.mem_ofPred_eq,markedBad,hq,decide_eq_true_eq] using hω
      by_cases hh : ω ∈ H
      · right
        have hcur := (accept_current_iff hs hq ω).mpr hh
        have hpred : ¬∀ u ∈ s.candidates t, 1-sc.δ <
            (ProductCylinder.law ((s.after ω).parameter sc.q)).real (u.event m) :=
          fun hp => hn ⟨hcur,hp⟩
        push Not at hpred
        obtain ⟨u,hu,hfail⟩ := hpred
        obtain ⟨⟨d,rfl⟩,hx⟩ := (mem_candidates s t u).mp hu
        exact Set.mem_iUnion.mpr ⟨d,hh,hx,hfail⟩
      · exact Or.inl hh
    calc
      _ ≤ μ.real (Hᶜ ∪ ⋃ d, T d) := measureReal_mono hb
      _ ≤ μ.real Hᶜ + μ.real (⋃ d, T d) := measureReal_union_le _ _
      _ ≤ μ.real Hᶜ + ∑ d, μ.real (T d) := add_le_add le_rfl (measureReal_iUnion_fintype_le _)
      _ ≤ μ.real Hᶜ + ∑ _d : Direction, (13*sc.η)/sc.δ :=
        add_le_add le_rfl (Finset.sum_le_sum (fun d _ => hT d))
      _ = μ.real Hᶜ + 52*sc.η/sc.δ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
      _ ≤ sc.δ + 52*sc.η/sc.δ := add_le_add hHprob.le le_rfl
      _ ≤ CriticalScales.contourError := sc.failure_budget.le

end Coarse.Exploration
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

end Coarse.Exploration
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse OAI.CriticalZ3.Coarse.Exploration
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.Coarse.Exploration.badMass_bound := @_root_.OAI.CriticalZ3.Coarse.Exploration.badMass_bound
