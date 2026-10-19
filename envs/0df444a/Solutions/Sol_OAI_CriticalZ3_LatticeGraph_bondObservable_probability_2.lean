-- Prove2me | solution 2 for OAI.CriticalZ3.LatticeGraph.bondObservable_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:19:07.068373+00:00
-- url     : https://prove2.me/submissions/9cdae8f5-c6b3-4a9e-9de3-e328a48ba1d0

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/LatticeGraph.lean:L178-L203
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.bondObservable_probability. The node keeps its source
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
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_bondConn_iff_hypergraph

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

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

section FiniteLaw
variable [Fintype E]

theorem eventProb_eq_real (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    eventProb p P = (law p).real {ω | P ω} := by
  simpa [eventProb, Set.indicator] using
    (integral_indicator_one (μ := law p) (s := {ω | P ω}) (Set.toFinite _).measurableSet)

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

end Site

end HyperedgeComparison

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

theorem bondMeets_determined (o : G.Node) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) G.edges (fun ω => G.BondMeets ω o T) := by
  intro ω ω' h
  exact propext (exists_congr (fun y => and_congr_right (fun _ => G.bondConn_determined ω ω' h o y)))

/-- Any observable of the finite graph's connections is a finite cylinder. -/
theorem bondObservable_probability (p : Bond → Set.Icc (0 : ℝ) 1)
    (φ : (G.Node → Set Vertex → Prop) → Prop) :
    (ProductCylinder.law p).real {ω | φ (G.BondMeets ω)} =
      HyperedgeComparison.eventProb (fun e : G.edges => p e.1)
        (fun ω => φ (fun o T => HyperedgeComparison.Meets G.hypergraph ω ∅ o {y | y.1 ∈ T})) := by
  have hd : ∀ ω ω', (∀ e ∈ G.edges, ω' e = ω e) →
      (φ (G.BondMeets ω') ↔ φ (G.BondMeets ω)) := by
    intro ω ω' he
    have hm : G.BondMeets ω' = G.BondMeets ω := by
      funext o T; exact G.bondMeets_determined o T ω ω' he
    rw [hm]
  rw [Measure.real_def,ProductCylinder.probability_determined G.edges p {ω | φ (G.BondMeets ω)} hd,
    HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  have he : (fun e : G.edges => ProductCylinder.extend G.edges ξ e.1) = ξ := by
    funext e; simp [ProductCylinder.extend,e.2]
  have hm : G.BondMeets (ProductCylinder.extend G.edges ξ) =
      fun o T => HyperedgeComparison.Meets G.hypergraph ξ ∅ o {y | y.1 ∈ T} := by
    funext o T
    apply propext
    simp only [BondMeets,G.bondConn_iff_hypergraph,he,
      HyperedgeComparison.Meets,Set.mem_ofPred_eq]
  simp only [Set.mem_ofPred_eq,hm]

end LatticeGraph
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical MeasureTheory ProbabilityTheory


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.bondObservable_probability := @_root_.OAI.CriticalZ3.LatticeGraph.bondObservable_probability
