-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.fixed_bad_success_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:57:16.269613+00:00
-- url     : https://prove2.me/submissions/ee96c6e6-67f9-4907-9c7d-2dca79594eca

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/SeedQuality.lean:L215-L236
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.fixed_bad_success_mass. The node keeps its source
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
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_bad_success_mass
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

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

end LatticeGraph
end CriticalZ3

namespace CriticalZ3.LatticeGraph
open Classical
variable (G : LatticeGraph)

theorem outsideBits_disjoint_inside (m : Model) (C : Box) :
    Disjoint (G.outsideBits m C) (C.bits m) := by
  rw [Finset.disjoint_left]
  intro e he he'
  cases m
  · exact (Finset.mem_filter.mp he).2.1 ((Box.mem_bonds C e).mp he').1
  · exact (Finset.mem_filter.mp he).2 ((Box.mem_vertices C e).mp he')

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

theorem successBits_disjoint_outside (m : Model) (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex} (hy : C.Exterior y) :
    Disjoint (C.successBits r m y) (G.outsideBits m C) := by
  have hs := (G.outsideBits_disjoint_inside m C).symm.mono_left
    (Box.bits_mono m (C.seedBox_contained r hw y))
  cases m
  · rw [Box.successBits,Finset.disjoint_insert_left]
    exact ⟨G.entryBit_not_outside .bond hy,hs⟩
  · exact hs

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

theorem allValue_determined (J : Finset E) (b : Bool) :
    ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ allValue J b) := by
  intro ω ω' h
  apply propext
  constructor <;> intro hh e he
  · rw [←h e he]; exact hh e he
  · rw [h e he]; exact hh e he

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

/-- Outside reveals preserve joint seed/quality statistics, as quality is an
interior function rather than an outside-conditional prediction. -/
theorem fixed_bad_success_mass (p : m.Bit → Set.Icc (0 : ℝ) 1) (q : Set.Icc (0 : ℝ) 1)
    (C : Box) (r : ℕ) (hw : ∀ i, C.lower i+r ≤ C.upper i-r)
    {y : Vertex} (hy : C.Exterior y) (ξ : m.Config)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q)
    (F : Set m.Config) (hF : ProductCylinder.DeterminedBy (F := Prop) (C.bits m) (fun ω => ω ∈ F))
    {γ τ : ℝ} (hqual : (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩ F) ≤ (q : ℝ)^Box.seedCard m r*γ/τ) :
    (ProductCylinder.law (fixedParameter p (G.outsideBits m C) ξ)).real
      (allValue (C.successBits r m y) true ∩ F) ≤ (q : ℝ)^Box.successCard m r*γ/τ := by
  have hdis : Disjoint (G.outsideBits m C) (C.successBits r m y ∪ C.bits m) :=
    Finset.disjoint_union_right.mpr ⟨(G.successBits_disjoint_outside m C r hw hy).symm,
      G.outsideBits_disjoint_inside m C⟩
  have hdet : ProductCylinder.DeterminedBy (F := Prop) (C.successBits r m y ∪ C.bits m)
      (fun ω => ω ∈ allValue (C.successBits r m y) true ∩ F) := by
    intro ω ω' h
    simp only [Set.mem_inter_iff,
      allValue_determined _ _ ω ω' (fun e he => h e (Finset.mem_union_left _ he)),
      hF ω ω' (fun e he => h e (Finset.mem_union_right _ he))]
  rw [fixed_determined_probability p _ _ hdis ξ _ hdet]
  exact bad_success_mass m p q C r hw hy hp F hF hqual

end LatticeGraph
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.fixed_bad_success_mass := @_root_.OAI.CriticalZ3.LatticeGraph.fixed_bad_success_mass
