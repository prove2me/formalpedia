-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.bad_success_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:54:31.030772+00:00
-- url     : https://prove2.me/submissions/cdaacd0f-0023-4de2-bd6e-ef174ac35183

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/SeedQuality.lean:L164-L204
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.bad_success_mass. The node keeps its source
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
import Theorems.Thm_OAI_InfiniteConditioning_disjoint_blocks_probability

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
theorem incidence_internal {B : Box} {x y : Vertex} {e : Bond}
    (hx : B.Contains x) (hy : B.Contains y) (he : Incidence e x y) : e ∈ B.bonds := by
  rw [Box.mem_bonds]
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨hx,hy⟩
  · exact ⟨hy,hx⟩

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

theorem crossing_not_internal {C : Box} {y : Vertex} (hy : C.Exterior y) :
    C.entryBit .bond y ∉ C.bonds := by
  intro he
  obtain ⟨h0,h1⟩ := (mem_bonds C _).mp he
  have hi := neighborBond_incidence (entry_spec hy).2
  rcases hi with ⟨hx,_⟩ | ⟨_,hx⟩
  · exact hy.1 (hx ▸ h0)
  · exact hy.1 (hx ▸ h1)

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

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

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E I : Type}

private theorem measurable_determined_sigma (J : Finset E) (A : Set (E → Bool))
    (hA : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ A)) :
    MeasurableSet[⨆ e ∈ (J : Set E), bitSigma e] A := by
  let M := ⨆ e ∈ (J : Set E), bitSigma e
  let mask : (E → Bool) → (E → Bool) := fun ω e => if e ∈ J then ω e else false
  have hm : @Measurable (E → Bool) (E → Bool) M MeasurableSpace.pi mask := by
    apply @Measurable.of_eval (E → Bool) E (fun _ => Bool) M _ mask
    intro e
    by_cases he : e ∈ J
    · simp only [mask,ite_eq_left he]
      exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
    · simp only [mask,ite_eq_right he]; exact measurable_const
  have heq : mask ⁻¹' A = A := by
    ext ω
    exact eq_iff_iff.mp (hA ω (mask ω) (fun e he => by simp [mask,he]))
  rw [←heq]
  exact hm (ProductCylinder.measurableSet_determined J A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h)))

/-- Arbitrary observables of disjoint finite blocks are independent under the
infinite product law, also when other coordinates have been fixed to 0 or 1. -/
theorem indepSet_determined (p : E → Set.Icc (0 : ℝ) 1) (J K : Finset E)
    (hJK : Disjoint J K) (A B : Set (E → Bool))
    (hA : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hB : ProductCylinder.DeterminedBy (F := Prop) K (fun ω => ω ∈ B)) :
    IndepSet A B (ProductCylinder.law p) := by
  have hi : iIndepFun (fun e (ω : E → Bool) => ω e) (ProductCylinder.law p) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hmi : iIndep (bitSigma (E := E)) (ProductCylinder.law p) :=
    (iIndepFun_iff_iIndep _ _ _).mp hi
  have h := indep_iSup_of_disjoint (fun e => (measurable_pi_apply e).comap_le) hmi
    (show Disjoint (J : Set E) (K : Set E) from Finset.disjoint_coe.mpr hJK)
  exact h.indepSet_of_measurableSet (measurable_determined_sigma J A hA)
    (measurable_determined_sigma K B hB)

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

end CriticalZ3.LatticeGraph

namespace FiniteAssociation
open Classical
variable {E : Type}

end FiniteAssociation

namespace ProductCylinder
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

theorem determinedBy_mono {J K : Finset E} (hJK : J ⊆ K) {F : Type}
    {f : (E → Bool) → F} (hf : DeterminedBy J f) : DeterminedBy K f :=
  fun ω ω' h => hf ω ω' (fun e he => h e (hJK he))

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

theorem successBits_contained (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex} (hy : C.Exterior y) :
    C.successBits r m y ⊆ (C.expand 1).bits m := by
  have hs := bits_mono m (fun x hx => C.contains_expand 1 (C.seedBox_contained r hw y x hx))
  cases m
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact LatticeGraph.incidence_internal (exterior_expand hy)
        (C.contains_expand 1 (entry_spec hy).1) (neighborBond_incidence (entry_spec hy).2)
    · exact hs he
  · exact hs
end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

/-- A single bad-success mass has the extra factor q for crossing bonds. -/
theorem bad_success_mass (p : m.Bit → Set.Icc (0 : ℝ) 1) (q : Set.Icc (0 : ℝ) 1)
    (C : Box) (r : ℕ) (hw : ∀ i, C.lower i+r ≤ C.upper i-r)
    {y : Vertex} (hy : C.Exterior y)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q)
    (F : Set m.Config) (hF : ProductCylinder.DeterminedBy (F := Prop) (C.bits m) (fun ω => ω ∈ F))
    {γ τ : ℝ} (hqual : (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩ F) ≤ (q : ℝ)^Box.seedCard m r*γ/τ) :
    (ProductCylinder.law p).real (allValue (C.successBits r m y) true ∩ F) ≤
      (q : ℝ)^Box.successCard m r*γ/τ := by
  cases m
  · have hseed := ProductCylinder.determinedBy_mono (Box.bits_mono .bond (C.seedBox_contained r hw y))
      (allValue_determined ((C.seedBox r y).bits .bond) true)
    have hd : ProductCylinder.DeterminedBy (F := Prop) C.bonds
        (fun ω => ω ∈ allValue (C.seedBox r y).bonds true ∩ F) := by
      intro ω ω' h
      change (ω' ∈ allValue ((C.seedBox r y).bits .bond) true ∧ ω' ∈ F) =
        (ω ∈ allValue ((C.seedBox r y).bits .bond) true ∧ ω ∈ F)
      exact congrArg₂ And (hseed ω ω' h) (hF ω ω' h)
    have hind := indepSet_determined p {C.entryBit .bond y} C.bonds
      (Finset.disjoint_singleton_left.mpr (C.crossing_not_internal hy))
      (allValue {C.entryBit .bond y} true) (allValue (C.seedBox r y).bonds true ∩ F)
      (allValue_determined _ _) hd
    have he : allValue (C.successBits r .bond y) true ∩ F =
        allValue {C.entryBit .bond y} true ∩ (allValue (C.seedBox r y).bonds true ∩ F) := by
      ext ω
      simp only [Box.successBits,allValue,Set.mem_inter_iff,Set.mem_ofPred_eq,
        Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
      tauto
    have hcross := hp (C.entryBit .bond y)
      (C.successBits_contained r .bond hw hy (Finset.mem_insert_self _ _))
    have hpone : (ProductCylinder.law p).real (allValue {C.entryBit .bond y} true) = (q : ℝ) := by
      rw [allValue_probability_constant p _ q (by intro e he; simpa only [Finset.mem_singleton.mp he] using hcross)]
      simp [bitProbability]
    rw [he,Measure.real_def,hind.measure_inter_eq_mul,ENNReal.toReal_mul]
    change (ProductCylinder.law p).real (allValue {C.entryBit .bond y} true)*_ ≤ _
    rw [hpone]
    calc
      _ ≤ (q : ℝ)*((q : ℝ)^Box.seedCard .bond r*γ/τ) := mul_le_mul_of_nonneg_left hqual q.2.1
      _ = _ := by simp only [Box.successCard,pow_succ]; ring
  · simpa only [Box.successBits,Box.bits,Box.successCard,Nat.add_zero] using hqual

end LatticeGraph
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.bad_success_mass := @_root_.OAI.CriticalZ3.LatticeGraph.bad_success_mass
