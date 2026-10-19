-- Prove2me | solution 2 for OAI.InfiniteConditioning.disjoint_blocks_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:36:20.72009+00:00
-- url     : https://prove2.me/submissions/87cacaa8-cb64-4d88-aebe-8641ec3222d4

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Conditioning.lean:L228-L259
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteConditioning.disjoint_blocks_probability. The node keeps its source
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

theorem disjoint_blocks_probability (p : E → Set.Icc (0 : ℝ) 1)
    (J : I → Finset E) (hJ : Pairwise (fun i j => Disjoint (J i) (J j)))
    (A : I → Set (E → Bool))
    (hA : ∀ i, ProductCylinder.DeterminedBy (F := Prop) (J i) (fun ω => ω ∈ A i))
    (s : Finset I) :
    (ProductCylinder.law p).real {ω | ∀ i ∈ s, ω ∈ A i} =
      ∏ i ∈ s, (ProductCylinder.law p).real (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty,false_implies,implies_true,Set.ofPred_true,
      probReal_univ,Finset.prod_empty]
  | @insert i s hi ih =>
    have hdis : Disjoint (J i) (s.biUnion J) := by
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨j,hj,hej⟩ := Finset.mem_biUnion.mp he'
      exact Finset.disjoint_left.mp (hJ (ne_of_mem_of_not_mem hj hi).symm) he hej
    have hdet : ProductCylinder.DeterminedBy (F := Prop) (s.biUnion J)
        (fun ω => ∀ j ∈ s, ω ∈ A j) := by
      intro ω ω' h
      apply propext
      constructor <;> intro hh j hj
      · exact (eq_iff_iff.mp (hA j ω ω' (fun e he => h e (Finset.mem_biUnion.mpr ⟨j,hj,he⟩)))).mp (hh j hj)
      · exact (eq_iff_iff.mp (hA j ω ω' (fun e he => h e (Finset.mem_biUnion.mpr ⟨j,hj,he⟩)))).mpr (hh j hj)
    have hh := (indepSet_determined p (J i) (s.biUnion J) hdis (A i)
      {ω | ∀ j ∈ s, ω ∈ A j} (hA i) hdet).measure_inter_eq_mul
    have heq : {ω | ∀ j ∈ insert i s, ω ∈ A j} = A i ∩ {ω | ∀ j ∈ s, ω ∈ A j} := by
      ext ω; simp only [Finset.mem_insert,forall_eq_or_imp,Set.mem_ofPred_eq,Set.mem_inter_iff]
    rw [heq,Measure.real_def,hh,ENNReal.toReal_mul]
    change (ProductCylinder.law p).real (A i) *
      (ProductCylinder.law p).real {ω | ∀ j ∈ s, ω ∈ A j} = _
    rw [ih,Finset.prod_insert hi]

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

variable [Countable E]

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

end InfiniteConditioning

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical


theorem solution : type_of% @_root_.OAI.InfiniteConditioning.disjoint_blocks_probability := @_root_.OAI.InfiniteConditioning.disjoint_blocks_probability
