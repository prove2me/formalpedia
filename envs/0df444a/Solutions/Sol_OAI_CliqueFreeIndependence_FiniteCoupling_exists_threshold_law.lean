-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteCoupling.exists_threshold_law
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:35:31.961981+00:00
-- url     : https://prove2.me/submissions/d13947dc-fa56-4bca-89d1-8032872f6b0f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteCoupling.lean:L76-L128
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteCoupling.exists_threshold_law. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling

-- ---- from OAI.Combinatorics.CliqueFree.FiniteCoupling ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteCoupling
universe z
variable {I : Type u} {J : Type v} {E : Type z}
variable [Fintype I] [Fintype J] [Fintype E]
attribute [local instance] OAI.CliqueFreeIndependence.FiniteCoupling.instDecidableEq_oAI_2
open MeasureTheory in
lemma exists_threshold_law (a : I → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    ∃ q : Finset I → ℝ, Law q ∧
      (∀ i, (∑ A, if i ∈ A then q A else 0) = a i) ∧
      (∀ i j, (∑ A, if i ∈ A ∧ j ∈ A then q A else 0) = min (a i) (a j)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 1)
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp [μ, Real.volume_Icc]
  let f : ℝ → Finset I := fun t ↦ univ.filter (fun i ↦ t ≤ a i)
  have hf : ∀ A, MeasurableSet (f ⁻¹' {A}) := by
    intro A
    have heq : f ⁻¹' {A} = ⋂ i, {t : ℝ | (t ≤ a i ↔ i ∈ A)} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.ext_iff,
        f, mem_filter, mem_univ, true_and, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ A
    · simpa only [hi, iff_true, Set.Iic] using (measurableSet_Iic : MeasurableSet (Set.Iic (a i)))
    · simpa only [hi, iff_false, not_le, Set.Ioi] using (measurableSet_Ioi : MeasurableSet (Set.Ioi (a i)))
  let q : Finset I → ℝ := fun A ↦ μ.real (f ⁻¹' {A})
  have hevent (b : Finset I → Prop) [DecidablePred b] :
      (∑ A, if b A then q A else 0) = μ.real {t | b (f t)} := by
    rw [← sum_filter]
    have h := sum_measureReal_preimage_singleton (μ := μ) (univ.filter b) (fun A _ ↦ hf A)
    convert h using 1; simp
  have hmass (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
      μ.real {t | t ≤ c} = c := by
    change (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iic c) = c
    rw [measureReal_restrict_apply measurableSet_Iic]
    have heq : Set.Iic c ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 c := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨ht, h0, _⟩; exact ⟨h0, ht⟩
      · rintro ⟨h0, htc⟩; exact ⟨htc, h0, htc.trans hc1⟩
    change volume.real (Set.Iic c ∩ Set.Icc (0 : ℝ) 1) = _
    rw [heq, measureReal_def, Real.volume_Icc]
    simpa using ENNReal.toReal_ofReal hc0
  refine ⟨q, ⟨fun A ↦ measureReal_nonneg, ?_⟩, ?_, ?_⟩
  · have h := hevent (fun _ ↦ True)
    simpa [μ, measureReal_def, Real.volume_Icc] using h
  · intro i
    trans μ.real {t | i ∈ f t}
    · exact hevent (fun A ↦ i ∈ A)
    simpa only [f, mem_filter, mem_univ, true_and] using hmass (a i) (ha0 i) (ha1 i)
  · intro i j
    trans μ.real {t | i ∈ f t ∧ j ∈ f t}
    · exact hevent (fun A ↦ i ∈ A ∧ j ∈ A)
    simpa only [f, mem_filter, mem_univ, true_and, le_min_iff] using
      hmass (min (a i) (a j)) (le_min (ha0 i) (ha0 j)) ((min_le_left _ _).trans (ha1 i))

end FiniteCoupling

end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteCoupling
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance] OAI.CliqueFreeIndependence.FiniteCoupling.instDecidableEq_oAI_2


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteCoupling.exists_threshold_law.{u} := @_root_.OAI.CliqueFreeIndependence.FiniteCoupling.exists_threshold_law.{u}
