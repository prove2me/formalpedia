-- Prove2me | solution 1 for OAI.FiniteCircle.finite_partition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:49:21.247967+00:00
-- url     : https://prove2.me/submissions/3969959c-5bbf-49b9-aadb-b03fbc59181c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Partitions.lean:L154-L183
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.finite_partition. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions

-- ---- from OAI.Combinatorics.FiniteCircle.Partitions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

end FiniteLaw

theorem selectionWeight_nonneg {I : Type*} [Fintype I] (q : I → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (s : I → Bool) : 0 ≤ selectionWeight q s := by
  apply Finset.prod_nonneg
  intro i _
  split
  · exact sub_nonneg.mpr (hq i).2
  · exact (hq i).1

theorem selectionWeight_total {I : Type*} [Fintype I] [DecidableEq I] (q : I → ℝ) :
    ∑ s : I → Bool, selectionWeight q s = 1 := by
  unfold selectionWeight
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b then 1 - q i else q i)]
  simp

theorem selection_collision {I X : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (c : I → X → Bool) (x y : X) :
    (∑ s : I → Bool, if selectionLabel c s x = selectionLabel c s y then selectionWeight q s else 0) =
      ∏ i, if c i x = c i y then 1 else q i := by
  classical
  have hterm (s : I → Bool) :
      (if selectionLabel c s x = selectionLabel c s y then selectionWeight q s else 0) =
      ∏ i, if (s i && c i x) = (s i && c i y) then
        (if s i then 1 - q i else q i) else 0 := by
    rw [Fintype.prod_ite_zero]
    simp only [selectionLabel, selectionWeight, funext_iff]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    if (b && c i x) = (b && c i y) then (if b then 1 - q i else q i) else 0)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool]
  cases hcx : c i x <;> cases hcy : c i y <;> simp

theorem finite_partition {X : Type*} [Fintype X] {ρ : X → X → ℝ}
    (hρ : HasCutRepresentation ρ) (α : ℝ) (hα : 0 ≤ α) : by
  classical
  exact ∃ (μ : FiniteLaw (PartitionSpace X)) (label : PartitionSpace X → X → PartitionSpace X),
      ∀ x y, μ.event (fun ω => label ω x = label ω y) = Real.exp (-α * ρ x y) := by
  classical
  obtain ⟨a, ha, hrep⟩ := hρ
  let q : (X → Bool) → ℝ := fun c => Real.exp (-α * a c)
  have hq (c : X → Bool) : 0 ≤ q c ∧ q c ≤ 1 := by
    constructor
    · exact (Real.exp_pos _).le
    · apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) (ha c)
  let μ : FiniteLaw (PartitionSpace X) :=
    ⟨selectionWeight q, selectionWeight_nonneg q hq, selectionWeight_total q⟩
  refine ⟨μ, selectionLabel (fun c => c), ?_⟩
  intro x y
  dsimp only [FiniteLaw.event, μ]
  trans ∏ c : X → Bool, if c x = c y then (1 : ℝ) else q c
  · convert selection_collision q (fun c : X → Bool => c) x y using 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : selectionLabel (fun c : X → Bool => c) ω x = selectionLabel (fun c => c) ω y <;> simp [h]
  have he (c : X → Bool) : (if c x = c y then (1 : ℝ) else q c) =
      Real.exp (-α * (a c * cutDistance c x y)) := by
    by_cases h : c x = c y <;> simp [h, cutDistance, q]
  simp_rw [he]
  rw [← Real.exp_sum, ← Finset.mul_sum]
  congr 2
  exact (hrep x y).symm

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.finite_partition := @_root_.OAI.FiniteCircle.finite_partition
