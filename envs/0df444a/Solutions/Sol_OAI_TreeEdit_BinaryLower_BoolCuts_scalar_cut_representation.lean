-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.BoolCuts.scalar_cut_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:26:10.918776+00:00
-- url     : https://prove2.me/submissions/3ac696a1-cd2e-4eb4-b9be-7f6dc625b54e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/ScalarCutsBool.lean:L114-L165
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.BoolCuts.scalar_cut_representation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Theorems.Thm_OAI_TreeEdit_BinaryLower_BoolCuts_group_cuts

-- ---- from OAI.Combinatorics.BinaryEdit.ScalarCutsBool ----
namespace OAI

/-! Scalar finite cut decomposition used by the finite-group obstruction.
This is the one-real-coordinate part of `lem:cuts` in preliminaries.tex. -/

namespace TreeEdit.BinaryLower.BoolCuts

open scoped BigOperators

lemma step_mono (k : ℕ) : Monotone (step k) := by
  intro i j hij
  unfold step
  split_ifs with hi hj hj
  · exact le_refl _
  · omega
  · norm_num
  · exact le_refl _

lemma step_abs_sub {i j : ℕ} (hij : i ≤ j) (k : ℕ) :
    |step k i - step k j| = step k j - step k i := by
  rw [abs_of_nonpos (sub_nonpos.mpr (step_mono k hij))]
  ring

lemma sum_gap_step (g : ℕ → ℝ) {n i : ℕ} (hi : i ≤ n) :
    ∑ k ∈ Finset.range n, (g (k + 1) - g k) * step k i = g i - g 0 := by
  calc
    _ = ∑ k ∈ Finset.range i, (g (k + 1) - g k) * step k i := by
      symm
      apply Finset.sum_subset (Finset.range_mono hi)
      intro k hk hki
      have : ¬ k < i := by simpa using hki
      simp [step, this]
    _ = ∑ k ∈ Finset.range i, (g (k + 1) - g k) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [step, Finset.mem_range.mp hk]
    _ = _ := Finset.sum_range_sub g i

lemma gap_cut_identity_of_le (g : ℕ → ℝ) (hg : Monotone g)
    {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (hij : i ≤ j) :
    |g i - g j| = ∑ k ∈ Finset.range n,
      (g (k + 1) - g k) * |step k i - step k j| := by
  simp_rw [step_abs_sub hij, mul_sub]
  rw [Finset.sum_sub_distrib, sum_gap_step g hj, sum_gap_step g hi,
    abs_of_nonpos (sub_nonpos.mpr (hg hij))]
  ring

lemma gap_cut_identity (g : ℕ → ℝ) (hg : Monotone g)
    {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    |g i - g j| = ∑ k ∈ Finset.range n,
      (g (k + 1) - g k) * |step k i - step k j| := by
  rcases le_total i j with hij | hji
  · exact gap_cut_identity_of_le g hg hi hj hij
  · simpa only [abs_sub_comm] using gap_cut_identity_of_le g hg hj hi hji

/-- Every real-valued function on a finite set is a nonnegative combination
of cut metrics. The two constant cuts receive zero weight. -/
theorem scalar_cut_representation {S : Type*} [Fintype S] [DecidableEq S]
    (f : S → ℝ) :
    ∃ a : (S → Bool) → ℝ,
      (∀ C, 0 ≤ a C) ∧
      (∀ x y, |f x - f y| = ∑ C, a C * cutDistance C x y) ∧
      a (fun _ => false) = 0 ∧ a (fun _ => true) = 0 := by
  classical
  cases isEmpty_or_nonempty S with
  | inl hS =>
    let := hS
    refine ⟨fun _ => 0, by simp, ?_, rfl, rfl⟩
    intro x
    exact isEmptyElim x
  | inr hS =>
    let := hS
    let s : Finset ℝ := Finset.univ.image f
    have hmem (x : S) : f x ∈ s := by simp [s]
    have hc : 0 < s.card := Finset.card_pos.mpr
      ⟨f (Classical.choice hS), hmem _⟩
    let e : Fin s.card ≃o s := s.orderIsoOfFin rfl
    let ix : S → Fin s.card := fun x => e.symm ⟨f x, hmem x⟩
    have hlast : s.card - 1 < s.card := Nat.sub_lt hc (by omega)
    let g : ℕ → ℝ := fun k =>
      (e ⟨min k (s.card - 1), lt_of_le_of_lt (min_le_right _ _) hlast⟩).val
    have hg : Monotone g := by
      intro i j hij
      exact e.monotone (show (⟨min i (s.card - 1),
        lt_of_le_of_lt (min_le_right _ _) hlast⟩ : Fin s.card) ≤
          ⟨min j (s.card - 1), lt_of_le_of_lt (min_le_right _ _) hlast⟩ from
        min_le_min_right _ hij)
    have hgi (x : S) : g (ix x).val = f x := by
      dsimp [g]
      have hmin : min (ix x).val (s.card - 1) = (ix x).val :=
        min_eq_left (Nat.le_sub_one_of_lt (ix x).isLt)
      simp only [hmin]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨f x, hmem x⟩)
    let C : Fin s.card → S → Bool := fun k x => decide (k.val < (ix x).val)
    let w : Fin s.card → ℝ := fun k => g (k.val + 1) - g k.val
    have hw (k : Fin s.card) : 0 ≤ w k := sub_nonneg.mpr (hg (Nat.le_succ _))
    obtain ⟨a, ha, hrep, hfalse, htrue⟩ := group_cuts C w hw
    refine ⟨a, ha, ?_, hfalse, htrue⟩
    intro x y
    rw [← hrep x y, ← hgi x, ← hgi y]
    have hid := gap_cut_identity g hg (n := s.card)
      (Nat.le_of_lt (ix x).isLt) (Nat.le_of_lt (ix y).isLt)
    convert hid using 1
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp [w, C, cutDistance, bit, step]

end TreeEdit.BinaryLower.BoolCuts

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.BoolCuts
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.BoolCuts.scalar_cut_representation := @_root_.OAI.TreeEdit.BinaryLower.BoolCuts.scalar_cut_representation
