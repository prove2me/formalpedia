-- Prove2me | solution 1 for OAI.RecursivePotentials.averagedModulus_lower_of_witness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:35:04.114309+00:00
-- url     : https://prove2.me/submissions/61fefc4d-184e-4005-ab84-5c4408e78d71

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean:L1225-L1249
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.averagedModulus_lower_of_witness. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry

-- ---- from OAI.Analysis.RecursivePotentials.TreeGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

namespace FiniteRootedTree

section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace CofiniteSubspace

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma nontrivial_space (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) :
    Nontrivial F.space := by
  by_contra hn
  have : Subsingleton F.space := not_nontrivial_iff_subsingleton.mp hn
  let := F.finiteQuotient
  exact hE (Module.Finite.of_submodule_quotient F.space)

lemma exists_unit (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) :
    ∃ y ∈ F.space, ‖y‖ = 1 := by
  have := F.nontrivial_space hE
  obtain ⟨y, hy⟩ := exists_norm_eq F.space (by norm_num : (0 : ℝ) ≤ 1)
  exact ⟨y, y.2, hy⟩

end CofiniteSubspace

section Moduli

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma averagedGain_lower (x : E) (t : ℝ) (y : E) : ‖x‖ - 1 ≤ averagedGain x t y := by
  have he : x + t • y + (x - t • y) = (2 : ℝ) • x := by module
  have h := norm_add_le (x + t • y) (x - t • y)
  rw [he, norm_smul, Real.norm_eq_abs] at h
  norm_num at h
  unfold averagedGain
  linarith

lemma averagedInner_bddBelow (x : E) (t : ℝ) (F : CofiniteSubspace E) :
    BddBelow {r : ℝ | ∃ y ∈ F.space, 1 ≤ ‖y‖ ∧ r = averagedGain x t y} := by
  refine ⟨‖x‖ - 1, ?_⟩
  rintro r ⟨y, hy, hy1, rfl⟩
  exact averagedGain_lower x t y

lemma averagedInner_nonempty (x : E) (t : ℝ) (F : CofiniteSubspace E)
    (hE : ¬Module.Finite ℝ E) :
    {r : ℝ | ∃ y ∈ F.space, 1 ≤ ‖y‖ ∧ r = averagedGain x t y}.Nonempty := by
  obtain ⟨y, hy, hy1⟩ := F.exists_unit hE
  exact ⟨_, y, hy, hy1.ge, rfl⟩

lemma averagedInner_le (x : E) (hx : ‖x‖ = 1) (t : ℝ) (ht : 0 ≤ t)
    (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) : averagedInner x t F ≤ t := by
  obtain ⟨y, hy, hy1⟩ := F.exists_unit hE
  have hle : averagedInner x t F ≤ averagedGain x t y :=
    csInf_le (averagedInner_bddBelow x t F) ⟨y, hy, hy1.ge, rfl⟩
  have h₁ := norm_add_le x (t • y)
  have h₂ := norm_sub_le x (t • y)
  have hnorm : ‖t • y‖ = t := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hy1, mul_one]
  rw [hx, hnorm] at h₁ h₂
  unfold averagedGain at hle
  linarith

theorem averagedModulus_lower_of_witness (hE : ¬Module.Finite ℝ E)
    {t c : ℝ} (ht : 0 ≤ t)
    (hw : ∀ x : E, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ F : CofiniteSubspace E, ∀ y ∈ F.space, 1 ≤ ‖y‖ → c - ε ≤ averagedGain x t y) :
    c ≤ averagedModulus E t := by
  have hunit : ∃ x : E, ‖x‖ = 1 := by
    obtain ⟨x, hx, hx1⟩ := (CofiniteSubspace.top : CofiniteSubspace E).exists_unit hE
    exact ⟨x, hx1⟩
  apply le_csInf
  · obtain ⟨x, hx⟩ := hunit
    exact ⟨_, x, hx, rfl⟩
  · rintro r ⟨x, hx, rfl⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨F, hF⟩ := hw x hx ε hε
    have hinner : c - ε ≤ averagedInner x t F := by
      apply le_csInf (averagedInner_nonempty x t F hE)
      rintro r ⟨y, hy, hy1, rfl⟩
      exact hF y hy hy1
    have hbounded : BddAbove (Set.range (averagedInner x t)) := by
      refine ⟨t, ?_⟩
      rintro r ⟨G, rfl⟩
      exact averagedInner_le x hx t ht G hE
    have hsup := le_csSup hbounded (Set.mem_range_self F)
    linarith

end Moduli

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials
open scoped BigOperators


theorem solution.{uSpace} : type_of% @_root_.OAI.RecursivePotentials.averagedModulus_lower_of_witness.{uSpace} := @_root_.OAI.RecursivePotentials.averagedModulus_lower_of_witness.{uSpace}
