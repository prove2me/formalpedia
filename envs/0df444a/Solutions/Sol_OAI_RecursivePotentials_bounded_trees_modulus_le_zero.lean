-- Prove2me | solution 1 for OAI.RecursivePotentials.bounded_trees_modulus_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:55:39.546134+00:00
-- url     : https://prove2.me/submissions/ddb91a21-98fd-4a1b-b73c-33b40d6060d7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean:L264-L317
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.bounded_trees_modulus_le_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Theorems.Thm_OAI_RecursivePotentials_EquivalentNorm_bounded_tree_step

-- ---- from OAI.Analysis.RecursivePotentials.EquivalentNorms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

lemma upper_pos : 0 < A.upper := A.lower_pos.trans_le A.lower_le_upper

end EquivalentNorm

theorem bounded_trees_modulus_le_zero {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬Module.Finite ℝ E) (A : EquivalentNorm E) (u : ℕ → List ℕ → E)
    {m M c : ℝ} (hm : 0 < m) (hM : 0 < M) (hc : 0 < c)
    (hu : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length ≤ h → m ≤ ‖u h s‖ ∧ ‖u h s‖ ≤ M)
    (hd : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      WeaklyNull (fun k => u h (s ++ [k]) - u h s))
    (hdc : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      ∀ k, c ≤ ‖u h (s ++ [k]) - u h s‖) :
    A.modulus (A.lower * c / (2 * A.upper * M)) ≤ 0 := by
  by_contra hnon
  have hpos := lt_of_not_ge hnon
  let γ := A.modulus (A.lower * c / (2 * A.upper * M)) / 2
  have hγ : 0 < γ := half_pos hpos
  have hγmod : γ < A.modulus (A.lower * c / (2 * A.upper * M)) := half_lt_self hpos
  let δ := γ * (A.lower * m) / 2
  have hδ : 0 < δ := by dsimp [δ]; have := A.lower_pos; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (A.upper * M / δ)
  let h := n + 1
  have hh : 1 ≤ h := by omega
  have hgrow : ∀ j : ℕ, j ≤ h → ∃ s : List ℕ, s.length = j ∧
      (j : ℝ) * δ + A.lower * m ≤ A.N (u h s) := by
    intro j hj
    induction j with
    | zero =>
        refine ⟨[], rfl, ?_⟩
        have hl := A.lower_bound (u h [])
        have hm' := mul_le_mul_of_nonneg_left (hu h hh [] (by simp)).1 A.lower_pos.le
        simpa using hm'.trans hl
    | succ j ih =>
        obtain ⟨s, hs, hsn⟩ := ih (by omega)
        have hsh : s.length < h := by omega
        have hs0 : u h s ≠ 0 := by
          intro he
          have hl := (hu h hh s hsh.le).1
          rw [he, norm_zero] at hl
          linarith
        obtain ⟨k, hk⟩ := A.bounded_tree_step hE hs0 (fun k => u h (s ++ [k]) - u h s)
          (hd h hh s hsh) hM hc (hu h hh s hsh.le).2 (hdc h hh s hsh) hγ hγmod
        have hl : A.lower * m ≤ A.N (u h s) :=
          (mul_le_mul_of_nonneg_left (hu h hh s hsh.le).1 A.lower_pos.le).trans (A.lower_bound _)
        have he : u h s + (u h (s ++ [k]) - u h s) = u h (s ++ [k]) := by abel
        rw [he] at hk
        refine ⟨s ++ [k], by simp [hs], ?_⟩
        push_cast
        dsimp [δ] at hsn ⊢
        nlinarith
  obtain ⟨s, hs, hsn⟩ := hgrow h le_rfl
  have huM := (A.upper_bound (u h s)).trans
    (mul_le_mul_of_nonneg_left (hu h hh s hs.le).2 A.upper_pos.le)
  have hn' : A.upper * M < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  have hhcast : (h : ℝ) = (n : ℝ) + 1 := by simp [h]
  rw [hhcast] at hsn
  have hm' := mul_pos A.lower_pos hm
  nlinarith

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end TreeSpace

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end TreeSpace

namespace ZeroTreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end ZeroTreeSpace

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

end EquivalentNorm

end RecursivePotentials

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials
open scoped BigOperators
open Filter Topology


theorem solution.{uSpace} : type_of% @_root_.OAI.RecursivePotentials.bounded_trees_modulus_le_zero.{uSpace} := @_root_.OAI.RecursivePotentials.bounded_trees_modulus_le_zero.{uSpace}
