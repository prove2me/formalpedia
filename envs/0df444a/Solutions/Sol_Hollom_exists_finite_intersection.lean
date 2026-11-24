-- Prove2me | solution 1 for Hollom.exists_finite_intersection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:12:14.433943+00:00
-- url     : https://prove2.me/submissions/9304c80a-8a89-4947-a8b1-3b8b9ca2e87a

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CompleteLattice
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_AharoniKorman_ForMathlib_Misc
import Definitions.Def_AharoniKorman_Counterexample
section
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
namespace Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
private lemma triangle_finite (n : ℕ) : {x : ℕ × ℕ | x.1 + x.2 ≤ n}.Finite :=
  (Set.finite_Iic (n, n)).subset <| by rintro ⟨a, b⟩ h; simp at h ⊢; omega
variable {C : Set Hollom}
open Filter
section SpinalMap
variable {α : Type*} [PartialOrder α] {C : Set α}
namespace SpinalMap
variable (f : SpinalMap C)
variable {x y z : α}
end SpinalMap
end SpinalMap
variable {f : SpinalMap C}
section make_chains
open Finset
end make_chains
variable {n : ℕ}
end Hollom
example : PartialOrder Hollom := inferInstance
example : Countable Hollom := inferInstance
example (A : Set Hollom) (hA : IsAntichain (· ≤ ·) A) : A.Finite := Hollom.no_infinite_antichain hA
example {f : ℚ → Hollom} : ¬ StrictMono f := Hollom.scattered
end

set_option autoImplicit true
attribute [local aesop 2 simp] Set.subset_def Finset.subset_iff
open Hollom
local notation3 "h(" x ", " y ", " z ")" => toHollom (x, y, z)
variable {C : Set Hollom}
open Filter
namespace Hollom
theorem _root_.solution (hC : IsChain (· ≤ ·) C) :
    ∃ᶠ n in atTop, (C ∩ level n).Finite := by
  -- Begin by assuming `C ∩ level n` is infinite for all `n ≥ n₀`
  rw [frequently_atTop]
  intro n₀
  by_contra! hC'
  -- Define `m n` to be the smallest value of `min x y` as `(x, y, n)` ranges over `C`.
  let m (n : ℕ) : ℕ := sInf {min (ofHollom x).1 (ofHollom x).2.1 | x ∈ C ∩ level n}
  -- `m n` is well-defined above `n₀`, since the set in question is nonempty (it's infinite).
  have nonempty_mins (n : ℕ) (hn : n₀ ≤ n) :
      {min (ofHollom x).1 (ofHollom x).2.1 | x ∈ C ∩ level n}.Nonempty :=
    (hC' n hn).nonempty.image _
  -- We aim to show that `m n` is strictly decreasing above `n₀`, which is clearly a contradiction.
  suffices ∀ n ≥ n₀, m (n + 1) < m n from no_strictly_decreasing _ this
  intro n hn
  -- Take `n ≥ n₀`, and take `u, v` such that `min u v = m n` (which exists by definition).
  -- We aim to show `m (n + 1) < min u v`
  obtain ⟨u, v, huv, hmn⟩ : ∃ u v : ℕ, h(u, v, n) ∈ C ∧ min u v = m n := by
    simpa [m] using Nat.sInf_mem (nonempty_mins n hn)
  rw [← hmn]
  -- Consider the set of points `{(x, y, z) | x + y ≤ 2 * (u + v)}`.
  let D : Set Hollom := {x | (ofHollom x).1 + (ofHollom x).2.1 ≤ 2 * (u + v)}
  -- There are infinitely many points in `C ∩ level (n + 1)` that are not in `D`...
  have : ((C ∩ level (n + 1)) \ D).Infinite := by
    -- ...because there are finitely many points in `C ∩ level (n + 1) ∩ D`...
    have : (C ∩ level (n + 1) ∩ D).Finite := by
      -- (indeed, `level (n + 1) ∩ D` is finite)
      refine .subset (.image (embed (n + 1)) (triangle_finite (2 * (u + v)))) ?_
      simp +contextual [Set.subset_def, D, embed_apply]
    -- ...and `C ∩ level (n + 1)` is infinite (by assumption).
    specialize hC' (n + 1) (by omega)
    rw [← (C ∩ level (n + 1)).inter_union_diff D, Set.infinite_union] at hC'
    refine hC'.resolve_left ?_
    simpa using this
  -- In fact, we only need it to be nonempty, and find a point.
  obtain ⟨x, hxy⟩ := this.nonempty
  induction hxy.1.2 using induction_on_level with | h x y =>
  simp only [Set.mem_diff, Set.mem_inter_iff, toHollom_mem_level_iff, and_true, Set.mem_setOf_eq,
    ofHollom_toHollom, not_le, D, m] at hxy
  -- Take the point `(x, y, n + 1)` in `C` that avoids `D`. As `(u, v, n)` is also in the chain `C`,
  -- they must be comparable.
  obtain h3 | h3 := hC.total huv hxy.1
  -- We cannot have `(u, v, n) ≤ (x, y, n + 1)` by definition of the order.
  · simpa using le_of_toHollom_le_toHollom h3
  -- Whereas if `(x, y, n + 1) ≤ (u, v, n)`, as `2 * (u + v) < x + y`, we must have
  -- `min x y + 1 ≤ min u v`, which finishes the proof.
  · cases h3
    case twice => omega
    case next_add => omega
    case next_min h3 =>
      rw [← Nat.add_one_le_iff]
      refine h3.trans' ?_
      simp only [add_le_add_iff_right]
      exact Nat.sInf_le ⟨_, ⟨hxy.1, by simp⟩, by simp⟩
end Hollom
