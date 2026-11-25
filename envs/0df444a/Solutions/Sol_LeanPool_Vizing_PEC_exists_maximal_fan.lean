-- Prove2me | solution 1 for LeanPool.Vizing.PEC.exists_maximal_fan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:34:08.369848+00:00
-- url     : https://prove2.me/submissions/e6370d1e-5857-459b-9798-7db9011185d3

module
public import Definitions.Def_LeanPool_Vizing_Kempe
public import Definitions.Def_LeanPool_Vizing_Fan
public import Theorems.Thm_LeanPool_Vizing_PEC_IsFan_length_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
open LeanPool.Vizing.PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
omit [Fintype V] [DecidableEq V] [DecidableEq C]
namespace LeanPool.Vizing.PEC
theorem _root_.solution [Finite V] (c : PEC G C) {x y : V}
    (hadj : G.Adj x y) (hnone : c.col x y = none) :
    ∃ (n : ℕ) (f : ℕ → V), c.IsFan x y n f ∧
      ∀ (m : ℕ) (g : ℕ → V), c.IsFan x y m g → m ≤ n := by
  classical
  let : Fintype V := Fintype.ofFinite V
  set P : ℕ → Prop := fun n => ∃ g : ℕ → V, c.IsFan x y n g with hP
  have hP0 : P 0 := by
    refine ⟨fun _ => y, rfl, hnone, fun i _ => hadj, ?_, ?_⟩
    · intro i hi j hj _
      omega
    · intro i hi
      omega
  set N := Fintype.card V with hN
  have hspec : P (Nat.findGreatest P N) := Nat.findGreatest_spec (Nat.zero_le _) hP0
  refine ⟨Nat.findGreatest P N, hspec.choose, hspec.choose_spec, ?_⟩
  intro m g hg
  by_contra hcon
  push Not at hcon
  exact Nat.findGreatest_is_greatest hcon hg.length_le ⟨g, hg⟩
end LeanPool.Vizing.PEC
