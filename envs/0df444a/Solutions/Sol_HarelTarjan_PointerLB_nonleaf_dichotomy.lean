-- Prove2me | solution 1 for HarelTarjan.PointerLB.nonleaf_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @walker
-- created : 2026-09-28T08:41:27.898498+00:00
-- url     : https://prove2.me/submissions/5b86af9e-08b4-47e9-a78e-71b5caf0dc57

import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine
import Theorems.Thm_HarelTarjan_PointerLB_answered_mem_acc

open HarelTarjan.PointerLB

variable {N : Type*}

/-- The longest common prefix of `s ++ [false] ++ x` and `s ++ [true] ++ y` is `s`: the two paths
first differ exactly at the turn after `s`. -/
lemma p2m_lcp_cons_false_true :
    ∀ (s x y : List Bool), lcp (s ++ [false] ++ x) (s ++ [true] ++ y) = s := by
  intro s
  induction s with
  | nil => intro x y; rfl
  | cons a s' ih =>
      intro x y
      exact (if_pos rfl).trans (congrArg (fun t => a :: t) (ih x y))

/-- **Theorem 1, p. 340, first paragraph.** A nonleaf `w` is accessible from every leaf below its
left child, or from every leaf below its right child: a single leaf `x` below `w`'s left child and a
single leaf `y` below `w`'s right child would have `nca x y = w`, and `answered_mem_acc` would put
`w` in `A_x ∪ A_y`. -/
theorem solution {N : Type*} {h k : ℕ} (ptr : N → Fin 2 → Option N)
    (rep : Vertex h → N) (hk : AnswersLeafQueriesIn ptr rep k)
    (w : Vertex h) (hw : w.1.length < h) :
    (∀ x : Vertex h, IsLeaf x → w.1 ++ [false] <+: x.1 → w ∈ A ptr rep k x) ∨
      (∀ y : Vertex h, IsLeaf y → w.1 ++ [true] <+: y.1 → w ∈ A ptr rep k y) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hP, hQ⟩ := hcon
  push Not at hP hQ
  obtain ⟨x, hxleaf, hxpfx, hxA⟩ := hP
  obtain ⟨y, hyleaf, hypfx, hyA⟩ := hQ
  -- their nearest common ancestor is `w`
  have hxyl : nca x y = w := by
    apply Subtype.ext
    show lcp x.1 y.1 = w.1
    obtain ⟨x', hx'⟩ := hxpfx
    obtain ⟨y', hy'⟩ := hypfx
    rw [← hx', ← hy', p2m_lcp_cons_false_true]
  -- the machine answers the query on the two leaves in `k` steps, so `w ∈ A_x ∪ A_y`
  have hmem : w ∈ A ptr rep k x ∨ w ∈ A ptr rep k y := by
    have h1 := hk x y hxleaf hyleaf
    rw [hxyl] at h1
    exact answered_mem_acc ptr (rep x) (rep y) (rep w) k h1
  rcases hmem with hx | hy
  · exact absurd hx hxA
  · exact absurd hy hyA
