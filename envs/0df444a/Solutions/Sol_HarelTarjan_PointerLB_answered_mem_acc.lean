-- Prove2me | solution 1 for HarelTarjan.PointerLB.answered_mem_acc
-- status  : ACCEPTED   (prove)
-- author  : @walker
-- created : 2026-09-28T08:19:23.236233+00:00
-- url     : https://prove2.me/submissions/201aae87-004c-43fd-8719-aa7bf83bad37

import Mathlib
import Definitions.Def_HarelTarjan_PointerLB_BinaryTree
import Definitions.Def_HarelTarjan_PointerLB_PointerMachine

open HarelTarjan.PointerLB

variable {N : Type*}

/-- `acc` grows with the number of steps. -/
lemma p2m_acc_subset_succ (ptr : N → Fin 2 → Option N) (a : N) (j : ℕ) :
    acc ptr j a ⊆ acc ptr (j + 1) a := by
  intro x hx
  exact Or.inl hx

/-- `acc ptr i a ⊆ acc ptr j a` whenever `i ≤ j`. -/
lemma p2m_acc_mono (ptr : N → Fin 2 → Option N) (a : N) {i j : ℕ} (h : i ≤ j) :
    acc ptr i a ⊆ acc ptr j a := by
  induction h with
  | refl => intro x hx; exact hx
  | step _ ih => intro x hx; exact p2m_acc_subset_succ ptr a _ (ih hx)

/-- **Theorem 1, p. 340, first paragraph.** If a run of at most `k` steps from the input nodes `a`
and `b` holds a pointer to `target`, then `target`'s node is accessible from `a` or from `b` in `k`
steps or less. -/
theorem solution {N : Type*} (ptr : N → Fin 2 → Option N) (a b target : N) (k : ℕ)
    (hans : AnsweredIn ptr a b target k) :
    target ∈ acc ptr k a ∪ acc ptr k b := by
  obtain ⟨t, htk, held, hrun, hmem⟩ := hans
  have key : ∀ (t : ℕ) (held : List N), Run ptr a b t held →
      ∀ x ∈ held, x ∈ acc ptr t a ∪ acc ptr t b := by
    intro t held hrun
    induction hrun with
    | start =>
        intro x hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with hxa | hxb
        · rw [hxa]; exact Or.inl (by simp [acc])
        · rw [hxb]; exact Or.inr (by simp [acc])
    | step i _ hmm hptr ih =>
        intro x hx
        rcases List.mem_cons.mp hx with hxn | hx'
        · rw [hxn]
          rcases ih _ hmm with hm' | hm'
          · exact Or.inl (Or.inr ⟨_, hm', i, hptr⟩)
          · exact Or.inr (Or.inr ⟨_, hm', i, hptr⟩)
        · rcases ih _ hx' with hx'' | hx''
          · exact Or.inl (p2m_acc_subset_succ ptr a _ hx'')
          · exact Or.inr (p2m_acc_subset_succ ptr b _ hx'')
  rcases key t held hrun target hmem with h | h
  · exact Or.inl (p2m_acc_mono ptr a htk h)
  · exact Or.inr (p2m_acc_mono ptr b htk h)
