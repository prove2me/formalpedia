-- Prove2me | solution 1 for OAI.Saxl.finset_eq_of_signed_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:02:26.263006+00:00
-- url     : https://prove2.me/submissions/60cc2299-5a0c-46c2-b207-82797586f2d2

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid

open OAI OAI.Saxl
open scoped TensorProduct
universe uX


theorem solution {X : Type uX} [DecidableEq X]
    (A B : Finset X) (w : X → ℤ)
    (hp : ∀ x ∈ B, 0 < w x) (hn : ∀ x ∉ B, w x < 0)
    (he : ∑ x ∈ A, w x = ∑ x ∈ B, w x) : A = B := by
  have h1 := Finset.sum_sdiff (s₁ := A ∩ B) (s₂ := A) (f := w) Finset.inter_subset_left
  have h2 := Finset.sum_sdiff (s₁ := A ∩ B) (s₂ := B) (f := w) Finset.inter_subset_right
  have e1 : A \ (A ∩ B) = A \ B := by ext x; simp
  have e2 : B \ (A ∩ B) = B \ A := by ext x; simp [and_comm]
  rw [e1] at h1; rw [e2] at h2
  have hAB : ∑ x ∈ A \ B, w x = ∑ x ∈ B \ A, w x := by omega
  have hle : ∑ x ∈ A \ B, w x ≤ 0 := Finset.sum_nonpos (fun x hx => by
    have := hn x (Finset.mem_sdiff.1 hx).2; omega)
  have hge : 0 ≤ ∑ x ∈ B \ A, w x := Finset.sum_nonneg (fun x hx => by
    have := hp x (Finset.mem_sdiff.1 hx).1; omega)
  have d1 : A \ B = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have : ∑ x ∈ A \ B, w x < 0 := Finset.sum_neg (fun x hx => hn x (Finset.mem_sdiff.1 hx).2) ⟨y, hy⟩
    omega
  have d2 : B \ A = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have : 0 < ∑ x ∈ B \ A, w x := Finset.sum_pos (fun x hx => hp x (Finset.mem_sdiff.1 hx).1) ⟨y, hy⟩
    omega
  rw [Finset.sdiff_eq_empty_iff_subset] at d1 d2
  exact Finset.Subset.antisymm d1 d2

