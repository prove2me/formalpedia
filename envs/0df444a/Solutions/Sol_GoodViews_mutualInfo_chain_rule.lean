-- Prove2me | solution 1 for GoodViews.mutualInfo_chain_rule
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T11:37:02.325266+00:00
-- url     : https://prove2.me/submissions/da8a0f68-79b1-4155-9eaa-fa792b1fa549

import Mathlib
import Definitions.Def_GoodViews_Basic
set_option autoImplicit false
open Finset
namespace GoodViews

lemma entropy_equiv {S α β : Type} [Fintype S] [Fintype α] [Fintype β] (P : S → ℝ)
    (A : S → α) (e : α ≃ β) : entropy P (fun ω => e (A ω)) = entropy P A := by
  unfold entropy
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  unfold law
  congr 1
  ext ω; simp

theorem mutualInfo_chain_rule {S α β γ : Type} [Fintype S] [Fintype α] [Fintype β]
    [Fintype γ] (P : S → ℝ) (hP : IsPMF P) (A : S → α) (B : S → β) (C : S → γ) :
    mutualInfo P A (fun ω => (B ω, C ω)) = mutualInfo P A B + condMutualInfo P A C B := by
  have h1 : entropy P (fun ω => (C ω, B ω)) = entropy P (fun ω => (B ω, C ω)) :=
    entropy_equiv P (fun ω => (B ω, C ω)) (Equiv.prodComm β γ)
  have h2 : entropy P (fun ω => (A ω, C ω, B ω)) = entropy P (fun ω => (A ω, B ω, C ω)) :=
    entropy_equiv P (fun ω => (A ω, B ω, C ω)) ((Equiv.refl α).prodCongr (Equiv.prodComm β γ))
  unfold mutualInfo condMutualInfo
  rw [h1, h2]; ring

end GoodViews
open GoodViews in
theorem solution {S α β γ : Type} [Fintype S] [Fintype α] [Fintype β]
    [Fintype γ] (P : S → ℝ) (hP : IsPMF P) (A : S → α) (B : S → β) (C : S → γ) :
    mutualInfo P A (fun ω => (B ω, C ω)) = mutualInfo P A B + condMutualInfo P A C B :=
  mutualInfo_chain_rule P hP A B C
