-- Prove2me | solution 1 for GeomDL.EGNN.conv_subset_att_subset_mp
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-22T03:42:13.120955+00:00
-- url     : https://prove2.me/submissions/c8f9ac95-67e9-4b02-a191-dac3d279aaaa

import Definitions.Def_GeomDL_EGNN_Defs

open GeomDL.EGNN

theorem solution {n : ℕ} {α M M' β : Type*} [SMul ℝ M]
    (φ : α → M' → β) (agg : Multiset M → M') (ψ : α → M) (X : Fin n → α)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ a : α → α → ℝ,
        attLayer φ agg a ψ X A = mpLayer φ agg (fun xu xv => a xu xv • ψ xv) X A) ∧
    (Function.Injective X → ∀ c : Matrix (Fin n) (Fin n) ℝ,
        ∃ a : α → α → ℝ, convLayer φ agg c ψ X A = attLayer φ agg a ψ X A) ∧
    (Function.Injective X → ∀ c : Matrix (Fin n) (Fin n) ℝ,
        ∃ ψ' : α → α → M, convLayer φ agg c ψ X A = mpLayer φ agg ψ' X A) := by
  classical
  have hatt (a : α → α → ℝ) :
      attLayer φ agg a ψ X A = mpLayer φ agg (fun xu xv => a xu xv • ψ xv) X A := rfl
  have hconv (hX : Function.Injective X) (c : Matrix (Fin n) (Fin n) ℝ) :
      ∃ a : α → α → ℝ, convLayer φ agg c ψ X A = attLayer φ agg a ψ X A := by
    let a : α → α → ℝ := Function.extend X
      (fun u => Function.extend X (c u) (fun _ => 0)) (fun _ _ => 0)
    have ha (u v : Fin n) : a (X u) (X v) = c u v := by
      dsimp only [a]
      rw [hX.extend_apply, hX.extend_apply]
    refine ⟨a, ?_⟩
    funext u
    simp only [convLayer, attLayer, ha]
  refine ⟨hatt, hconv, ?_⟩
  intro hX c
  obtain ⟨a, ha⟩ := hconv hX c
  exact ⟨fun xu xv => a xu xv • ψ xv, ha.trans (hatt a)⟩

#print axioms solution
