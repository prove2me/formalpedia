-- Prove2me | solution 2 for ModernConvex.SLemma.general_helly
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:40:33.340998+00:00
-- url     : https://prove2.me/submissions/30c08659-77d0-456a-8c12-b4eac9fa21d7

import Mathlib
set_option autoImplicit false

theorem solution {n : ℕ} {I : Type} (A : I → Set (Fin n → ℝ))
    (hclosed : ∀ α, IsClosed (A α)) (hconvex : ∀ α, Convex ℝ (A α))
    (hinter : ∀ f : Fin (n + 1) → I, (⋂ k, A (f k)).Nonempty)
    (hbdd : ∃ s : Finset I, Bornology.IsBounded (⋂ α ∈ s, A α)) :
    (⋂ α, A α).Nonempty := by
  classical
  obtain ⟨s, hs⟩ := hbdd
  have hBclosed : IsClosed (⋂ α ∈ s, A α) := isClosed_biInter (fun α _ => hclosed α)
  have hBcomp : IsCompact (⋂ α ∈ s, A α) := Metric.isCompact_of_isClosed_isBounded hBclosed hs
  -- every at most n+1 of the sets have a common point
  have hsmall : ∀ K : Finset I, K.card ≤ n + 1 → (⋂ i ∈ K, A i).Nonempty := by
    intro K hK
    rcases K.eq_empty_or_nonempty with h0 | hne
    · subst h0; simp
    · have hpos : 0 < K.card := Finset.card_pos.mpr hne
      let f : Fin (n + 1) → I := fun k =>
        if h : (k : ℕ) < K.card then ((K.equivFin.symm ⟨k, h⟩ : K) : I)
        else ((K.equivFin.symm ⟨0, hpos⟩ : K) : I)
      obtain ⟨x, hx⟩ := hinter f
      refine ⟨x, ?_⟩
      simp only [Set.mem_iInter] at hx ⊢
      intro i hi
      have hlt : ((K.equivFin ⟨i, hi⟩ : Fin K.card) : ℕ) < n + 1 :=
        lt_of_lt_of_le (K.equivFin ⟨i, hi⟩).2 hK
      have := hx ⟨(K.equivFin ⟨i, hi⟩ : ℕ), hlt⟩
      have hf : f ⟨(K.equivFin ⟨i, hi⟩ : ℕ), hlt⟩ = i := by
        simp only [f]
        rw [dif_pos (K.equivFin ⟨i, hi⟩).2]
        simp
      rwa [hf] at this
  -- finite Helly
  have hfin : ∀ J : Finset I, (⋂ i ∈ J, A i).Nonempty := by
    intro J
    apply Convex.helly_theorem' (𝕜 := ℝ) (F := A) (s := J) (fun i _ => hconvex i)
    intro K _ hKcard
    apply hsmall K
    rw [Module.finrank_fin_fun] at hKcard
    exact hKcard
  -- compactness trick
  have key := Convex.helly_theorem_compact' (𝕜 := ℝ) (F := fun α => A α ∩ ⋂ β ∈ s, A β)
    (fun α => (hconvex α).inter (convex_iInter fun β => convex_iInter fun _ => hconvex β))
    (fun α => hBcomp.inter_left (hclosed α))
    (by
      intro J _
      obtain ⟨x, hx⟩ := hfin (J ∪ s)
      refine ⟨x, ?_⟩
      simp only [Set.mem_iInter] at hx ⊢
      intro i hi
      refine ⟨hx i (Finset.mem_union_left _ hi), ?_⟩
      simp only [Set.mem_iInter]
      intro β hβ
      exact hx β (Finset.mem_union_right _ hβ))
  obtain ⟨x, hx⟩ := key
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro i
  exact (hx i).1
