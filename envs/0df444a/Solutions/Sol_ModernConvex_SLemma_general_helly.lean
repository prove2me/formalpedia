-- Prove2me | solution 1 for ModernConvex.SLemma.general_helly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:50:02.678787+00:00
-- url     : https://prove2.me/submissions/85e92ab6-f89e-404b-96b5-07c26690c707

import Mathlib

theorem g70mc1_finite_inter {n : ℕ} {I : Type} (A : I → Set (Fin n → ℝ))
    (hconvex : ∀ α, Convex ℝ (A α))
    (hinter : ∀ f : Fin (n + 1) → I, (⋂ k, A (f k)).Nonempty) (J : Finset I) :
    (⋂ α ∈ J, A α).Nonempty := by
  classical
  apply Convex.helly_theorem' (𝕜 := ℝ) (fun i _ => hconvex i)
  intro I' _ hcard
  rw [Module.finrank_fin_fun] at hcard
  rcases I'.eq_empty_or_nonempty with h | ⟨i0, hi0⟩
  · subst h; simp
  let e := I'.equivFin
  let f : Fin (n + 1) → I := fun k =>
    if h : (k : ℕ) < I'.card then (e.symm ⟨k, h⟩ : I) else i0
  obtain ⟨x, hx⟩ := hinter f
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro α hα
  have hk : ((e ⟨α, hα⟩ : Fin I'.card) : ℕ) < n + 1 := by
    have := (e ⟨α, hα⟩).isLt; omega
  have := hx ⟨_, hk⟩
  simp only [f, Fin.is_lt, dite_true] at this
  simpa using this

theorem solution {n : ℕ} {I : Type} (A : I → Set (Fin n → ℝ))
    (hclosed : ∀ α, IsClosed (A α)) (hconvex : ∀ α, Convex ℝ (A α))
    (hinter : ∀ f : Fin (n + 1) → I, (⋂ k, A (f k)).Nonempty)
    (hbdd : ∃ s : Finset I, Bornology.IsBounded (⋂ α ∈ s, A α)) :
    (⋂ α, A α).Nonempty := by
  classical
  obtain ⟨s, hs⟩ := hbdd
  have hK : IsCompact (⋂ α ∈ s, A α) :=
    Metric.isCompact_of_isClosed_isBounded
      (isClosed_biInter fun i _ => hclosed i) hs
  have := hK.inter_iInter_nonempty A hclosed (fun u => by
    obtain ⟨x, hx⟩ := g70mc1_finite_inter A hconvex hinter (s ∪ u)
    refine ⟨x, ?_, ?_⟩ <;> simp only [Set.mem_iInter, Finset.mem_union] at hx ⊢
    · exact fun i hi => hx i (Or.inl hi)
    · exact fun i hi => hx i (Or.inr hi))
  exact this.mono Set.inter_subset_right
