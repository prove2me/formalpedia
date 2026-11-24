-- Prove2me | solution 1 for L1ResistanceCount.Counting.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T06:17:18.222788+00:00
-- url     : https://prove2.me/submissions/8521d77a-2a36-4a17-a457-63819c77dffa

import Mathlib
import Definitions.Def_L1ResistanceCount_Counting_Obstacle

open L1ResistanceCount.Counting

theorem solution {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected)
    (p : Vector n) (hboundary : ∃ v, p v ≤ 0)
    (hsubharmonic : ∀ v, 0 < p v → G.laplacian.mulVec p v ≤ 0) :
    ∀ v, p v ≤ 0 := by
  classical
  obtain ⟨b, hb⟩ := hboundary
  haveI : Nonempty (Fin n) := ⟨b⟩
  obtain ⟨v0, hv0⟩ := Finite.exists_max p
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc⟩ := hcon
  have hMpos : 0 < p v0 := lt_of_lt_of_le hc (hv0 c)
  -- key: neighbours of a maximum vertex are maxima
  have key : ∀ v, p v = p v0 → ∀ e, (G.head e = v ∨ G.tail e = v) →
      p (G.head e) = p v0 ∧ p (G.tail e) = p v0 := by
    intro v hv
    have hle := hsubharmonic v (by rw [hv]; exact hMpos)
    have hterm : ∀ e, 0 ≤ G.incidence e v * G.w e * (p (G.head e) - p (G.tail e)) := by
      intro e
      have h1 := hv0 (G.head e)
      have h2 := hv0 (G.tail e)
      have hw := G.w_pos e
      have hne := G.head_ne_tail e
      unfold EffResSparsify.Sampling.WGraph.incidence
      by_cases h : v = G.head e
      · simp only [h, if_true, one_mul]
        apply mul_nonneg hw.le
        rw [h] at hv; linarith
      · by_cases h' : v = G.tail e
        · simp only [h, h', if_false, if_true, hne.symm, hne]
          have hne' := hne
          have : 0 ≤ G.w e * (p (G.tail e) - p (G.head e)) := by
            apply mul_nonneg hw.le
            rw [h'] at hv; linarith
          nlinarith
        · simp [h, h']
    have hBp : ∀ e, G.incidence.mulVec p e = p (G.head e) - p (G.tail e) := by
      intro e
      have hne := G.head_ne_tail e
      unfold EffResSparsify.Sampling.WGraph.incidence
      simp only [Matrix.mulVec, dotProduct]
      have : ∀ x, (if x = G.head e then (1:ℝ) else if x = G.tail e then -1 else 0) * p x
          = (if x = G.head e then p x else 0) - (if x = G.tail e then p x else 0) := by
        intro x
        by_cases h1 : x = G.head e
        · have : x ≠ G.tail e := fun h => hne (h1.symm.trans h)
          simp [h1, this, hne]
        · by_cases h2 : x = G.tail e <;> simp [h1, h2, hne.symm]
      simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hsum : G.laplacian.mulVec p v =
        ∑ e, G.incidence e v * G.w e * (p (G.head e) - p (G.tail e)) := by
      unfold EffResSparsify.Sampling.WGraph.laplacian EffResSparsify.Sampling.WGraph.weightMatrix
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hD : ∀ q : Fin m → ℝ, (Matrix.diagonal G.w).mulVec q = fun e => G.w e * q e :=
        fun q => funext fun e => Matrix.mulVec_diagonal _ _ _
      rw [hD]
      simp only [hBp]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      ring
    have hzero : ∀ e ∈ Finset.univ, G.incidence e v * G.w e * (p (G.head e) - p (G.tail e)) = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hterm e)).1
        (le_antisymm (hsum ▸ hle) (Finset.sum_nonneg (fun e _ => hterm e)))
      exact this
    intro e he
    have h0 := hzero e (Finset.mem_univ e)
    have hw := G.w_pos e
    have hne := G.head_ne_tail e
    have h1 := hv0 (G.head e)
    have h2 := hv0 (G.tail e)
    unfold EffResSparsify.Sampling.WGraph.incidence at h0
    rcases he with he | he
    · have : v = G.head e := he.symm
      simp only [this, if_true, one_mul] at h0 hv
      rcases mul_eq_zero.1 h0 with h | h
      · linarith
      · constructor <;> linarith
    · have h' : v = G.tail e := he.symm
      have : v ≠ G.head e := fun h => hne (h.symm.trans h')
      simp only [this, h', if_false, if_true, hne.symm] at h0 hv
      have h3 : G.w e * (p (G.head e) - p (G.tail e)) = 0 := by linarith
      rcases mul_eq_zero.1 h3 with h | h
      · linarith
      · constructor <;> linarith
  have hclosed : ∀ u w, G.toSimpleGraph.Adj u w → p u = p v0 → p w = p v0 := by
    intro u w hadj hu
    obtain ⟨_, h | h⟩ := hadj
    · obtain ⟨e, he1, he2⟩ := h
      exact (key u hu e (Or.inl he1)).2 |> fun _ => by
        have := key u hu e (Or.inl he1); rw [← he2]; exact this.2
    · obtain ⟨e, he1, he2⟩ := h
      have := key u hu e (Or.inr he2); rw [← he1]; exact this.1
  have hwalk : ∀ {a c : Fin n} (w : G.toSimpleGraph.Walk a c), p a = p v0 → p c = p v0 := by
    intro a c w
    induction w with
    | nil => exact id
    | cons h _ ih => exact fun ha => ih (hclosed _ _ h ha)
  have hall : ∀ u, p u = p v0 := by
    intro u
    obtain ⟨walk⟩ := hG.preconnected v0 u
    exact hwalk walk rfl
  have := hall b
  linarith
