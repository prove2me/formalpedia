-- Prove2me | solution 1 for KellyStochasticNetworks.RandomAccessCapacity.inequality_value_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:58:58.888154+00:00
-- url     : https://prove2.me/submissions/8ebdc1dd-4495-4491-aafa-a0b3ce79e53d

import Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Optimization

open KellyStochasticNetworks.RandomAccessCapacity

theorem solution {n m : ℕ} (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (h : (Fin n → ℝ) → Fin m → ℝ)
    (hX : Convex ℝ X) (hf : ConvexOn ℝ X f)
    (hh : ∀ i, ConvexOn ℝ X (fun x => h x i)) :
    let φ : (Fin m → ℝ) → EReal := fun b =>
      sInf {v : EReal | ∃ x ∈ X, (∀ i, h x i ≤ b i) ∧ v = (f x : EReal)}
    Convex ℝ {p : (Fin m → ℝ) × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
  intro φ
  -- near-optimal feasible points
  have hnear : ∀ (b : Fin m → ℝ) (a ε : ℝ), φ b ≤ (a : EReal) → 0 < ε →
      ∃ x ∈ X, (∀ i, h x i ≤ b i) ∧ f x < a + ε := by
    intro b a ε hb hε
    have hlt : φ b < ((a + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hb (EReal.coe_lt_coe_iff.2 (by linarith))
    obtain ⟨v, ⟨x, hx, hxb, rfl⟩, hv⟩ := sInf_lt_iff.1 hlt
    exact ⟨x, hx, hxb, EReal.coe_lt_coe_iff.1 hv⟩
  intro p hp q hq s t hs ht hst
  simp only [Set.mem_setOf_eq] at hp hq ⊢
  set c : ℝ := s * p.2 + t * q.2
  have hc : (s • p + t • q).2 = c := by simp [c]
  rw [hc]
  -- φ(...) ≤ c + ε for all ε > 0
  refine EReal.le_of_forall_lt_iff_le.1 ?_
  intro d hd
  have hd' : c < d := EReal.coe_lt_coe_iff.1 hd
  set ε := d - c
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨x, hx, hxb, hfx⟩ := hnear p.1 p.2 ε hp hε
  obtain ⟨y, hy, hyb, hfy⟩ := hnear q.1 q.2 ε hq hε
  have hz : s • x + t • y ∈ X := hX hx hy hs ht hst
  have hzb : ∀ i, h (s • x + t • y) i ≤ (s • p + t • q).1 i := by
    intro i
    have := (hh i).2 hx hy hs ht hst
    simp only [smul_eq_mul] at this
    simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hxb i) hs, mul_le_mul_of_nonneg_left (hyb i) ht]
  have hfz : f (s • x + t • y) ≤ s * f x + t * f y := by
    have := hf.2 hx hy hs ht hst
    simpa [smul_eq_mul] using this
  have hle : φ (s • p + t • q).1 ≤ (f (s • x + t • y) : EReal) :=
    sInf_le ⟨s • x + t • y, hz, hzb, rfl⟩
  refine hle.trans (EReal.coe_le_coe_iff.2 ?_)
  have : s * f x + t * f y ≤ s * (p.2 + ε) + t * (q.2 + ε) := by
    nlinarith [mul_le_mul_of_nonneg_left hfx.le hs, mul_le_mul_of_nonneg_left hfy.le ht]
  have e : s * (p.2 + ε) + t * (q.2 + ε) = d := by
    simp only [ε, c] at *
    rw [← sub_eq_zero]
    have : s * (p.2 + (d - (s * p.2 + t * q.2))) + t * (q.2 + (d - (s * p.2 + t * q.2))) - d =
        (s + t - 1) * (d - (s * p.2 + t * q.2)) := by ring
    rw [this, hst, sub_self, zero_mul]
  linarith
