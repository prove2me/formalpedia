-- Prove2me | solution 1 for NQueensComp.NPC.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:39:09.324596+00:00
-- url     : https://prove2.me/submissions/bb0c82f2-5769-4031-9ed9-84f983061a33

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

open NQueensComp.NPC

/-- Two numbers below `n` plus distinct multiples of `n` differ. -/
theorem key_col (n x y u v : ℕ) (hx : x < n) (hy : y < n) (huv : u ≠ v) :
    x + n * u ≠ y + n * v := by
  intro heq
  rcases Nat.lt_or_gt_of_ne huv with h | h
  · have : n * (u + 1) ≤ n * v := Nat.mul_le_mul_left n h
    nlinarith
  · have : n * (v + 1) ≤ n * u := Nat.mul_le_mul_left n h
    nlinarith

theorem sumSet_eq (n : ℕ) (Q₁ Q₂ : Finset Queen) :
    sumSet Q₁ (scaleSet n Q₂) = (Q₁ ×ˢ Q₂).image (fun p => p.1 + n • p.2) := by
  ext x
  simp only [sumSet, scaleSet, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    obtain ⟨q, hq, hqb⟩ := hb
    exact ⟨(a, q), ⟨ha, hq⟩, by simp only at hqb; rw [hqb]⟩
  · rintro ⟨⟨a, q⟩, ⟨ha, hq⟩, rfl⟩
    exact ⟨(a, n • q), ⟨ha, q, hq, rfl⟩, rfl⟩

theorem solution (n m : ℕ) (Q₁ Q₂ : Finset Queen) (h₁ : IsModularSol n Q₁)
    (h₂ : IsNQueensSol m Q₂) : IsNQueensSol (n * m) (sumSet Q₁ (scaleSet n Q₂)) := by
  obtain ⟨⟨hn, hfit₁, hcard₁, hNA₁⟩, hmod⟩ := h₁
  obtain ⟨hm, hfit₂, hcard₂, hNA₂⟩ := h₂
  rw [sumSet_eq]
  -- the decomposition is unique
  have uniq : ∀ q₁ ∈ Q₁, ∀ q₂ ∈ Q₁, ∀ q₃ q₄ : Queen,
      q₁ + n • q₃ = q₂ + n • q₄ → q₁ = q₂ ∧ q₃ = q₄ := by
    intro q₁ hq₁ q₂ hq₂ q₃ q₄ heq
    have f₁ := hfit₁ q₁ hq₁
    have f₂ := hfit₁ q₂ hq₂
    obtain ⟨a₁, b₁⟩ := q₁
    obtain ⟨a₂, b₂⟩ := q₂
    obtain ⟨a₃, b₃⟩ := q₃
    obtain ⟨a₄, b₄⟩ := q₄
    simp only [FitsOn, size, max_lt_iff] at f₁ f₂
    simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at heq ⊢
    obtain ⟨hc, hr⟩ := heq
    have e₁ : a₃ = a₄ := by
      by_contra h; exact key_col n a₁ a₂ a₃ a₄ f₁.1 f₂.1 h hc
    have e₂ : b₃ = b₄ := by
      by_contra h; exact key_col n b₁ b₂ b₃ b₄ f₁.2 f₂.2 h hr
    subst e₁ e₂
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  · intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨⟨q₁, q₂⟩, hp, rfl⟩ := hq
    rw [Finset.mem_product] at hp
    have f₁ := hfit₁ q₁ hp.1
    have f₂ := hfit₂ q₂ hp.2
    obtain ⟨a₁, b₁⟩ := q₁
    obtain ⟨a₂, b₂⟩ := q₂
    simp only [FitsOn, size, max_lt_iff, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul] at f₁ f₂ ⊢
    constructor
    · have : n * (a₂ + 1) ≤ n * m := Nat.mul_le_mul_left n f₂.1
      nlinarith
    · have : n * (b₂ + 1) ≤ n * m := Nat.mul_le_mul_left n f₂.2
      nlinarith
  · rw [Finset.card_image_of_injOn, Finset.card_product, hcard₁, hcard₂]
    rintro ⟨q₁, q₃⟩ hp ⟨q₂, q₄⟩ hp' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
    obtain ⟨e₁, e₂⟩ := uniq q₁ hp.1 q₂ hp'.1 q₃ q₄ heq
    rw [e₁, e₂]
  · intro x hx y hy hatt
    rw [Finset.mem_image] at hx hy
    obtain ⟨⟨q₁, q₃⟩, hp, rfl⟩ := hx
    obtain ⟨⟨q₂, q₄⟩, hp', rfl⟩ := hy
    rw [Finset.mem_product] at hp hp'
    obtain ⟨hq₁, hq₃⟩ := hp
    obtain ⟨hq₂, hq₄⟩ := hp'
    obtain ⟨hne, hline⟩ := hatt
    have f₁ := hfit₁ q₁ hq₁
    have f₂ := hfit₁ q₂ hq₂
    obtain ⟨a₁, b₁⟩ := q₁
    obtain ⟨a₂, b₂⟩ := q₂
    obtain ⟨a₃, b₃⟩ := q₃
    obtain ⟨a₄, b₄⟩ := q₄
    simp only [FitsOn, size, max_lt_iff] at f₁ f₂
    simp only [col, row, sumDiag, diffDiag, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul] at hline
    -- reduce to the two component solutions
    have finish : (a₁, b₁) = (a₂, b₂) →
        (a₃ = a₄ ∨ b₃ = b₄ ∨ a₃ + b₃ = a₄ + b₄ ∨ (a₃ : ℤ) - b₃ = (a₄ : ℤ) - b₄) → False := by
      intro e hl
      rw [Prod.mk.injEq] at e
      obtain ⟨e1, e2⟩ := e
      subst e1 e2
      have : (a₃, b₃) ≠ (a₄, b₄) := fun h => hne (by rw [h])
      exact hNA₂ (a₃, b₃) hq₃ (a₄, b₄) hq₄ ⟨this, by simpa [col, row, sumDiag, diffDiag] using hl⟩
    have finish₁ : (a₁ = a₂ ∨ b₁ = b₂ ∨ a₁ + b₁ = a₂ + b₂ ∨ (a₁ : ℤ) - b₁ = (a₂ : ℤ) - b₂) →
        (a₁, b₁) = (a₂, b₂) := by
      intro hl
      by_contra h
      exact hNA₁ (a₁, b₁) hq₁ (a₂, b₂) hq₂ ⟨h, by simpa [col, row, sumDiag, diffDiag] using hl⟩
    rcases hline with h | h | h | h
    · -- columns
      have e₃ : a₃ = a₄ := by
        by_contra h'; exact key_col n a₁ a₂ a₃ a₄ f₁.1 f₂.1 h' h
      subst e₃
      have e₁ : a₁ = a₂ := by omega
      have := finish₁ (Or.inl e₁)
      exact finish this (Or.inl rfl)
    · -- rows
      have e₃ : b₃ = b₄ := by
        by_contra h'; exact key_col n b₁ b₂ b₃ b₄ f₁.2 f₂.2 h' h
      subst e₃
      have e₁ : b₁ = b₂ := by omega
      have := finish₁ (Or.inr (Or.inl e₁))
      exact finish this (Or.inr (Or.inl rfl))
    · -- sum-diagonals
      have hcong : ((a₁ + b₁ : ℕ) : ℤ) ≡ ((a₂ + b₂ : ℕ) : ℤ) [ZMOD (n : ℤ)] := by
        rw [Int.modEq_iff_dvd]
        refine ⟨((a₃ + b₃ : ℕ) : ℤ) - ((a₄ + b₄ : ℕ) : ℤ), ?_⟩
        have := congrArg (fun x : ℕ => (x : ℤ)) h
        push_cast at this ⊢
        linarith
      have e : (a₁, b₁) = (a₂, b₂) := by
        by_contra hne'
        exact (hmod (a₁, b₁) hq₁ (a₂, b₂) hq₂ hne').1 (by simpa [sumDiag] using hcong)
      have e' : a₃ + b₃ = a₄ + b₄ := by
        rw [Prod.mk.injEq] at e
        obtain ⟨e1, e2⟩ := e
        subst e1 e2
        have : n * (a₃ + b₃) = n * (a₄ + b₄) := by
          rw [Nat.mul_add, Nat.mul_add]; omega
        exact Nat.eq_of_mul_eq_mul_left (by omega) this
      exact finish e (Or.inr (Or.inr (Or.inl e')))
    · -- difference-diagonals
      have hcong : ((a₁ : ℤ) - b₁) ≡ ((a₂ : ℤ) - b₂) [ZMOD (n : ℤ)] := by
        rw [Int.modEq_iff_dvd]
        refine ⟨((a₃ : ℤ) - b₃) - ((a₄ : ℤ) - b₄), ?_⟩
        push_cast at h
        linarith
      have e : (a₁, b₁) = (a₂, b₂) := by
        by_contra hne'
        exact (hmod (a₁, b₁) hq₁ (a₂, b₂) hq₂ hne').2 (by simpa [diffDiag] using hcong)
      have e' : (a₃ : ℤ) - b₃ = (a₄ : ℤ) - b₄ := by
        rw [Prod.mk.injEq] at e
        obtain ⟨e1, e2⟩ := e
        subst e1 e2
        push_cast at h
        have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        have : (n : ℤ) * ((a₃ : ℤ) - b₃) = (n : ℤ) * ((a₄ : ℤ) - b₄) := by linarith
        exact mul_left_cancel₀ hn' this
      exact finish e (Or.inr (Or.inr (Or.inr e')))
