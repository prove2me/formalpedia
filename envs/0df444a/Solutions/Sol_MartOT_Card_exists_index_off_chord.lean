-- Prove2me | solution 1 for MartOT.Card.exists_index_off_chord
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:54:00.597992+00:00
-- url     : https://prove2.me/submissions/ba77f7c4-97de-4a46-9d8e-159093fbc1fa

import Mathlib

theorem solution (h : ℝ → ℝ) (k : ℕ)
    (hk : ∀ s t : ℝ, {x : ℝ | deriv h x = s * x + t}.encard ≤ k)
    (a : ℝ) (b : Fin (k + 1) → ℝ) (hb : StrictMono b) :
    ∃ i : Fin (k + 1), 0 < (i : ℕ) ∧ (i : ℕ) < k ∧
      ∀ a' : ℝ, a' ≠ a →
        (deriv h (b i - a) -
            ((1 - (b i - b 0) / (b (Fin.last k) - b 0)) * deriv h (b 0 - a) +
              (b i - b 0) / (b (Fin.last k) - b 0) * deriv h (b (Fin.last k) - a))) *
          (a' - a) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have h1 := hk 0 (deriv h 0)
    have h2 : 1 ≤ {x : ℝ | deriv h x = 0 * x + deriv h 0}.encard :=
      Set.one_le_encard_iff_nonempty.mpr ⟨0, by simp⟩
    have := le_trans h2 h1
    simp at this
  · have hlt : (0 : Fin (k + 1)) < Fin.last k := by
      rw [Fin.lt_def]; simp; omega
    have hD : 0 < b (Fin.last k) - b 0 := sub_pos.mpr (hb hlt)
    set D := b (Fin.last k) - b 0 with hDdef
    set s := (deriv h (b (Fin.last k) - a) - deriv h (b 0 - a)) / D with hs
    set t := deriv h (b 0 - a) - s * (b 0 - a) with ht
    have hall : ∀ i, deriv h (b i - a) = s * (b i - a) + t := by
      intro i
      by_cases h0 : (i : ℕ) = 0
      · have : i = 0 := Fin.ext (by simp [h0])
        subst this
        rw [ht]; ring
      by_cases hk' : (i : ℕ) = k
      · have : i = Fin.last k := Fin.ext (by simp [hk'])
        subst this
        rw [ht, hs]
        field_simp
        ring
      · obtain ⟨a', ha', heq⟩ := hcon i (by omega) (by have := i.isLt; omega)
        have hE := (mul_eq_zero.mp heq).resolve_right (sub_ne_zero.mpr ha')
        have hEq : deriv h (b i - a) = (1 - (b i - b 0) / D) * deriv h (b 0 - a) +
            (b i - b 0) / D * deriv h (b (Fin.last k) - a) := by linarith
        rw [hEq, ht, hs]
        field_simp
        ring
    have hmaps : Set.MapsTo (fun i : Fin (k + 1) => b i - a) Set.univ
        {x : ℝ | deriv h x = s * x + t} := by
      intro i _
      exact hall i
    have hinj : Set.InjOn (fun i : Fin (k + 1) => b i - a) Set.univ := by
      intro i _ j _ hij
      exact hb.injective (by simpa using hij)
    have h1 := Set.encard_le_encard_of_injOn hmaps hinj
    have h2 := hk s t
    have hle : ((k + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by
      calc ((k + 1 : ℕ) : ℕ∞) = (Set.univ : Set (Fin (k + 1))).encard := by
            rw [Set.encard_univ]; simp
        _ ≤ _ := h1
        _ ≤ _ := h2
    have : k + 1 ≤ k := by exact_mod_cast hle
    omega
