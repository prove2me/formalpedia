-- Prove2me | solution 1 for InventoryControl.serial_aggregation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T16:52:26.597986+00:00
-- url     : https://prove2.me/submissions/5509b9dd-9a35-4dd3-a980-64b188c8ec0d

import Mathlib
import Definitions.Def_InventoryControl_serial

open InventoryControl in
theorem solution {N : ℕ} (A e : Fin N → ℝ) (d : ℝ) (hd : 0 < d)
    (hA : ∀ i, 0 < A i) (he : ∀ i, 0 < e i) (Qrel : Fin N → ℝ) (hpos : ∀ i, 0 < Qrel i)
    (hnest : SerialNested Qrel)
    (hopt : ∀ Q : Fin N → ℝ, (∀ i, 0 < Q i) → SerialNested Q →
      serialCost A e d Qrel ≤ serialCost A e d Q)
    (i j : Fin N) (hij : j.val = i.val + 1) (hratio : A j / e j < A i / e i) :
    Qrel j = Qrel i := by
  -- cost change when one coordinate is updated
  have hupd : ∀ (k : Fin N) (x : ℝ),
      serialCost A e d (Function.update Qrel k x)
        = serialCost A e d Qrel + (eoqCost (A k) d (e k) x - eoqCost (A k) d (e k) (Qrel k)) := by
    intro k x
    unfold serialCost
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    have hrest : ∑ l ∈ Finset.univ.erase k, eoqCost (A l) d (e l) (Function.update Qrel k x l)
        = ∑ l ∈ Finset.univ.erase k, eoqCost (A l) d (e l) (Qrel l) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    rw [hrest, Function.update_self]
    ring
  have hji : j ≠ i := by
    intro h
    rw [h] at hij
    omega
  have hle : Qrel i ≤ Qrel j := hnest i j hij
  by_contra hne
  have hlt : Qrel i < Qrel j := lt_of_le_of_ne hle (Ne.symm hne)
  set a := Qrel i with ha
  set b := Qrel j with hb
  have ha0 : 0 < a := hpos i
  have hb0 : 0 < b := hpos j
  -- monotonicity along the chain: consecutive
  -- perturbation 1: lower Q_j to a
  have hnest1 : SerialNested (Function.update Qrel j a) := by
    intro k l hkl
    by_cases hlj : l = j
    · subst hlj
      have hki : k = i := Fin.ext (by omega)
      subst hki
      have hkj : k ≠ l := by intro h; rw [h] at hkl; omega
      rw [Function.update_self, Function.update_of_ne hkj]
    · rw [Function.update_of_ne hlj]
      by_cases hkj : k = j
      · subst hkj
        rw [Function.update_self]
        exact le_trans hlt.le (hnest k l hkl)
      · rw [Function.update_of_ne hkj]
        exact hnest k l hkl
  have hpos1 : ∀ k, 0 < Function.update Qrel j a k := by
    intro k
    by_cases hkj : k = j
    · subst hkj; rw [Function.update_self]; exact ha0
    · rw [Function.update_of_ne hkj]; exact hpos k
  have h1 := hopt _ hpos1 hnest1
  rw [hupd] at h1
  -- perturbation 2: raise Q_i to b
  have hnest2 : SerialNested (Function.update Qrel i b) := by
    intro k l hkl
    by_cases hki : k = i
    · subst hki
      have hlj : l = j := Fin.ext (by omega)
      subst hlj
      rw [Function.update_self, Function.update_of_ne hji]
    · rw [Function.update_of_ne hki]
      by_cases hli : l = i
      · subst hli
        rw [Function.update_self]
        exact le_trans (hnest k l hkl) hlt.le
      · rw [Function.update_of_ne hli]
        exact hnest k l hkl
  have hpos2 : ∀ k, 0 < Function.update Qrel i b k := by
    intro k
    by_cases hki : k = i
    · subst hki; rw [Function.update_self]; exact hb0
    · rw [Function.update_of_ne hki]; exact hpos k
  have h2 := hopt _ hpos2 hnest2
  rw [hupd] at h2
  have h1' : 0 ≤ eoqCost (A j) d (e j) a - eoqCost (A j) d (e j) b := by linarith
  have h2' : 0 ≤ eoqCost (A i) d (e i) b - eoqCost (A i) d (e i) a := by linarith
  unfold eoqCost at h1' h2'
  have hej := he j
  have hei := he i
  have hAj := hA j
  have hAi := hA i
  -- h1': e_j a b ≤ 2 d A_j ; h2': e_i a b ≥ 2 d A_i
  have k1 : e j * (a * b) ≤ 2 * d * A j := by
    have hid : a / 2 * e j + d / a * A j - (b / 2 * e j + d / b * A j)
        = (b - a) * (2 * d * A j - e j * (a * b)) / (2 * a * b) := by
      field_simp
      ring
    rw [hid] at h1'
    have hden : 0 < 2 * a * b := by positivity
    have := (div_nonneg_iff.mp h1')
    rcases this with ⟨hn, _⟩ | ⟨_, hd'⟩
    · have hba : 0 < b - a := by linarith
      nlinarith
    · linarith
  have k2 : 2 * d * A i ≤ e i * (a * b) := by
    have hid : b / 2 * e i + d / b * A i - (a / 2 * e i + d / a * A i)
        = (b - a) * (e i * (a * b) - 2 * d * A i) / (2 * a * b) := by
      field_simp
      ring
    rw [hid] at h2'
    have hden : 0 < 2 * a * b := by positivity
    have := (div_nonneg_iff.mp h2')
    rcases this with ⟨hn, _⟩ | ⟨_, hd'⟩
    · have hba : 0 < b - a := by linarith
      nlinarith
    · linarith
  -- A_i / e_i ≤ ab/(2d) ≤ A_j / e_j
  rw [div_lt_div_iff₀ hej hei] at hratio
  -- A j * e i < A i * e j
  have : A i * e j * (2 * d) ≤ A j * e i * (2 * d) := by
    nlinarith [mul_le_mul_of_nonneg_left k2 hej.le, mul_le_mul_of_nonneg_left k1 hei.le]
  have h2d : 0 < 2 * d := by linarith
  nlinarith
