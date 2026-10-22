-- Prove2me | solution 1 for InterdepSOS.RSV.display_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:22:52.197981+00:00
-- url     : https://prove2.me/submissions/adc2310e-8ccf-4d59-bb44-22891e9758bc

import Mathlib
import Definitions.Def_InterdepSOS_RSV_Setting
set_option autoImplicit false
open InterdepSOS.RSV

theorem l23_aux_BB {n : ℕ} (w : Signal n → ℝ) (d : ℝ) (hd : IsDSOS d w) (A : Finset (Fin n))
    (s y s' : Signal n) (hss' : ∀ j, j ∉ A → s j ≤ s' j) :
    ∀ T : Finset (Fin n), T ⊆ A →
      w (fun j => if j ∈ A then (if j ∈ T then s j + y j else s j) else s' j) -
        w (fun j => if j ∈ A then s j else s' j) ≤
      d * (w (fun j => if j ∈ T then s j + y j else s j) - w s) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    have e1 : (fun j => if j ∈ A then (if j ∈ (∅ : Finset (Fin n)) then s j + y j else s j) else s' j)
        = (fun j => if j ∈ A then s j else s' j) := by
      funext j; simp
    have e2 : (fun j => if j ∈ (∅ : Finset (Fin n)) then s j + y j else s j) = s := by
      funext j; simp
    rw [e1, e2]; simp
  | insert a T haT ih =>
    intro hsub
    have hTA : T ⊆ A := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    have haA : a ∈ A := hsub (Finset.mem_insert_self a T)
    have ih' := ih hTA
    set PL : Signal n := fun j => if j ∈ A then (if j ∈ T then s j + y j else s j) else s' j with hPL
    set PR : Signal n := fun j => if j ∈ T then s j + y j else s j with hPR
    have hL1 : (fun j => if j ∈ A then (if j ∈ insert a T then s j + y j else s j) else s' j)
        = Function.update PL a (s a + y a) := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [hPL, haA]
      · simp [hPL, Function.update_of_ne hj, hj]
    have hL2 : PL = Function.update PL a (s a) := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [hPL, haA, haT]
      · simp [Function.update_of_ne hj]
    have hR1 : (fun j => if j ∈ insert a T then s j + y j else s j)
        = Function.update PR a (s a + y a) := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [hPR]
      · simp [hPR, Function.update_of_ne hj, hj]
    have hR2 : PR = Function.update PR a (s a) := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [hPR, haT]
      · simp [Function.update_of_ne hj]
    have key := hd a (s a) (y a) PL PR (by
      intro l hl
      by_cases hlA : l ∈ A
      · simp [hPL, hPR, hlA]
      · have : l ∉ T := fun h => hlA (hTA h)
        simp [hPL, hPR, hlA, this, hss' l hlA])
    rw [hL1, hR1]
    rw [← hL2, ← hR2] at key
    linarith

theorem l23_BB {n : ℕ} (w : Signal n → ℝ) (hw : ∀ s, 0 ≤ w s)
    (d : ℝ) (hd : IsDSOS d w) (A : Finset (Fin n))
    (s y s' : Signal n) (hss' : ∀ j, j ∉ A → s j ≤ s' j) :
    w (fun j => if j ∈ A then s j + y j else s' j) -
      w (fun j => if j ∈ A then s j else s' j) ≤
      d * (w (fun j => if j ∈ A then s j + y j else s j) - w s) := by
  have h := l23_aux_BB w d hd A s y s' hss' A (Finset.Subset.refl A)
  have e1 : (fun j => if j ∈ A then (if j ∈ A then s j + y j else s j) else s' j)
      = (fun j => if j ∈ A then s j + y j else s' j) := by
    funext j; by_cases hj : j ∈ A <;> simp [hj]
  rw [e1] at h
  exact h

theorem l31_BB {n : ℕ} (w : Signal n → ℝ) (hw : ∀ s, 0 ≤ w s)
    (d : ℝ) (hd_nonneg : 0 ≤ d) (hd : IsDSOS d w) (i : Fin n)
    (s : Signal n) :
    1 / (d + 1) * w s ≤
      (2 ^ (n - 1) : ℝ)⁻¹ *
        ∑ A ∈ (Finset.univ.erase i).powerset, w (keepOn (insert i A) s) := by
  classical
  set E : Finset (Fin n) := Finset.univ.erase i with hE
  -- pointwise inequality
  have hpt : ∀ A ∈ E.powerset, w s - w (keepOn (insert i A) s) ≤
      d * w (keepOn (insert i (E \ A)) s) := by
    intro A hA
    have hAE : A ⊆ E := Finset.mem_powerset.1 hA
    have key := l23_BB w hw d hd (E \ A) (keepOn {i} s) s (keepOn (insert i A) s) (by
      intro j hj
      by_cases hji : j = i
      · subst hji; simp [keepOn]
      · simp [keepOn, hji])
    have e1 : (fun j => if j ∈ E \ A then keepOn {i} s j + s j else keepOn (insert i A) s j) = s := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [keepOn, hE]
      · by_cases hjA : j ∈ A
        · have : j ∉ E \ A := by simp [hjA]
          simp [keepOn, this, hjA, hji]
        · have : j ∈ E \ A := by simp [hE, hji, hjA]
          simp [keepOn, this, hji, hjA]
    have e2 : (fun j => if j ∈ E \ A then keepOn {i} s j else keepOn (insert i A) s j) = keepOn (insert i A) s := by
      funext j
      by_cases hji : j = i
      · subst hji
        have : j ∉ E \ A := by simp [hE]
        simp [keepOn, this]
      · by_cases hjA : j ∈ A
        · have : j ∉ E \ A := by simp [hjA]
          simp [keepOn, this]
        · have : j ∈ E \ A := by simp [hE, hji, hjA]
          simp [keepOn, this, hji, hjA]
    have e3 : (fun j => if j ∈ E \ A then keepOn {i} s j + s j else keepOn {i} s j) = keepOn (insert i (E \ A)) s := by
      funext j
      by_cases hji : j = i
      · subst hji
        have : j ∉ E \ A := by simp [hE]
        simp [keepOn, this]
      · by_cases hjB : j ∈ E \ A
        · simp [keepOn, hjB, hji]
        · simp [keepOn, hjB, hji]
    rw [e1, e2, e3] at key
    have h0 := hw (keepOn {i} s)
    nlinarith [mul_nonneg hd_nonneg h0]
  have hsum := Finset.sum_le_sum hpt
  have hcompl : ∑ A ∈ E.powerset, w (keepOn (insert i (E \ A)) s) =
      ∑ A ∈ E.powerset, w (keepOn (insert i A) s) := by
    apply Finset.sum_nbij' (fun A => E \ A) (fun A => E \ A)
    · intro A hA; simp
    · intro A hA; simp
    · intro A hA
      have : A ⊆ E := Finset.mem_powerset.1 hA
      simp [Finset.sdiff_sdiff_eq_self this]
    · intro A hA
      have : A ⊆ E := Finset.mem_powerset.1 hA
      simp [Finset.sdiff_sdiff_eq_self this]
    · intro A hA; rfl
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcompl] at hsum
  simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_powerset, nsmul_eq_mul] at hsum
  have hcard : (E.card) = n - 1 := by simp [hE]
  rw [hcard] at hsum
  have hpos : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  have hd1 : (0 : ℝ) < d + 1 := by linarith
  rw [← div_eq_inv_mul, div_mul_eq_mul_div, div_le_div_iff₀ hd1 hpos]
  push_cast at hsum
  nlinarith [hsum]

theorem solution {n : ℕ} (v : Valuation n) (hv : IsValuation v)
    (d : ℝ) (hd : ∀ i, IsDSOS d (v i)) (i : Fin n) (s : Signal n) :
    v i s / (d + 1) * (1 / 2 : ℝ) ≤
      avgB (fun B => if i ∈ B then rsvWeight v B s i else 0) := by
  classical
  have hnn : ∀ t, 0 ≤ v i t := hv.1 i
  -- d ≥ 0 : otherwise handle separately
  have hd0 : 0 ≤ d := by
    have h1 := hv.2.2 i 0 0 1 (by norm_num)
    have h2 := hd i i 0 1 0 0 (by intro l _; exact le_rfl)
    rw [zero_add] at h2
    by_contra hneg
    push_neg at hneg
    nlinarith
  · have h31 := l31_BB (v i) hnn d hd0 (hd i) i s
    set E : Finset (Fin n) := Finset.univ.erase i with hE
    have hsum : ∑ B : Finset (Fin n), (if i ∈ B then rsvWeight v B s i else 0) =
        ∑ A ∈ E.powerset, v i (keepOn (insert i A) s) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_nbij' (fun B => Bᶜ) (fun A => Aᶜ)
      · intro B hB
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
        rw [Finset.mem_powerset]
        intro x hx
        simp only [hE, Finset.mem_erase, Finset.mem_univ, and_true]
        rintro rfl
        exact (Finset.mem_compl.1 hx) hB
      · intro A hA
        have := Finset.mem_powerset.1 hA
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Finset.mem_compl]
        intro hiA
        have := this hiA
        simp [hE] at this
      · intro B _; simp
      · intro A _; simp
      · intro B hB; simp [rsvWeight]
    have hcard : (2 ^ (n - 1) : ℝ) * 2 = 2 ^ n := by
      have : 0 < n := Fin.pos i
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp [pow_succ]
    unfold avgB
    rw [hsum, ← hcard]
    have hpos : (0 : ℝ) < 2 ^ (n - 1) := by positivity
    have : (2 ^ (n - 1) * 2 : ℝ)⁻¹ = (2 ^ (n - 1) : ℝ)⁻¹ * (1 / 2) := by
      rw [mul_inv]; ring
    rw [this, mul_assoc]
    have h' : 1 / (d + 1) * v i s ≤ (2 ^ (n - 1) : ℝ)⁻¹ * ∑ A ∈ E.powerset, v i (keepOn (insert i A) s) := h31
    have hh : v i s / (d + 1) * (1 / 2 : ℝ) = (1 / (d + 1) * v i s) * (1 / 2) := by ring
    rw [hh, ← mul_assoc]
    nlinarith [h', (by norm_num : (0:ℝ) ≤ 1 / 2)]
