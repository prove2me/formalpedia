-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_offset_2_residue_assembly__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:14:37.917268+00:00
-- url     : https://prove2.me/submissions/13f25d72-dde4-4975-8ea0-e2f9f8a04966

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
theorem p2m_lf (i : ℕ) : KnodelPrimeCordial.labelF i =
    if i % 12 = 0 ∨ i % 12 = 6 ∨ i % 12 = 10 then i + 2
    else if i % 12 = 1 ∨ i % 12 = 2 then i + 3
    else if i % 12 = 3 then i - 2
    else if i % 12 = 4 ∨ i % 12 = 8 ∨ i % 12 = 11 then i - 1
    else if i % 12 = 5 then i + 1
    else if i % 12 = 7 then i + 4 else i := by
  have h12 := Nat.mod_lt i (show 0 < 12 by norm_num)
  generalize hc : i % 12 = c at h12
  unfold KnodelPrimeCordial.labelF; rw [hc]
  interval_cases c <;> simp

theorem p2m_lfv (i c v : ℕ) (hc : i % 12 = c) (hv : KnodelPrimeCordial.labelF i = v) :
    KnodelPrimeCordial.labelF i = v := hv

theorem p2m_cop_add (x d : ℕ) (h : Nat.Coprime x d) : Nat.Coprime x (x + d) := by
  rw [add_comm, Nat.coprime_add_self_right]; exact h

theorem p2m_cop3 (x : ℕ) (h : ¬ 3 ∣ x) : Nat.Coprime x 3 :=
  ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h).symm

theorem p2m_idx2 (m a : ℕ) (ha : a < (12 * m + 6) / 2) :
    (2 * ((a + 2 ^ 2 - 1) % ((12 * m + 6) / 2)) + (12 * m + 6) - 1) % (12 * m + 6) =
      (2 * a + 5) % (12 * m + 6) := by
  have hN : (12 * m + 6) / 2 = 6 * m + 3 := by omega
  rw [hN] at ha ⊢
  rw [show a + 2 ^ 2 - 1 = a + 3 by norm_num]
  rcases Nat.lt_or_ge (a + 3) (6 * m + 3) with h | h
  · rw [Nat.mod_eq_of_lt h, show 2 * (a + 3) + (12 * m + 6) - 1 = (2 * a + 5) + (12 * m + 6) by omega,
      Nat.add_mod_right]
  · have e : (a + 3) % (6 * m + 3) = a + 3 - (6 * m + 3) := by
      rw [Nat.mod_eq_sub_mod h]; exact Nat.mod_eq_of_lt (by omega)
    rw [e]
    congr 1; omega

theorem p2m_cl2 (m a : ℕ) (ha : a < (12 * m + 6) / 2) :
    Nat.Coprime (KnodelPrimeCordial.labelF (2 * a))
      (KnodelPrimeCordial.labelF ((2 * ((a + 2 ^ 2 - 1) % ((12 * m + 6) / 2)) + (12 * m + 6) - 1) % (12 * m + 6))) ↔
      (a % 6 = 1 ∨ a % 6 = 4 ∨ a % 6 = 5 ∨ a = 6 * m + 2) := by
  rw [p2m_idx2 m a ha]
  have hN : (12 * m + 6) / 2 = 6 * m + 3 := by omega
  rw [hN] at ha
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 6 ∧ a = 6 * k + r :=
    ⟨a / 6, a % 6, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod a 6).symm⟩
  interval_cases r
  · -- r = 0
    have i1 : (2 * (6 * k + 0) + 5) % (12 * m + 6) = 12 * k + 5 := Nat.mod_eq_of_lt (by omega) |>.trans (by omega)
    rw [i1, p2m_lf, p2m_lf (12 * k + 5)]
    simp only [show 2 * (6 * k + 0) % 12 = 0 by omega, show (12 * k + 5) % 12 = 5 by omega]
    refine ⟨fun h => absurd h ?_, fun h => absurd h (by omega)⟩
    norm_num
    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2) (by omega) (by omega)
  · -- r = 1
    rcases Nat.lt_or_ge k m with hk | hk
    · have i1 : (2 * (6 * k + 1) + 5) % (12 * m + 6) = 12 * k + 7 := Nat.mod_eq_of_lt (by omega) |>.trans (by omega)
      rw [i1, p2m_lf, p2m_lf (12 * k + 7)]
      simp only [show 2 * (6 * k + 1) % 12 = 2 by omega, show (12 * k + 7) % 12 = 7 by omega]
      norm_num
      rw [show 12 * k + 7 + 4 = (2 * (6 * k + 1) + 3) + 6 by ring]
      apply p2m_cop_add
      rw [show (6 : ℕ) = 2 * 3 by norm_num]
      apply Nat.Coprime.mul_right
      · exact Nat.coprime_two_right.mpr ⟨6 * k + 2, by ring⟩
      · exact p2m_cop3 _ (by omega)
    · have hkm : k = m := by omega
      subst hkm
      have i1 : (2 * (6 * k + 1) + 5) % (12 * k + 6) = 1 := by
        rw [show 2 * (6 * k + 1) + 5 = 1 + (12 * k + 6) by ring, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [i1, p2m_lf, p2m_lf 1]
      simp only [show 2 * (6 * k + 1) % 12 = 2 by omega]
      norm_num
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ⟨6 * k + 2, by ring⟩)
  · -- r = 2
    rcases Nat.lt_or_ge k m with hk | hk
    · have i1 : (2 * (6 * k + 2) + 5) % (12 * m + 6) = 12 * k + 9 := Nat.mod_eq_of_lt (by omega) |>.trans (by omega)
      rw [i1, p2m_lf, p2m_lf (12 * k + 9)]
      simp only [show 2 * (6 * k + 2) % 12 = 4 by omega, show (12 * k + 9) % 12 = 9 by omega]
      refine ⟨fun h => absurd h ?_, fun h => absurd h (by omega)⟩
      norm_num
      exact Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3) (by omega) (by omega)
    · have hkm : k = m := by omega
      subst hkm
      have i1 : (2 * (6 * k + 2) + 5) % (12 * k + 6) = 3 := by
        rw [show 2 * (6 * k + 2) + 5 = 3 + (12 * k + 6) by ring, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [i1, p2m_lf 3]
      norm_num
  · -- r = 3
    have i1 : (2 * (6 * k + 3) + 5) % (12 * m + 6) = 12 * k + 11 := Nat.mod_eq_of_lt (by omega) |>.trans (by omega)
    rw [i1, p2m_lf, p2m_lf (12 * k + 11)]
    simp only [show 2 * (6 * k + 3) % 12 = 6 by omega, show (12 * k + 11) % 12 = 11 by omega]
    refine ⟨fun h => absurd h ?_, fun h => absurd h (by omega)⟩
    norm_num
    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 2) (by omega) (by omega)
  · -- r = 4
    have i1 : (2 * (6 * k + 4) + 5) % (12 * m + 6) = 12 * k + 13 := Nat.mod_eq_of_lt (by omega) |>.trans (by omega)
    rw [i1, p2m_lf, p2m_lf (12 * k + 13)]
    simp only [show 2 * (6 * k + 4) % 12 = 8 by omega, show (12 * k + 13) % 12 = 1 by omega]
    norm_num
    rw [show 12 * k + 13 + 3 = (2 * (6 * k + 4) - 1) + 9 by omega]
    apply p2m_cop_add
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (p2m_cop3 _ (by omega))
  · -- r = 5
    have i1 : (2 * (6 * k + 5) + 5) % (12 * m + 6) = 12 * k + 15 := Nat.mod_eq_of_lt (by omega) |>.trans (by omega)
    rw [i1, p2m_lf, p2m_lf (12 * k + 15)]
    simp only [show 2 * (6 * k + 5) % 12 = 10 by omega, show (12 * k + 15) % 12 = 3 by omega]
    norm_num
    rw [show 12 * k + 15 - 2 = (2 * (6 * k + 5) + 2) + 1 by omega]
    apply p2m_cop_add
    exact Nat.coprime_one_right _

theorem p2m_cnt_fin (N : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (Finset.univ.filter fun j : Fin N => q j.val).card = ((Finset.range N).filter q).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if q i then 1 else 0) N

theorem p2m_cnt_step (k : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    ((Finset.range (6 * (k + 1) + 3)).filter q).card =
      ((Finset.range (6 * k + 3)).filter q).card +
      ((if q (6 * k + 3) then 1 else 0) + (if q (6 * k + 4) then 1 else 0) +
       (if q (6 * k + 5) then 1 else 0) + (if q (6 * k + 6) then 1 else 0) +
       (if q (6 * k + 7) then 1 else 0) + (if q (6 * k + 8) then 1 else 0)) := by
  rw [Finset.card_filter, Finset.card_filter,
    show 6 * (k + 1) + 3 = 6 * k + 3 + 1 + 1 + 1 + 1 + 1 + 1 by ring]
  simp only [Finset.sum_range_succ]
  ring_nf

theorem KnodelPrimeCordial.case_mod_6_offset_2_residue_assembly__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6)
    (h0 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 0 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = 0)
    (h1 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 1 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = n / 12 + 1)
    (h2 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 2 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = 1)
    (h3 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 3 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = 0)
    (h4 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 4 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = n / 12)
    (h5 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 5 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = n / 12) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card =
      (n + 2) / 4 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun j : Fin (n / 2) => j.val % 6) (t := Finset.range 6)
    (fun j _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.filter_filter]
  have e : ∀ r : ℕ, (Finset.univ.filter fun j : Fin (n / 2) =>
      Nat.Coprime (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n)) ∧ j.val % 6 = r) =
      (Finset.univ.filter fun j : Fin (n / 2) => j.val % 6 = r ∧
      Nat.Coprime (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))) := by
    intro r; apply Finset.filter_congr; intro j _; exact and_comm
  rw [e 0, e 1, e 2, e 3, e 4, e 5, h0, h1, h2, h3, h4, h5]
  omega

theorem solution
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6)
    (h0 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 0 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = 0)
    (h1 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 1 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = n / 12 + 1)
    (h2 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 2 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = 1)
    (h3 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 3 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = 0)
    (h4 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 4 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = n / 12)
    (h5 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 5 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = n / 12) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card =
      (n + 2) / 4 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun j : Fin (n / 2) => j.val % 6) (t := Finset.range 6)
    (fun j _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num)))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.filter_filter]
  have e : ∀ r : ℕ, (Finset.univ.filter fun j : Fin (n / 2) =>
      Nat.Coprime (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n)) ∧ j.val % 6 = r) =
      (Finset.univ.filter fun j : Fin (n / 2) => j.val % 6 = r ∧
      Nat.Coprime (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))) := by
    intro r; apply Finset.filter_congr; intro j _; exact and_comm
  rw [e 0, e 1, e 2, e 3, e 4, e 5, h0, h1, h2, h3, h4, h5]
  omega
