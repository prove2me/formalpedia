-- Prove2me | solution 2 for KnodelPrimeCordial.cyclic_case_mod_10_edge_balance__p2m_274a48da_4cfb_4ff4_bf18_08c4c347ae66_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T03:32:39.423194+00:00
-- url     : https://prove2.me/submissions/251315b4-b9c3-415e-8816-a2523df939d9

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

namespace KnAux
open KnodelPrimeCordial

lemma lf (i : ℕ) :
    (i % 12 = 0 ∧ labelF i = i + 2) ∨ (i % 12 = 1 ∧ labelF i = i + 3) ∨
    (i % 12 = 2 ∧ labelF i = i + 3) ∨ (i % 12 = 3 ∧ labelF i = i - 2) ∨
    (i % 12 = 4 ∧ labelF i = i - 1) ∨ (i % 12 = 5 ∧ labelF i = i + 1) ∨
    (i % 12 = 6 ∧ labelF i = i + 2) ∨ (i % 12 = 7 ∧ labelF i = i + 4) ∨
    (i % 12 = 8 ∧ labelF i = i - 1) ∨ (i % 12 = 9 ∧ labelF i = i) ∨
    (i % 12 = 10 ∧ labelF i = i + 2) ∨ (i % 12 = 11 ∧ labelF i = i - 1) := by
  have hlt := Nat.mod_lt i (show 0 < 12 by norm_num)
  unfold labelF
  interval_cases h : i % 12 <;> simp

lemma L0 (a b p : ℕ) (hp : 2 ≤ p) (ha : p ∣ a) (hb : p ∣ b) (hb0 : 0 < b) :
    1 < Nat.gcd a b :=
  lt_of_lt_of_le (by omega) (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ hb0) (Nat.dvd_gcd ha hb))

lemma L1 (a b d : ℕ) (hab : b = a + d ∨ a = b + d) (hd : d ∣ 36)
    (h2 : ¬ (2 ∣ a ∧ 2 ∣ b)) (h3 : ¬ (3 ∣ a ∧ 3 ∣ b)) : Nat.gcd a b ≤ 1 := by
  by_contra hc
  have hg : Nat.gcd a b ≠ 1 := by omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
  have hpa : p ∣ a := hpd.trans (Nat.gcd_dvd_left a b)
  have hpb : p ∣ b := hpd.trans (Nat.gcd_dvd_right a b)
  have hpdd : p ∣ d := by
    rcases hab with h | h
    · rw [h] at hpb; exact (Nat.dvd_add_right hpa).mp hpb
    · rw [h] at hpa; exact (Nat.dvd_add_right hpb).mp hpa
  have h36 : p ∣ 2 ^ 2 * 3 ^ 2 := hpdd.trans hd
  rcases (Nat.Prime.dvd_mul hp).mp h36 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    subst this; exact h2 ⟨hpa, hpb⟩
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
    subst this; exact h3 ⟨hpa, hpb⟩

lemma L1b (a b c : ℕ) (hbc : b = c) (hc : c ∣ 36)
    (h2 : ¬ (2 ∣ a ∧ 2 ∣ b)) (h3 : ¬ (3 ∣ a ∧ 3 ∣ b)) : Nat.gcd a b ≤ 1 := by
  by_contra hcon
  have hg : Nat.gcd a b ≠ 1 := by omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
  have hpa : p ∣ a := hpd.trans (Nat.gcd_dvd_left a b)
  have hpb : p ∣ b := hpd.trans (Nat.gcd_dvd_right a b)
  have h36 : p ∣ 2 ^ 2 * 3 ^ 2 := (hbc ▸ hpb).trans hc
  rcases (Nat.Prime.dvd_mul hp).mp h36 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    subst this; exact h2 ⟨hpa, hpb⟩
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
    subst this; exact h3 ⟨hpa, hpb⟩

lemma lf_pos (i : ℕ) : 0 < labelF i := by have := lf i; omega

def Qc (r : ℕ) : Prop := r = 0 ∨ r = 4 ∨ r = 5 ∨ r = 9 ∨ r = 10 ∨ r = 11
def Qh (r : ℕ) : Prop := r = 0 ∨ r = 2 ∨ r = 3
instance : DecidablePred Qc := fun r => by unfold Qc; infer_instance
instance : DecidablePred Qh := fun r => by unfold Qh; infer_instance

lemma count_period (Q : ℕ → Prop) [DecidablePred Q] (p k : ℕ) :
    Nat.count (fun i => Q (i % p)) (p * k) = k * Nat.count (fun i => Q (i % p)) p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.count_add, ih]
    have : (fun j => Q ((p * k + j) % p)) = (fun j => Q (j % p)) := by
      funext j; rw [Nat.mul_add_mod]
    simp only [this]
    ring

lemma modfact (x n : ℕ) (hx : x < 2 * n) :
    (x < n ∧ x % n = x) ∨ (n ≤ x ∧ x % n = x - n) := by
  rcases Nat.lt_or_ge x n with h | h
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · right; refine ⟨h, ?_⟩
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

def phi (n : ℕ) (hn : 0 < n) : Fin n ⊕ Fin (n / 2) → Sym2 (Fin n)
  | Sum.inl i => s(i, ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)
  | Sum.inr j => s(⟨2 * j.val, by omega⟩, ⟨(2 * j.val + 5) % n, Nat.mod_lt _ hn⟩)

lemma phi_mem (n : ℕ) (hn : 10 ≤ n) (x : Fin n ⊕ Fin (n / 2)) :
    phi n (by omega) x ∈ (cyc n).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  rcases x with i | j
  · simp only [phi, SimpleGraph.mem_edgeSet]
    refine ⟨fun h => ?_, Or.inl rfl⟩
    have hv := congrArg Fin.val h
    simp only at hv
    clear h
    have := modfact (i.val + 1) n (by omega)
    have := i.isLt
    generalize (i.val + 1) % n = k at *
    omega
  · simp only [phi, SimpleGraph.mem_edgeSet]
    refine ⟨fun h => ?_, Or.inr (Or.inr (Or.inl ⟨even_two_mul _, rfl⟩))⟩
    have hv := congrArg Fin.val h
    simp only at hv
    clear h
    have := modfact (2 * j.val + 5) n (by omega)
    have := j.isLt
    generalize (2 * j.val + 5) % n = k at *
    omega

lemma phi_inj (n : ℕ) (hn : 10 ≤ n) (h2 : 2 ∣ n) (x y : Fin n ⊕ Fin (n / 2))
    (h : phi n (by omega) x = phi n (by omega) y) : x = y := by
  rcases x with i | j <;> rcases y with i' | j' <;>
    simp only [phi, Sym2.eq_iff, Fin.ext_iff] at h
  · have h1 := modfact (i.val + 1) n (by omega)
    have h2 := modfact (i'.val + 1) n (by omega)
    have := i.isLt; have := i'.isLt
    generalize (i.val + 1) % n = k at *
    generalize (i'.val + 1) % n = k' at *
    congr 1; ext; omega
  · have h1 := modfact (i.val + 1) n (by omega)
    have h2 := modfact (2 * j'.val + 5) n (by omega)
    have := i.isLt; have := j'.isLt
    generalize (i.val + 1) % n = k at *
    generalize (2 * j'.val + 5) % n = k' at *
    exfalso; omega
  · have h1 := modfact (i'.val + 1) n (by omega)
    have h2 := modfact (2 * j.val + 5) n (by omega)
    have := i'.isLt; have := j.isLt
    generalize (i'.val + 1) % n = k at *
    generalize (2 * j.val + 5) % n = k' at *
    exfalso; omega
  · have h1 := modfact (2 * j.val + 5) n (by omega)
    have h2 := modfact (2 * j'.val + 5) n (by omega)
    have := j.isLt; have := j'.isLt
    generalize (2 * j.val + 5) % n = k at *
    generalize (2 * j'.val + 5) % n = k' at *
    congr 1; ext; omega

lemma phi_surj (n : ℕ) (hn : 10 ≤ n) (h2 : 2 ∣ n) (e : Sym2 (Fin n))
    (he : e ∈ (cyc n).edgeFinset) : ∃ x, phi n (by omega) x = e := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    obtain ⟨_, h | h | ⟨hev, h⟩ | ⟨hev, h⟩⟩ := he
    · exact ⟨Sum.inl a, by simp only [phi]; congr 1; ext; exact h.symm⟩
    · refine ⟨Sum.inl b, ?_⟩
      simp only [phi]; rw [Sym2.eq_swap]; congr 1; ext; exact h.symm
    · obtain ⟨r, hr⟩ := hev
      refine ⟨Sum.inr ⟨r, by have := a.isLt; omega⟩, ?_⟩
      simp only [phi]; congr 1
      · ext; simp only; omega
      · ext; simp only; rw [h]; congr 1; omega
    · obtain ⟨r, hr⟩ := hev
      refine ⟨Sum.inr ⟨r, by have := b.isLt; omega⟩, ?_⟩
      simp only [phi]; rw [Sym2.eq_swap]; congr 1
      · ext; simp only; rw [h]; congr 1; omega
      · ext; simp only; omega

lemma card_edges_filter (n : ℕ) (hn : 10 ≤ n) (h2 : 2 ∣ n) (q : Sym2 (Fin n) → Prop)
    [DecidablePred q] :
    ((cyc n).edgeFinset.filter q).card =
      (Finset.univ.filter (fun x => q (phi n (by omega) x))).card := by
  symm
  apply Finset.card_bij (fun x _ => phi n (by omega) x)
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨phi_mem n hn x, hx.2⟩
  · intro x _ y _ h
    exact phi_inj n hn h2 x y h
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨x, hx⟩ := phi_surj n hn h2 e he.1
    exact ⟨x, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx ▸ he.2⟩, hx⟩

lemma split_count (n : ℕ) (hn : 10 ≤ n) (h2 : 2 ∣ n) (q : ℕ → ℕ → Prop) [∀ a, DecidablePred (q a)] (F : ℕ → ℕ) :
    ((cyc n).edgeFinset.filter
        (fun e => q 0 (edgeGcd (fun i : Fin n => F i.val) e))).card =
      ((Finset.range n).filter
          (fun i => q 0 (Nat.gcd (F i) (F ((i + 1) % n))))).card +
      ((Finset.range (n / 2)).filter
          (fun j => q 0 (Nat.gcd (F (2 * j)) (F ((2 * j + 5) % n))))).card := by
  rw [card_edges_filter n hn h2, Finset.card_filter, Fintype.sum_sum_type,
    Finset.card_filter, Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun i => if q 0 (Nat.gcd (F i) (F ((i + 1) % n)))
      then 1 else 0) n,
    ← Fin.sum_univ_eq_sum_range (fun j => if q 0 (Nat.gcd (F (2 * j))
      (F ((2 * j + 5) % n))) then 1 else 0) (n / 2)]
  rfl


def G (n i : ℕ) : ℕ := if i = n - 3 then i + 3 else labelF i

lemma G_pos (n i : ℕ) : 0 < G n i := by
  unfold G; split_ifs
  · omega
  · exact lf_pos i

lemma cyc_core (i : ℕ) :
    1 < Nat.gcd (labelF i) (labelF (i + 1)) ↔ Qc (i % 12) := by
  unfold Qc
  have h1 := lf i
  have h2 := lf (i + 1)
  have : i % 12 < 12 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : i % 12 = 0 ∨ i % 12 = 1 ∨ i % 12 = 2 ∨ i % 12 = 3 ∨ i % 12 = 4 ∨
    i % 12 = 5 ∨ i % 12 = 6 ∨ i % 12 = 7 ∨ i % 12 = 8 ∨ i % 12 = 9 ∨ i % 12 = 10 ∨
    i % 12 = 11) with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  all_goals (
    first
      | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
      | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1b _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1b _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp))

lemma chord_core (j : ℕ) :
    1 < Nat.gcd (labelF (2 * j)) (labelF (2 * j + 5)) ↔ Qh (j % 6) := by
  unfold Qh
  have h1 := lf (2 * j)
  have h2 := lf (2 * j + 5)
  have : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨
    j % 6 = 5) with hr | hr | hr | hr | hr | hr
  all_goals (
    first
      | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
      | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1b _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
      | exact iff_of_false (not_lt.mpr (L1b _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp))

def tv : ℕ → ℕ
  | 0 => 2 | 1 => 4 | 2 => 5 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 8 | 7 => 11
  | 8 => 7 | 9 => 9 | 10 => 12 | _ => 10

lemma lf_eq (m r : ℕ) (hr : r < 12) : labelF (12 * m + r) = 12 * m + tv r := by
  have := lf (12 * m + r)
  interval_cases r <;> simp only [tv] <;> omega

lemma tail_cyc (k t : ℕ) (ht : t < 10) :
    1 < Nat.gcd (G (12 * k + 10) (12 * k + t)) (G (12 * k + 10) ((12 * k + t + 1) % (12 * k + 10))) ↔
      (t = 0 ∨ t = 4 ∨ t = 5 ∨ t = 6) := by
  have hm : (12 * k + t + 1) % (12 * k + 10) = if t = 9 then 0 else 12 * k + (t + 1) := by
    split_ifs with h9
    · subst h9; rw [show 12 * k + 9 + 1 = 12 * k + 10 by ring]; exact Nat.mod_self _
    · exact Nat.mod_eq_of_lt (by omega)
  have l0 : labelF 0 = 2 := by decide
  rcases (by omega : t < 9 ∨ t = 9) with h9 | h9
  · rw [hm, if_neg (by omega)]
    interval_cases t
    all_goals (
      simp only [G]
      split_ifs
      all_goals (
        try simp only [lf_eq k _ (by norm_num : (0:ℕ) < 12), lf_eq k _ (by norm_num : (1:ℕ) < 12),
          lf_eq k _ (by norm_num : (2:ℕ) < 12), lf_eq k _ (by norm_num : (3:ℕ) < 12),
          lf_eq k _ (by norm_num : (4:ℕ) < 12), lf_eq k _ (by norm_num : (5:ℕ) < 12),
          lf_eq k _ (by norm_num : (6:ℕ) < 12), lf_eq k _ (by norm_num : (7:ℕ) < 12),
          lf_eq k _ (by norm_num : (8:ℕ) < 12), lf_eq k _ (by norm_num : (9:ℕ) < 12),
          lf_eq k _ (by norm_num : (10:ℕ) < 12), tv]
        first
          | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
          | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
          | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
          | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
          | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
          | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
          | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
          | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
          | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
          | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
          | exact iff_of_false (not_lt.mpr (L1b _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
          | exact iff_of_false (not_lt.mpr (L1b _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
          | (exfalso; omega)))
  · subst h9
    rw [hm, if_pos rfl]
    simp only [G]
    split_ifs
    all_goals (
      try simp only [lf_eq k _ (by norm_num : (9:ℕ) < 12), l0, tv]
      first
        | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
        | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | (exfalso; omega))

lemma tail_ch (k t : ℕ) (ht : t < 5) (h1 : t ≠ 1) :
    1 < Nat.gcd (G (12 * k + 10) (2 * (6 * k + t)))
      (G (12 * k + 10) ((2 * (6 * k + t) + 5) % (12 * k + 10))) ↔ (t = 0 ∨ t = 2 ∨ t = 3) := by
  have l1 : labelF 1 = 4 := by decide
  have l3 : labelF 3 = 1 := by decide
  interval_cases t
  · rw [show 2 * (6 * k + 0) = 12 * k + 0 by ring,
      show (12 * k + 0 + 5) % (12 * k + 10) = 12 * k + 5 from
        Nat.mod_eq_of_lt (show 12 * k + 0 + 5 < 12 * k + 10 by omega)]
    simp only [G]
    split_ifs
    all_goals (
      try simp only [lf_eq k _ (by norm_num : (0:ℕ) < 12), lf_eq k _ (by norm_num : (5:ℕ) < 12), tv]
      first
        | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
        | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | (exfalso; omega))
  · exact absurd rfl h1
  · rw [show 2 * (6 * k + 2) = 12 * k + 4 by ring,
      show (12 * k + 4 + 5) % (12 * k + 10) = 12 * k + 9 from
        Nat.mod_eq_of_lt (show 12 * k + 4 + 5 < 12 * k + 10 by omega)]
    simp only [G]
    split_ifs
    all_goals (
      try simp only [lf_eq k _ (by norm_num : (4:ℕ) < 12), lf_eq k _ (by norm_num : (9:ℕ) < 12), tv]
      first
        | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
        | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | (exfalso; omega))
  · rw [show 2 * (6 * k + 3) = 12 * k + 6 by ring,
      show (12 * k + 6 + 5) % (12 * k + 10) = 1 by
        rw [show 12 * k + 6 + 5 = 1 + (12 * k + 10) by ring, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (show 1 < 12 * k + 10 by omega)]
    simp only [G]
    split_ifs
    all_goals (
      try simp only [lf_eq k _ (by norm_num : (6:ℕ) < 12), l1, tv]
      first
        | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
        | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | (exfalso; omega))
  · rw [show 2 * (6 * k + 4) = 12 * k + 8 by ring,
      show (12 * k + 8 + 5) % (12 * k + 10) = 3 by
        rw [show 12 * k + 8 + 5 = 3 + (12 * k + 10) by ring, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (show 3 < 12 * k + 10 by omega)]
    simp only [G]
    split_ifs
    all_goals (
      try simp only [lf_eq k _ (by norm_num : (8:ℕ) < 12), l3, tv]
      first
        | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
        | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by first | omega | simp)
        | (exfalso; omega))

lemma count_congr' (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q] (m : ℕ)
    (h : ∀ i < m, (p i ↔ q i)) : Nat.count p m = Nat.count q m := by
  simp only [Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact h i (Finset.mem_range.mp hi)

lemma cyc_count (k : ℕ) :
    Nat.count (fun i => 1 < Nat.gcd (G (12 * k + 10) i) (G (12 * k + 10) ((i + 1) % (12 * k + 10))))
      (12 * k + 10) = 6 * k + 4 := by
  rw [Nat.count_add]
  have e1 := count_congr' (fun i => 1 < Nat.gcd (G (12 * k + 10) i)
      (G (12 * k + 10) ((i + 1) % (12 * k + 10)))) (fun i => Qc (i % 12)) (12 * k) (by
    intro i hi
    rw [Nat.mod_eq_of_lt (show i + 1 < 12 * k + 10 by omega)]
    simp only [G, if_neg (show i ≠ 12 * k + 10 - 3 by omega),
      if_neg (show i + 1 ≠ 12 * k + 10 - 3 by omega)]
    exact cyc_core i)
  have e2 := count_congr' (fun t => 1 < Nat.gcd (G (12 * k + 10) (12 * k + t))
      (G (12 * k + 10) ((12 * k + t + 1) % (12 * k + 10))))
      (fun t => t = 0 ∨ t = 4 ∨ t = 5 ∨ t = 6) 10 (fun t ht => tail_cyc k t ht)
  rw [e1, e2, count_period]
  have c1 : Nat.count (fun i => Qc (i % 12)) 12 = 6 := by decide
  have c2 : Nat.count (fun t => t = 0 ∨ t = 4 ∨ t = 5 ∨ t = 6) 10 = 4 := by decide
  rw [c1, c2]; ring

lemma ch_count (k : ℕ) :
    Nat.count (fun j => 1 < Nat.gcd (G (12 * k + 10) (2 * j))
      (G (12 * k + 10) ((2 * j + 5) % (12 * k + 10)))) (6 * k + 5) = 3 * k + 3 ∨
    Nat.count (fun j => 1 < Nat.gcd (G (12 * k + 10) (2 * j))
      (G (12 * k + 10) ((2 * j + 5) % (12 * k + 10)))) (6 * k + 5) = 3 * k + 4 := by
  rw [Nat.count_add]
  have e1 := count_congr' (fun j => 1 < Nat.gcd (G (12 * k + 10) (2 * j))
      (G (12 * k + 10) ((2 * j + 5) % (12 * k + 10)))) (fun j => Qh (j % 6)) (6 * k) (by
    intro j hj
    rw [Nat.mod_eq_of_lt (show 2 * j + 5 < 12 * k + 10 by omega)]
    simp only [G, if_neg (show 2 * j ≠ 12 * k + 10 - 3 by omega),
      if_neg (show 2 * j + 5 ≠ 12 * k + 10 - 3 by omega)]
    exact chord_core j)
  rw [e1, count_period]
  have c1 : Nat.count (fun i => Qh (i % 6)) 6 = 3 := by decide
  rw [c1]
  simp only [Nat.count_succ, Nat.count_zero]
  rw [if_pos ((tail_ch k 0 (by norm_num) (by norm_num)).mpr (by norm_num)),
    if_pos ((tail_ch k 2 (by norm_num) (by norm_num)).mpr (by norm_num)),
    if_pos ((tail_ch k 3 (by norm_num) (by norm_num)).mpr (by norm_num)),
    if_neg (mt (tail_ch k 4 (by norm_num) (by norm_num)).mp (by omega))]
  split_ifs <;> omega

lemma split10 (k : ℕ) (q : ℕ → ℕ → Prop) [∀ a, DecidablePred (q a)] :
    ((cyc (12 * k + 10)).edgeFinset.filter
        (fun e => q 0 (edgeGcd (fun i : Fin (12 * k + 10) => G (12 * k + 10) i.val) e))).card =
      Nat.count (fun i => q 0 (Nat.gcd (G (12 * k + 10) i)
        (G (12 * k + 10) ((i + 1) % (12 * k + 10))))) (12 * k + 10) +
      Nat.count (fun j => q 0 (Nat.gcd (G (12 * k + 10) (2 * j))
        (G (12 * k + 10) ((2 * j + 5) % (12 * k + 10))))) (6 * k + 5) := by
  rw [split_count (12 * k + 10) (by omega) ⟨6 * k + 5, by ring⟩ q (G (12 * k + 10)),
    Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    show (12 * k + 10) / 2 = 6 * k + 5 by omega]

lemma balance10 (k : ℕ) :
    |((edgesLabelZero (cyc (12 * k + 10))
        (fun i : Fin (12 * k + 10) => G (12 * k + 10) i.val)).card : ℤ) -
      ((edgesLabelOne (cyc (12 * k + 10))
        (fun i : Fin (12 * k + 10) => G (12 * k + 10) i.val)).card : ℤ)| ≤ 1 := by
  unfold edgesLabelZero edgesLabelOne
  rw [split10 k (fun _ g => 1 < g), split10 k (fun _ g => g = 1)]
  have hc := cyc_count k
  have hh := ch_count k
  have n1 : ∀ (p : ℕ → Prop) [DecidablePred p] (m : ℕ),
      Nat.count p m + Nat.count (fun i => ¬ p i) m = m := by
    intro p _ m
    simp only [Nat.count_eq_card_filter_range]
    rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
  have a1 := n1 (fun i => 1 < Nat.gcd (G (12 * k + 10) i)
    (G (12 * k + 10) ((i + 1) % (12 * k + 10)))) (12 * k + 10)
  have a2 := n1 (fun j => 1 < Nat.gcd (G (12 * k + 10) (2 * j))
    (G (12 * k + 10) ((2 * j + 5) % (12 * k + 10)))) (6 * k + 5)
  have b1 : Nat.count (fun i => Nat.gcd (G (12 * k + 10) i)
      (G (12 * k + 10) ((i + 1) % (12 * k + 10))) = 1) (12 * k + 10) =
      Nat.count (fun i => ¬ 1 < Nat.gcd (G (12 * k + 10) i)
      (G (12 * k + 10) ((i + 1) % (12 * k + 10)))) (12 * k + 10) := by
    apply count_congr'
    intro i _
    have := Nat.gcd_pos_of_pos_left (G (12 * k + 10) ((i + 1) % (12 * k + 10))) (G_pos (12 * k + 10) i)
    omega
  have b2 : Nat.count (fun j => Nat.gcd (G (12 * k + 10) (2 * j))
      (G (12 * k + 10) ((2 * j + 5) % (12 * k + 10))) = 1) (6 * k + 5) =
      Nat.count (fun j => ¬ 1 < Nat.gcd (G (12 * k + 10) (2 * j))
      (G (12 * k + 10) ((2 * j + 5) % (12 * k + 10)))) (6 * k + 5) := by
    apply count_congr'
    intro j _
    have := Nat.gcd_pos_of_pos_left (G (12 * k + 10) ((2 * j + 5) % (12 * k + 10))) (G_pos (12 * k + 10) (2 * j))
    omega
  rw [b1, b2]
  rw [abs_le]
  constructor <;> omega

end KnAux

open KnodelPrimeCordial in
theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 10) :
    |((KnodelPrimeCordial.edgesLabelZero (KnodelPrimeCordial.cyc n)
        (fun i : Fin n =>
          if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card : ℤ) -
      ((KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.cyc n)
        (fun i : Fin n =>
          if i.val = n - 3 then i.val + 3 else KnodelPrimeCordial.labelF i.val)).card : ℤ)| ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 12 * k + 10 := ⟨n / 12, by omega⟩
  exact KnAux.balance10 k
