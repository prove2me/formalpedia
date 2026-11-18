-- Prove2me | solution 2 for KnodelPrimeCordial.case_mod_0__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T03:19:33.452426+00:00
-- url     : https://prove2.me/submissions/cc1fbf80-f1ed-44d3-935a-803ef2129fd1

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_labelF_cyc_bijective_mod0
import Theorems.Thm_KnodelPrimeCordial_cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel

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

lemma cyc_res (n i : ℕ) (h12 : 12 ∣ n) (hi : i < n) :
    1 < Nat.gcd (labelF i) (labelF ((i + 1) % n)) ↔
      (i % 12 = 0 ∨ i % 12 = 4 ∨ i % 12 = 5 ∨ i % 12 = 9 ∨ i % 12 = 10 ∨ i % 12 = 11) := by
  have h1 := lf i
  rcases Nat.lt_or_ge (i + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h]
    have h2 := lf (i + 1)
    have : i % 12 < 12 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : i % 12 = 0 ∨ i % 12 = 1 ∨ i % 12 = 2 ∨ i % 12 = 3 ∨ i % 12 = 4 ∨
      i % 12 = 5 ∨ i % 12 = 6 ∨ i % 12 = 7 ∨ i % 12 = 8 ∨ i % 12 = 9 ∨ i % 12 = 10 ∨
      i % 12 = 11) with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
    all_goals (
      first
        | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by omega)
        | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by omega))
  · have hin : i + 1 = n := by omega
    rw [hin, Nat.mod_self]
    have h2 := lf 0
    first
      | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by omega)
      | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by omega)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
      | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
      | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
      | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by omega)

lemma chord_res (n j : ℕ) (h12 : 12 ∣ n) (hj : j < n / 2) :
    1 < Nat.gcd (labelF (2 * j)) (labelF ((2 * j + 5) % n)) ↔
      (j % 6 = 0 ∨ j % 6 = 2 ∨ j % 6 = 3) := by
  have h1 := lf (2 * j)
  rcases Nat.lt_or_ge (2 * j + 5) n with h | h
  · rw [Nat.mod_eq_of_lt h]
    have h2 := lf (2 * j + 5)
    have : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨
      j % 6 = 5) with hr | hr | hr | hr | hr | hr
    all_goals (
      first
        | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by omega)
        | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by omega))
  · have hk : (2 * j + 5) % n = 2 * j + 5 - n := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (show 2 * j + 5 - n < n by omega)]
    rw [hk]
    have h2 := lf (2 * j + 5 - n)
    rcases (by omega : 2 * j = n - 4 ∨ 2 * j = n - 2) with hr | hr
    all_goals (
      first
        | exact iff_of_true (L0 _ _ 2 (by norm_num) (by omega) (by omega) (by omega)) (by omega)
        | exact iff_of_true (L0 _ _ 3 (by norm_num) (by omega) (by omega) (by omega)) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 2 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 3 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 6 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1 _ _ 9 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 1 (by omega) (by norm_num) (by omega) (by omega))) (by omega)
        | exact iff_of_false (not_lt.mpr (L1b _ _ 4 (by omega) (by norm_num) (by omega) (by omega))) (by omega))


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

lemma phi_mem (n : ℕ) (hn : 12 ≤ n) (x : Fin n ⊕ Fin (n / 2)) :
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

lemma phi_inj (n : ℕ) (hn : 12 ≤ n) (h2 : 2 ∣ n) (x y : Fin n ⊕ Fin (n / 2))
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

lemma phi_surj (n : ℕ) (hn : 12 ≤ n) (h2 : 2 ∣ n) (e : Sym2 (Fin n))
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

lemma card_edges_filter (n : ℕ) (hn : 12 ≤ n) (h2 : 2 ∣ n) (q : Sym2 (Fin n) → Prop)
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

lemma split_count (n : ℕ) (hn : 12 ≤ n) (h2 : 2 ∣ n) (q : ℕ → ℕ → Prop) [∀ a, DecidablePred (q a)] :
    ((cyc n).edgeFinset.filter
        (fun e => q 0 (edgeGcd (fun i : Fin n => labelF i.val) e))).card =
      ((Finset.range n).filter
          (fun i => q 0 (Nat.gcd (labelF i) (labelF ((i + 1) % n))))).card +
      ((Finset.range (n / 2)).filter
          (fun j => q 0 (Nat.gcd (labelF (2 * j)) (labelF ((2 * j + 5) % n))))).card := by
  rw [card_edges_filter n hn h2, Finset.card_filter, Fintype.sum_sum_type,
    Finset.card_filter, Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun i => if q 0 (Nat.gcd (labelF i) (labelF ((i + 1) % n)))
      then 1 else 0) n,
    ← Fin.sum_univ_eq_sum_range (fun j => if q 0 (Nat.gcd (labelF (2 * j))
      (labelF ((2 * j + 5) % n))) then 1 else 0) (n / 2)]
  rfl

lemma zero_count (n : ℕ) (hn : 0 < n) (h12 : 12 ∣ n) :
    (edgesLabelZero (cyc n) (fun i : Fin n => labelF i.val)).card = 3 * n / 4 := by
  obtain ⟨k, rfl⟩ := h12
  have hk : 0 < k := by omega
  unfold edgesLabelZero
  have := split_count (12 * k) (by omega) ⟨6 * k, by ring⟩ (fun _ g => 1 < g)
  rw [this]
  have e1 : ((Finset.range (12 * k)).filter
      (fun i => 1 < Nat.gcd (labelF i) (labelF ((i + 1) % (12 * k))))) =
      (Finset.range (12 * k)).filter (fun i => Qc (i % 12)) := by
    apply Finset.filter_congr
    intro i hi
    rw [Finset.mem_range] at hi
    rw [cyc_res (12 * k) i ⟨k, rfl⟩ hi]; rfl
  have e2 : ((Finset.range (12 * k / 2)).filter
      (fun j => 1 < Nat.gcd (labelF (2 * j)) (labelF ((2 * j + 5) % (12 * k))))) =
      (Finset.range (6 * k)).filter (fun j => Qh (j % 6)) := by
    rw [show 12 * k / 2 = 6 * k by omega]
    apply Finset.filter_congr
    intro j hj
    rw [Finset.mem_range] at hj
    rw [chord_res (12 * k) j ⟨k, rfl⟩ (by omega)]; rfl
  rw [e1, e2, ← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range,
    count_period, count_period]
  have c1 : Nat.count (fun i => Qc (i % 12)) 12 = 6 := by decide
  have c2 : Nat.count (fun i => Qh (i % 6)) 6 = 3 := by decide
  rw [c1, c2]; omega

lemma one_count (n : ℕ) (hn : 0 < n) (h12 : 12 ∣ n) :
    (edgesLabelOne (cyc n) (fun i : Fin n => labelF i.val)).card = 3 * n / 4 := by
  obtain ⟨k, rfl⟩ := h12
  have hk : 0 < k := by omega
  unfold edgesLabelOne
  have := split_count (12 * k) (by omega) ⟨6 * k, by ring⟩ (fun _ g => g = 1)
  rw [this]
  have e1 : ((Finset.range (12 * k)).filter
      (fun i => Nat.gcd (labelF i) (labelF ((i + 1) % (12 * k))) = 1)) =
      (Finset.range (12 * k)).filter (fun i => ¬ Qc (i % 12)) := by
    apply Finset.filter_congr
    intro i hi
    rw [Finset.mem_range] at hi
    have h0 := Nat.gcd_pos_of_pos_left (labelF ((i + 1) % (12 * k))) (lf_pos i)
    have := cyc_res (12 * k) i ⟨k, rfl⟩ hi
    unfold Qc
    constructor
    · intro h; rw [← this, h]; omega
    · intro h; rw [← this] at h; omega
  have e2 : ((Finset.range (12 * k / 2)).filter
      (fun j => Nat.gcd (labelF (2 * j)) (labelF ((2 * j + 5) % (12 * k))) = 1)) =
      (Finset.range (6 * k)).filter (fun j => ¬ Qh (j % 6)) := by
    rw [show 12 * k / 2 = 6 * k by omega]
    apply Finset.filter_congr
    intro j hj
    rw [Finset.mem_range] at hj
    have h0 := Nat.gcd_pos_of_pos_left (labelF ((2 * j + 5) % (12 * k))) (lf_pos (2 * j))
    have := chord_res (12 * k) j ⟨k, rfl⟩ (by omega)
    unfold Qh
    constructor
    · intro h; rw [← this, h]; omega
    · intro h; rw [← this] at h; omega
  rw [e1, e2, ← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range,
    count_period (fun r => ¬ Qc r), count_period (fun r => ¬ Qh r)]
  have c1 : Nat.count (fun i => ¬ Qc (i % 12)) 12 = 6 := by decide
  have c2 : Nat.count (fun i => ¬ Qh (i % 6)) 6 = 3 := by decide
  rw [c1, c2]; omega

lemma cordial (n : ℕ) (hn : 0 < n) (h12 : 12 ∣ n) :
    IsPrimeCordialLabeling (cyc n) (fun i : Fin n => labelF i.val) := by
  refine ⟨?_, ?_⟩
  · rw [Fintype.card_fin]
    exact KnodelPrimeCordial.labelF_cyc_bijective_mod0 n hn h12
  · rw [zero_count n hn h12, one_count n hn h12]
    simp

end KnAux


theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 0) :
    KnodelPrimeCordial.PrimeCordial (KnodelPrimeCordial.knodel 3 n) := by
  have h12 : 12 ∣ n := Nat.dvd_of_mod_eq_zero hmod
  exact KnodelPrimeCordial.cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
    n hn h10 _ (KnAux.cordial n (by omega) h12)
