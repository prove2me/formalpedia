-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_2__p2m_be27a6d0_01d1_46f0_b9ba_0d15398f9cfb_a1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T03:54:07.004206+00:00
-- url     : https://prove2.me/submissions/c18248b7-cde6-4385-bc48-8a1ca7dcfb40

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Theorems.Thm_KnodelPrimeCordial_cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2

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

lemma lf_pos (i : ℕ) : 0 < labelF i := by have := lf i; omega

lemma lf_inj (i j : ℕ) (h : labelF i = labelF j) : i = j := by
  have h1 := lf i
  have h2 := lf j
  omega

lemma L0 (a b p : ℕ) (hp : 2 ≤ p) (ha : p ∣ a) (hb : p ∣ b) (hb0 : 0 < a ∨ 0 < b) :
    1 < Nat.gcd a b := by
  have hpos : 0 < Nat.gcd a b := by
    rcases hb0 with h | h
    · exact Nat.gcd_pos_of_pos_left _ h
    · exact Nat.gcd_pos_of_pos_right _ h
  exact lt_of_lt_of_le (by omega) (Nat.le_of_dvd hpos (Nat.dvd_gcd ha hb))

lemma Gdiff (a b d : ℕ) (hab : b = a + d ∨ a = b + d) (hd : d ∣ 36) (hd0 : 0 < d) :
    1 < Nat.gcd a b ↔ ((2 ∣ a ∧ 2 ∣ b) ∨ (3 ∣ a ∧ 3 ∣ b)) := by
  constructor
  · intro hc
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
      subst this; exact Or.inl ⟨hpa, hpb⟩
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
      subst this; exact Or.inr ⟨hpa, hpb⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact L0 a b 2 (by norm_num) h1 h2 (by omega)
    · exact L0 a b 3 (by norm_num) h1 h2 (by omega)

lemma Gs (a b : ℕ) (hb : b ∣ 36) :
    1 < Nat.gcd a b ↔ ((2 ∣ a ∧ 2 ∣ b) ∨ (3 ∣ a ∧ 3 ∣ b)) := by
  have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hb (by norm_num)
  constructor
  · intro hc
    have hg : Nat.gcd a b ≠ 1 := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
    have hpa : p ∣ a := hpd.trans (Nat.gcd_dvd_left a b)
    have hpb : p ∣ b := hpd.trans (Nat.gcd_dvd_right a b)
    have h36 : p ∣ 2 ^ 2 * 3 ^ 2 := hpb.trans hb
    rcases (Nat.Prime.dvd_mul hp).mp h36 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      subst this; exact Or.inl ⟨hpa, hpb⟩
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
      subst this; exact Or.inr ⟨hpa, hpb⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact L0 a b 2 (by norm_num) h1 h2 (Or.inr hb0)
    · exact L0 a b 3 (by norm_num) h1 h2 (Or.inr hb0)

def Qc (r : ℕ) : Prop := r = 0 ∨ r = 4 ∨ r = 5 ∨ r = 9 ∨ r = 10 ∨ r = 11
def Qh (r : ℕ) : Prop := r = 0 ∨ r = 2 ∨ r = 3
instance : DecidablePred Qc := fun r => by unfold Qc; infer_instance
instance : DecidablePred Qh := fun r => by unfold Qh; infer_instance

lemma edge_res (i : ℕ) : 1 < Nat.gcd (labelF i) (labelF (i + 1)) ↔ Qc (i % 12) := by
  have h1 := lf i
  have h2 := lf (i + 1)
  unfold Qc
  have hmod : i % 12 < 12 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : i % 12 = 0 ∨ i % 12 = 1 ∨ i % 12 = 2 ∨ i % 12 = 3 ∨ i % 12 = 4 ∨
      i % 12 = 5 ∨ i % 12 = 6 ∨ i % 12 = 7 ∨ i % 12 = 8 ∨ i % 12 = 9 ∨ i % 12 = 10 ∨
      i % 12 = 11) with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  all_goals (
    first
      | (rw [Gdiff _ _ 1 (by omega) (by norm_num) (by norm_num)]; omega)
      | (rw [Gdiff _ _ 2 (by omega) (by norm_num) (by norm_num)]; omega)
      | (rw [Gdiff _ _ 3 (by omega) (by norm_num) (by norm_num)]; omega)
      | (rw [Gdiff _ _ 4 (by omega) (by norm_num) (by norm_num)]; omega)
      | (rw [Gdiff _ _ 6 (by omega) (by norm_num) (by norm_num)]; omega)
      | (rw [Gdiff _ _ 9 (by omega) (by norm_num) (by norm_num)]; omega))

lemma chord_res (j : ℕ) : 1 < Nat.gcd (labelF (2 * j)) (labelF (2 * j + 5)) ↔ Qh (j % 6) := by
  have h1 := lf (2 * j)
  have h2 := lf (2 * j + 5)
  unfold Qh
  have hmod : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨
      j % 6 = 5) with hr | hr | hr | hr | hr | hr
  all_goals (
    first
      | (rw [Gdiff _ _ 1 (by omega) (by norm_num) (by norm_num)]; omega)
      | (rw [Gdiff _ _ 2 (by omega) (by norm_num) (by norm_num)]; omega)
      | (rw [Gdiff _ _ 3 (by omega) (by norm_num) (by norm_num)]; omega)
      | (rw [Gdiff _ _ 4 (by omega) (by norm_num) (by norm_num)]; omega)
      | (rw [Gdiff _ _ 6 (by omega) (by norm_num) (by norm_num)]; omega)
      | (rw [Gdiff _ _ 9 (by omega) (by norm_num) (by norm_num)]; omega))

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

lemma count_mod (Q : ℕ → Prop) [DecidablePred Q] (p k s : ℕ) :
    Nat.count (fun i => Q (i % p)) (p * k + s) =
      k * Nat.count (fun i => Q (i % p)) p + Nat.count (fun i => Q (i % p)) s := by
  rw [Nat.count_add, count_period]
  have : (fun j => Q ((p * k + j) % p)) = (fun j => Q (j % p)) := by
    funext j; rw [Nat.mul_add_mod]
  simp only [this]

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

lemma split_count (n : ℕ) (hn : 12 ≤ n) (h2 : 2 ∣ n) (g : ℕ → ℕ) (q : ℕ → Prop)
    [DecidablePred q] :
    ((cyc n).edgeFinset.filter
        (fun e => q (edgeGcd (fun i : Fin n => g i.val) e))).card =
      ((Finset.range n).filter
          (fun i => q (Nat.gcd (g i) (g ((i + 1) % n))))).card +
      ((Finset.range (n / 2)).filter
          (fun j => q (Nat.gcd (g (2 * j)) (g ((2 * j + 5) % n))))).card := by
  rw [card_edges_filter n hn h2, Finset.card_filter, Fintype.sum_sum_type,
    Finset.card_filter, Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun i => if q (Nat.gcd (g i) (g ((i + 1) % n)))
      then 1 else 0) n,
    ← Fin.sum_univ_eq_sum_range (fun j => if q (Nat.gcd (g (2 * j))
      (g ((2 * j + 5) % n))) then 1 else 0) (n / 2)]
  rfl

/-- total edge count -/
lemma card_edges_total (n : ℕ) (hn : 12 ≤ n) (h2 : 2 ∣ n) :
    (cyc n).edgeFinset.card = n + n / 2 := by
  have := card_edges_filter n hn h2 (fun _ => True)
  simp only [Finset.filter_true_of_mem, implies_true] at this
  rw [this]
  simp [Fintype.card_sum]

/-- Zero + One = total, given positivity of labels -/
lemma zero_add_one (n : ℕ) (hn : 12 ≤ n) (h2 : 2 ∣ n) (g : ℕ → ℕ) (hpos : ∀ i, i < n → 0 < g i) :
    (edgesLabelZero (cyc n) (fun i : Fin n => g i.val)).card +
      (edgesLabelOne (cyc n) (fun i : Fin n => g i.val)).card = n + n / 2 := by
  rw [← card_edges_total n hn h2]
  unfold edgesLabelZero edgesLabelOne
  have hc : ((cyc n).edgeFinset.filter (fun e => edgeGcd (fun i : Fin n => g i.val) e = 1)) =
      ((cyc n).edgeFinset.filter (fun e => ¬ 1 < edgeGcd (fun i : Fin n => g i.val) e)) := by
    apply Finset.filter_congr
    intro e _
    induction e using Sym2.ind with
    | _ a b =>
      have h0 : 0 < edgeGcd (fun i : Fin n => g i.val) s(a, b) := by
        show 0 < Nat.gcd (g a.val) (g b.val)
        exact Nat.gcd_pos_of_pos_left _ (hpos a.val a.isLt)
      omega
  rw [hc]
  exact Finset.card_filter_add_card_filter_not _

end KnAux

namespace KnAux

lemma mod_small (x n : ℕ) (h : x < n) : x % n = x := Nat.mod_eq_of_lt h

lemma mod_wrap (x n : ℕ) (h1 : n ≤ x) (h2 : x < 2 * n) : x % n = x - n := by
  rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

lemma count_split (P : ℕ → Prop) [DecidablePred P] (n a b : ℕ) (h : n = a + b) :
    Nat.count P n = Nat.count P a + Nat.count (fun t => P (a + t)) b := by
  subst h; exact Nat.count_add P a b

lemma count_congr' (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q] (m : ℕ)
    (h : ∀ i, i < m → (P i ↔ Q i)) : Nat.count P m = Nat.count Q m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.count_succ, Nat.count_succ, ih (fun i hi => h i (by omega))]
    have := h m (by omega)
    simp only [this]

end KnAux
namespace KnAux
open KnodelPrimeCordial
def g2 (n i : ℕ) : ℕ :=
  if i = n - 3 then n else
  if i = n - 2 then n - 1 else
  if i = n - 1 then n - 4 else
  labelF i


lemma g2_pre (n i : ℕ) (hn : n % 12 = 2) (h : i + 3 < n) : g2 n i = labelF i := by
  unfold g2; split_ifs <;> omega

lemma g2_range (n i : ℕ) (hn : n % 12 = 2) (h : 14 ≤ n) (hi : i < n) :
    1 ≤ g2 n i ∧ g2 n i ≤ n := by
  unfold g2; have := lf i; split_ifs <;> omega

lemma g2_inj (n i j : ℕ) (hn : n % 12 = 2) (h : 14 ≤ n) (hi : i < n) (hj : j < n)
    (hij : g2 n i = g2 n j) : i = j := by
  unfold g2 at hij; have := lf i; have := lf j; split_ifs at hij <;> omega

lemma g2_bij (n : ℕ) (hn : n % 12 = 2) (h : 14 ≤ n) :
    Set.BijOn (fun i : Fin n => g2 n i.val) Set.univ (Set.Icc 1 n) := by
  have hmaps : ∀ i : Fin n, 1 ≤ g2 n i.val ∧ g2 n i.val ≤ n :=
    fun i => g2_range n i.val hn h i.isLt
  have hinj : Function.Injective (fun i : Fin n => g2 n i.val) := by
    intro i j hij
    exact Fin.ext (g2_inj n i.val j.val hn h i.isLt j.isLt hij)
  refine ⟨fun i _ => ?_, hinj.injOn, ?_⟩
  · exact Set.mem_Icc.mpr (hmaps i)
  · have hsub : (Finset.univ.image (fun i : Fin n => g2 n i.val)) ⊆ Finset.Icc 1 n := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨i, _, rfl⟩ := hy
      exact Finset.mem_Icc.mpr (hmaps i)
    have hcard : (Finset.univ.image (fun i : Fin n => g2 n i.val)).card = (Finset.Icc 1 n).card := by
      rw [Finset.card_image_of_injective _ hinj]; simp
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
    intro y hy
    have : y ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr hy
    rw [← heq] at this
    rw [Finset.mem_image] at this
    obtain ⟨i, _, hi⟩ := this
    exact ⟨i, Set.mem_univ _, hi⟩


lemma g2_zero (n k : ℕ) (hn : n = 12 * k + 14) :
    (edgesLabelZero (cyc n) (fun i : Fin n => g2 n i.val)).card = 9 * k + 10 := by
  have hn12 : n % 12 = 2 := by omega
  unfold edgesLabelZero
  rw [split_count n (by omega) ⟨6 * k + 7, by omega⟩ (g2 n) (fun x => 1 < x)]
  have E : ((Finset.range n).filter
      (fun i => 1 < Nat.gcd (g2 n i) (g2 n ((i + 1) % n)))).card = 6 * k + 6 := by
    rw [← Nat.count_eq_card_filter_range, count_split _ n (12 * k + 10) 4 (by omega)]
    have h1 : Nat.count (fun i => 1 < Nat.gcd (g2 n i) (g2 n ((i + 1) % n))) (12 * k + 10) =
        Nat.count (fun i => Qc (i % 12)) (12 * k + 10) := by
      apply count_congr'
      intro i hi
      rw [mod_small _ _ (by omega)]
      rw [g2_pre n i (by omega) (by omega), g2_pre n (i + 1) (by omega) (by omega), edge_res]
    have h2 : Nat.count (fun t => 1 < Nat.gcd (g2 n (12 * k + 10 + t)) (g2 n ((12 * k + 10 + t + 1) % n))) 4 =
        Nat.count (fun t => t = 0 ∨ t = 3) 4 := by
      apply count_congr'
      intro t ht
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
      · -- t = 0
        have hm : (12 * k + 10 + 0 + 1) % n = 12 * k + 11 := by
          first
            | (rw [mod_small (12 * k + 10 + 0 + 1) n (by omega)] <;> omega)
            | (rw [mod_wrap (12 * k + 10 + 0 + 1) n (by omega) (by omega)] <;> omega)
        rw [hm]
        have v1 : g2 n (12 * k + 10 + 0) = 12 * k + 12 := by
          unfold g2; have := lf (12 * k + 10 + 0); split_ifs <;> omega
        have v2 : g2 n (12 * k + 11) = 12 * k + 14 := by
          unfold g2; have := lf (12 * k + 11); split_ifs <;> omega
        rw [v1, v2]
        rw [Gdiff _ _ 2 (by omega) (by norm_num) (by norm_num)]; omega
      · -- t = 1
        have hm : (12 * k + 10 + 1 + 1) % n = 12 * k + 12 := by
          first
            | (rw [mod_small (12 * k + 10 + 1 + 1) n (by omega)] <;> omega)
            | (rw [mod_wrap (12 * k + 10 + 1 + 1) n (by omega) (by omega)] <;> omega)
        rw [hm]
        have v1 : g2 n (12 * k + 10 + 1) = 12 * k + 14 := by
          unfold g2; have := lf (12 * k + 10 + 1); split_ifs <;> omega
        have v2 : g2 n (12 * k + 12) = 12 * k + 13 := by
          unfold g2; have := lf (12 * k + 12); split_ifs <;> omega
        rw [v1, v2]
        rw [Gdiff _ _ 1 (by omega) (by norm_num) (by norm_num)]; omega
      · -- t = 2
        have hm : (12 * k + 10 + 2 + 1) % n = 12 * k + 13 := by
          first
            | (rw [mod_small (12 * k + 10 + 2 + 1) n (by omega)] <;> omega)
            | (rw [mod_wrap (12 * k + 10 + 2 + 1) n (by omega) (by omega)] <;> omega)
        rw [hm]
        have v1 : g2 n (12 * k + 10 + 2) = 12 * k + 13 := by
          unfold g2; have := lf (12 * k + 10 + 2); split_ifs <;> omega
        have v2 : g2 n (12 * k + 13) = 12 * k + 10 := by
          unfold g2; have := lf (12 * k + 13); split_ifs <;> omega
        rw [v1, v2]
        rw [Gdiff _ _ 3 (by omega) (by norm_num) (by norm_num)]; omega
      · -- t = 3
        have hm : (12 * k + 10 + 3 + 1) % n = 0 := by
          first
            | (rw [mod_small (12 * k + 10 + 3 + 1) n (by omega)] <;> omega)
            | (rw [mod_wrap (12 * k + 10 + 3 + 1) n (by omega) (by omega)] <;> omega)
        rw [hm]
        have v1 : g2 n (12 * k + 10 + 3) = 12 * k + 10 := by
          unfold g2; have := lf (12 * k + 10 + 3); split_ifs <;> omega
        have v2 : g2 n (0) = 2 := by
          unfold g2; have := lf (0); split_ifs <;> omega
        rw [v1, v2]
        rw [Gs _ _ (by norm_num : 2 ∣ 36)]; omega
    rw [h1, h2, count_mod]
    have c1 : Nat.count (fun i => Qc (i % 12)) 12 = 6 := by decide
    have c2 : Nat.count (fun i => Qc (i % 12)) 10 = 4 := by decide
    have c3 : Nat.count (fun t => t = 0 ∨ t = 3) 4 = 2 := by decide
    rw [c1]; omega
  have C : ((Finset.range (n / 2)).filter
      (fun j => 1 < Nat.gcd (g2 n (2 * j)) (g2 n ((2 * j + 5) % n)))).card = 3 * k + 4 := by
    rw [← Nat.count_eq_card_filter_range, count_split _ (n / 2) (6 * k + 3) 4 (by omega)]
    have h1 : Nat.count (fun j => 1 < Nat.gcd (g2 n (2 * j)) (g2 n ((2 * j + 5) % n))) (6 * k + 3) =
        Nat.count (fun j => Qh (j % 6)) (6 * k + 3) := by
      apply count_congr'
      intro j hj
      rw [mod_small _ _ (by omega)]
      rw [g2_pre n (2 * j) (by omega) (by omega), g2_pre n (2 * j + 5) (by omega) (by omega), chord_res]
    have h2 : Nat.count (fun t => 1 < Nat.gcd (g2 n (2 * (6 * k + 3 + t))) (g2 n ((2 * (6 * k + 3 + t) + 5) % n))) 4 =
        Nat.count (fun t => t = 0 ∨ t = 2) 4 := by
      apply count_congr'
      intro t ht
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
      · -- t = 0
        have hm : (2 * (6 * k + 3 + 0) + 5) % n = 12 * k + 11 := by
          first
            | (rw [mod_small (2 * (6 * k + 3 + 0) + 5) n (by omega)] <;> omega)
            | (rw [mod_wrap (2 * (6 * k + 3 + 0) + 5) n (by omega) (by omega)] <;> omega)
        rw [hm]
        have v1 : g2 n (2 * (6 * k + 3 + 0)) = 12 * k + 8 := by
          unfold g2; have := lf (2 * (6 * k + 3 + 0)); split_ifs <;> omega
        have v2 : g2 n (12 * k + 11) = 12 * k + 14 := by
          unfold g2; have := lf (12 * k + 11); split_ifs <;> omega
        rw [v1, v2]
        rw [Gdiff _ _ 6 (by omega) (by norm_num) (by norm_num)]; omega
      · -- t = 1
        have hm : (2 * (6 * k + 3 + 1) + 5) % n = 12 * k + 13 := by
          first
            | (rw [mod_small (2 * (6 * k + 3 + 1) + 5) n (by omega)] <;> omega)
            | (rw [mod_wrap (2 * (6 * k + 3 + 1) + 5) n (by omega) (by omega)] <;> omega)
        rw [hm]
        have v1 : g2 n (2 * (6 * k + 3 + 1)) = 12 * k + 7 := by
          unfold g2; have := lf (2 * (6 * k + 3 + 1)); split_ifs <;> omega
        have v2 : g2 n (12 * k + 13) = 12 * k + 10 := by
          unfold g2; have := lf (12 * k + 13); split_ifs <;> omega
        rw [v1, v2]
        rw [Gdiff _ _ 3 (by omega) (by norm_num) (by norm_num)]; omega
      · -- t = 2
        have hm : (2 * (6 * k + 3 + 2) + 5) % n = 1 := by
          first
            | (rw [mod_small (2 * (6 * k + 3 + 2) + 5) n (by omega)] <;> omega)
            | (rw [mod_wrap (2 * (6 * k + 3 + 2) + 5) n (by omega) (by omega)] <;> omega)
        rw [hm]
        have v1 : g2 n (2 * (6 * k + 3 + 2)) = 12 * k + 12 := by
          unfold g2; have := lf (2 * (6 * k + 3 + 2)); split_ifs <;> omega
        have v2 : g2 n (1) = 4 := by
          unfold g2; have := lf (1); split_ifs <;> omega
        rw [v1, v2]
        rw [Gs _ _ (by norm_num : 4 ∣ 36)]; omega
      · -- t = 3
        have hm : (2 * (6 * k + 3 + 3) + 5) % n = 3 := by
          first
            | (rw [mod_small (2 * (6 * k + 3 + 3) + 5) n (by omega)] <;> omega)
            | (rw [mod_wrap (2 * (6 * k + 3 + 3) + 5) n (by omega) (by omega)] <;> omega)
        rw [hm]
        have v1 : g2 n (2 * (6 * k + 3 + 3)) = 12 * k + 13 := by
          unfold g2; have := lf (2 * (6 * k + 3 + 3)); split_ifs <;> omega
        have v2 : g2 n (3) = 1 := by
          unfold g2; have := lf (3); split_ifs <;> omega
        rw [v1, v2]
        rw [Gs _ _ (by norm_num : 1 ∣ 36)]; omega
    rw [h1, h2, count_mod]
    have c1 : Nat.count (fun j => Qh (j % 6)) 6 = 3 := by decide
    have c2 : Nat.count (fun j => Qh (j % 6)) 3 = 2 := by decide
    have c3 : Nat.count (fun t => t = 0 ∨ t = 2) 4 = 2 := by decide
    rw [c1]; omega
  omega


lemma g2_cyc (n k : ℕ) (hn : n = 12 * k + 14) :
    IsPrimeCordialLabeling (cyc n) (fun i : Fin n => g2 n i.val) := by
  have hn12 : n % 12 = 2 := by omega
  refine ⟨?_, ?_⟩
  · rw [Fintype.card_fin]
    exact g2_bij n hn12 (by omega)
  · have hz := g2_zero n k hn
    have hs := zero_add_one n (by omega) (by omega) (g2 n)
      (fun i hi => by have := g2_range n i hn12 (by omega) hi; omega)
    rw [abs_le]
    constructor <;> omega

end KnAux

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 2) :
    KnodelPrimeCordial.PrimeCordial (KnodelPrimeCordial.knodel 3 n) := by
  obtain ⟨k, hk⟩ : ∃ k, n = 12 * k + 14 := ⟨n / 12 - 1, by omega⟩
  have hcyc := KnAux.g2_cyc n k hk
  obtain ⟨g, hg⟩ :=
    KnodelPrimeCordial.cyclic_label_transport__p2m_2c82152f_23cb_4c50_aa74_3d1d5ac827a4_a2
      n hn h10 _ hcyc
  exact ⟨g, hg⟩

