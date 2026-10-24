-- Prove2me | solution 1 for HiringLP.ProbeTopK.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:49:59.517996+00:00
-- url     : https://prove2.me/submissions/e6fd8913-f4e7-43c7-bbb3-3b90acdded5f

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model
import Definitions.Def_HiringLP_ProbeTopK_WeightedRank
import Theorems.Thm_HiringLP_ProbeTopK_lemma_2

set_option autoImplicit false
open Finset HiringLP.ProbeTopK

namespace PTKAux

section Bern
variable {ι : Type*} [DecidableEq ι]

def WW (q : ι → ℝ) (S A : Finset ι) : ℝ := ∏ i ∈ S, if i ∈ A then q i else 1 - q i

theorem WW_insert (q : ι → ℝ) (a : ι) (S : Finset ι) (ha : a ∉ S) (Φ : Finset ι → ℝ) :
    ∑ A ∈ (insert a S).powerset, WW q (insert a S) A * Φ A =
      (1 - q a) * ∑ A ∈ S.powerset, WW q S A * Φ A +
        q a * ∑ A ∈ S.powerset, WW q S A * Φ (insert a A) := by
  rw [sum_powerset_insert ha, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro A hA
    have haA : a ∉ A := fun h => ha (mem_powerset.1 hA h)
    unfold WW
    rw [prod_insert ha, if_neg haA]; ring
  · apply sum_congr rfl
    intro A _
    unfold WW
    rw [prod_insert ha, if_pos (mem_insert_self a A)]
    have : ∏ i ∈ S, (if i ∈ insert a A then q i else 1 - q i) =
        ∏ i ∈ S, (if i ∈ A then q i else 1 - q i) := by
      apply prod_congr rfl
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      simp [mem_insert, hia]
    rw [this]; ring

end Bern

section Greedy
variable {n : ℕ} (ord : Equiv.Perm (Fin n))

def pre (t : ℕ) : Finset (Fin n) := univ.filter (fun i => ((ord.symm i : Fin n) : ℕ) < t)

def gset (k : ℕ) (D : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun i => i ∈ D ∧ (univ.filter fun l => l ∈ D ∧ before ord l i).card < k)

theorem pre_zero : pre ord 0 = ∅ := by
  ext i; simp [pre]

theorem pre_succ (t : ℕ) (ht : t < n) :
    pre ord (t + 1) = insert (ord ⟨t, ht⟩) (pre ord t) ∧ ord ⟨t, ht⟩ ∉ pre ord t := by
  constructor
  · ext i
    simp only [pre, mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inr h
      · left
        have : ord.symm i = ⟨t, ht⟩ := Fin.ext h
        rw [← this, Equiv.apply_symm_apply]
    · rintro (h | h)
      · rw [h, Equiv.symm_apply_apply]; simp
      · omega
  · simp [pre]

theorem pre_of_le (t : ℕ) (ht : n ≤ t) : pre ord t = univ := by
  ext i; simp only [pre, mem_filter, mem_univ, true_and, iff_true]
  have := (ord.symm i).isLt; omega

theorem before_iff_pre (l : Fin n) (t : ℕ) (ht : t < n) :
    before ord l (ord ⟨t, ht⟩) ↔ l ∈ pre ord t := by
  simp only [before, Equiv.symm_apply_apply, pre, mem_filter, mem_univ, true_and, Fin.lt_def]

theorem gset_pre (k : ℕ) (D : Finset (Fin n)) (t : ℕ) :
    (gset ord k D ∩ pre ord t).card = min k (D ∩ pre ord t).card := by
  induction t with
  | zero => simp [pre_zero]
  | succ t ih =>
    by_cases ht : t < n
    · obtain ⟨hpre, hna⟩ := pre_succ ord t ht
      set a : Fin n := ord ⟨t, ht⟩ with ha_def
      have hcount : (univ.filter fun l => l ∈ D ∧ before ord l a) = D ∩ pre ord t := by
        ext l
        simp only [mem_filter, mem_univ, true_and, mem_inter]
        rw [ha_def, before_iff_pre ord l t ht]
      rw [hpre]
      by_cases haD : a ∈ D
      · rw [inter_insert_of_mem haD, card_insert_of_notMem (fun h => hna (mem_inter.1 h).2)]
        by_cases hk : (D ∩ pre ord t).card < k
        · have hag : a ∈ gset ord k D := by
            simp only [gset, mem_filter, mem_univ, true_and]
            exact ⟨haD, by rw [hcount]; exact hk⟩
          rw [inter_insert_of_mem hag, card_insert_of_notMem (fun h => hna (mem_inter.1 h).2), ih]
          omega
        · have hag : a ∉ gset ord k D := by
            simp only [gset, mem_filter, mem_univ, true_and, not_and]
            intro _; rw [hcount]; exact hk
          rw [inter_insert_of_notMem hag, ih]
          omega
      · have hag : a ∉ gset ord k D := by
          simp only [gset, mem_filter, mem_univ, true_and, not_and]
          intro h; exact absurd h haD
        rw [inter_insert_of_notMem hag, inter_insert_of_notMem haD, ih]
    · rw [pre_of_le ord (t + 1) (by omega), ← pre_of_le ord t (by omega), ih]

theorem gset_sub (k : ℕ) (D : Finset (Fin n)) : gset ord k D ⊆ D := by
  intro i hi; simp only [gset, mem_filter] at hi; exact hi.2.1

theorem gset_card (k : ℕ) (D : Finset (Fin n)) : (gset ord k D).card ≤ k := by
  have := gset_pre ord k D n
  rw [pre_of_le ord n le_rfl, inter_univ, inter_univ] at this
  omega

/-- partial sums of `g` along the order equal sums over prefixes -/
theorem range_sum_eq_pre (d : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∑ t ∈ range m, (if h : t < n then d (ord ⟨t, h⟩) else 0) = ∑ i ∈ pre ord m, d i := by
  induction m with
  | zero => simp [pre_zero]
  | succ m ih =>
    have hm' : m < n := by omega
    obtain ⟨hpre, hna⟩ := pre_succ ord m hm'
    rw [sum_range_succ, ih (by omega), hpre, sum_insert hna, dif_pos hm', add_comm]

theorem abel (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : SortedBy ord w) (α β : Fin n → ℝ)
    (h : ∀ t ≤ n, ∑ i ∈ pre ord t, α i ≤ ∑ i ∈ pre ord t, β i) :
    ∑ i, w i * α i ≤ ∑ i, w i * β i := by
  set d : Fin n → ℝ := fun i => β i - α i with hd
  suffices H : 0 ≤ ∑ i, w i * d i by
    have : ∑ i, w i * d i = ∑ i, w i * β i - ∑ i, w i * α i := by
      rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _; simp [hd]; ring
    linarith
  set f : ℕ → ℝ := fun t => if h : t < n then w (ord ⟨t, h⟩) else 0 with hf
  set g : ℕ → ℝ := fun t => if h : t < n then d (ord ⟨t, h⟩) else 0 with hg
  have hsum : ∑ i, w i * d i = ∑ t ∈ range n, f t • g t := by
    rw [← Equiv.sum_comp ord, ← Fin.sum_univ_eq_sum_range (fun t => f t • g t)]
    apply sum_congr rfl
    intro t _
    simp [hf, hg, dif_pos t.isLt]
  have hG : ∀ m ≤ n, 0 ≤ ∑ j ∈ range m, g j := by
    intro m hm
    rw [hg, range_sum_eq_pre ord d m hm]
    have := h m hm
    have e : ∑ i ∈ pre ord m, d i = ∑ i ∈ pre ord m, β i - ∑ i ∈ pre ord m, α i := by
      rw [← sum_sub_distrib]
    rw [e]; linarith
  have hf0 : ∀ t, 0 ≤ f t := by
    intro t; simp only [hf]; split_ifs
    · exact hw _
    · exact le_rfl
  have hfanti : ∀ i, i + 1 < n → f (i + 1) ≤ f i := by
    intro i hi
    simp only [hf, dif_pos hi, dif_pos (show i < n by omega)]
    apply hs
    simp [before, Fin.lt_def]
  rw [hsum, sum_range_by_parts]
  have h1 : 0 ≤ f (n - 1) • ∑ j ∈ range n, g j := mul_nonneg (hf0 _) (hG n le_rfl)
  have h2 : ∑ i ∈ range (n - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j ≤ 0 := by
    apply sum_nonpos
    intro i hi
    have hi' : i + 1 < n := by have := mem_range.1 hi; omega
    have := hfanti i hi'
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hG (i + 1) (by omega))
  linarith

theorem wrank_eq_gset (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : SortedBy ord w) (k : ℕ)
    (D : Finset (Fin n)) : HiringLP.ProbeTopK.wrank w k D = ∑ i ∈ gset ord k D, w i := by
  apply le_antisymm
  · unfold HiringLP.ProbeTopK.wrank
    apply sup'_le
    intro R hR
    simp only [mem_filter, mem_powerset] at hR
    have key := abel ord w hw hs (fun i => if i ∈ R then 1 else 0)
      (fun i => if i ∈ gset ord k D then 1 else 0) (by
        intro t _
        simp only [sum_boole, Nat.cast_le]
        have e1 : (filter (fun i => i ∈ R) (pre ord t)) = R ∩ pre ord t := by
          ext i; simp [and_comm]
        have e2 : (filter (fun i => i ∈ gset ord k D) (pre ord t)) = gset ord k D ∩ pre ord t := by
          ext i; simp [and_comm]
        rw [e1, e2, gset_pre]
        apply le_min
        · exact (card_le_card inter_subset_left).trans hR.2
        · exact card_le_card (inter_subset_inter_right hR.1))
    simp only [mul_ite, mul_one, mul_zero, ← sum_filter] at key
    have e1 : (univ.filter fun i => i ∈ R) = R := by ext; simp
    have e2 : (univ.filter fun i => i ∈ gset ord k D) = gset ord k D := by ext; simp
    rw [e1, e2] at key
    exact key
  · unfold HiringLP.ProbeTopK.wrank
    apply le_sup' (fun R => ∑ i ∈ R, w i)
    simp only [mem_filter, mem_powerset]
    exact ⟨gset_sub ord k D, gset_card ord k D⟩

end Greedy

end PTKAux

namespace PTK4
open PTKAux

section W01
variable {ι : Type*} [DecidableEq ι]

theorem WW01 (q : ι → ℝ) (R : Finset ι) (hR : ∀ i ∈ R, q i = 0 ∨ q i = 1)
    (G : Finset ι → ℝ) :
    ∑ A ∈ R.powerset, WW q R A * G A = G (R.filter (fun i => q i = 1)) := by
  induction R using Finset.induction_on generalizing G with
  | empty => simp [WW]
  | insert c R hc ih =>
    rw [WW_insert q c R hc]
    have hR' : ∀ i ∈ R, q i = 0 ∨ q i = 1 := fun i hi => hR i (mem_insert_of_mem hi)
    rcases hR c (mem_insert_self c R) with h0 | h1
    · rw [h0, ih hR' G, filter_insert, if_neg (by rw [h0]; norm_num)]; ring
    · rw [h1, ih hR' G, ih hR' (fun A => G (insert c A)), filter_insert, if_pos h1]; ring

end W01

theorem card_ins {n : ℕ} (a : Fin n) (A B : Finset (Fin n)) (ha : a ∉ A) :
    (insert a A ∩ B).card = (A ∩ B).card + if a ∈ B then 1 else 0 := by
  by_cases hB : a ∈ B
  · rw [insert_inter_of_mem hB, card_insert_of_notMem (fun h => ha (mem_inter.1 h).1), if_pos hB]
  · rw [insert_inter_of_notMem hB, if_neg hB, add_zero]

/-- the greedy value `Φ(M) = Σ_{i ∈ G(M)} v_i` is submodular along the sorted order -/
theorem submod {n : ℕ} (ord : Equiv.Perm (Fin n)) (k : ℕ) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hs : SortedBy ord v) (A Q : Finset (Fin n)) (a b : Fin n) (ha : a ∉ A) (hb : b ∉ A)
    (hab : a ≠ b) :
    ∑ i ∈ gset ord k (insert a (insert b A) ∩ Q), v i + ∑ i ∈ gset ord k (A ∩ Q), v i ≤
      ∑ i ∈ gset ord k (insert a A ∩ Q), v i + ∑ i ∈ gset ord k (insert b A ∩ Q), v i := by
  have hsum : ∀ M : Finset (Fin n), ∑ i ∈ gset ord k M, v i =
      ∑ i, v i * (if i ∈ gset ord k M then 1 else 0) := by
    intro M
    rw [← sum_subset (subset_univ (gset ord k M))]
    · apply sum_congr rfl; intro i hi; rw [if_pos hi, mul_one]
    · intro i _ hi; rw [if_neg hi, mul_zero]
  simp only [hsum, ← sum_add_distrib, ← mul_add]
  apply abel ord v hv hs
  intro t _
  simp only [sum_add_distrib, sum_boole]
  have e : ∀ X : Finset (Fin n),
      ((filter (fun i => i ∈ gset ord k (X ∩ Q)) (pre ord t)).card : ℝ) =
      ((min k ((X ∩ (Q ∩ pre ord t)).card) : ℕ) : ℝ) := by
    intro X
    have : filter (fun i => i ∈ gset ord k (X ∩ Q)) (pre ord t) = gset ord k (X ∩ Q) ∩ pre ord t := by
      ext i; simp [and_comm]
    rw [this, gset_pre, inter_assoc]
  rw [e (insert a (insert b A)), e A, e (insert a A), e (insert b A)]
  have hab' : a ∉ insert b A := by simp [hab, ha]
  have key : min k (insert a (insert b A) ∩ (Q ∩ pre ord t)).card +
      min k (A ∩ (Q ∩ pre ord t)).card ≤
      min k (insert a A ∩ (Q ∩ pre ord t)).card + min k (insert b A ∩ (Q ∩ pre ord t)).card := by
    rw [card_ins a _ _ hab', card_ins b _ _ hb, card_ins a _ _ ha]
    split_ifs <;> omega
  exact_mod_cast key

end PTK4

namespace PTK4

theorem pbar_bounds {n J : ℕ} (I : Instance n J) (hI : I.Valid) (x : Fin n → Fin J → ℝ)
    (y : Fin n → ℝ) (hf : LPFeasible I x y) (i : Fin n) :
    0 ≤ pbar x y i ∧ pbar x y i ≤ 1 := by
  unfold pbar
  split_ifs with hy0
  · exact ⟨le_rfl, zero_le_one⟩
  · have hypos : 0 < y i := lt_of_le_of_ne (hf.2.2.2.2 i).1 (Ne.symm hy0)
    have hX0 : 0 ≤ ∑ j, x i j := sum_nonneg (fun j _ => hf.2.2.2.1 i j)
    have hXy : ∑ j, x i j ≤ y i := by
      calc ∑ j, x i j ≤ ∑ j, y i * I.q i j := sum_le_sum (fun j _ => hf.1 i j)
        _ = y i := by rw [← mul_sum, hI.2.2.2.2.2 i, mul_one]
    exact ⟨div_nonneg hX0 hypos.le, (div_le_one hypos).2 hXy⟩

theorem vbar_nonneg {n J : ℕ} (I : Instance n J) (hI : I.Valid) (x : Fin n → Fin J → ℝ)
    (y : Fin n → ℝ) (hf : LPFeasible I x y) (i : Fin n) : 0 ≤ vbar I x i := by
  unfold vbar
  split_ifs
  · exact le_rfl
  · apply div_nonneg
    · exact sum_nonneg (fun j _ => mul_nonneg (hI.2.2.2.1 j) (hf.2.2.2.1 i j))
    · exact sum_nonneg (fun j _ => hf.2.2.2.1 i j)

end PTK4

open PTKAux PTK4 in
theorem solution {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (hext : (x, y) ∈ Set.extremePoints ℝ (feasibleSet I)) (hF : (fracSet y).card = 2)
    (ord : Equiv.Perm (Fin n)) (hord : SortedBy ord (vbar I x)) :
    cutValue I x y ord (indepProb y) ≤ cutValue I x y ord (DR y) := by
  have hf : LPFeasible I x y := hext.1
  have hy := hf.2.2.2.2
  have h2 := (lemma_2 I hI x y hext).2 hF
  obtain ⟨a, b, hab, hfr⟩ := card_eq_two.1 hF
  have ha : a ∈ fracSet y := by rw [hfr]; simp
  have hb : b ∈ fracSet y := by rw [hfr]; simp
  have hya : 0 < y a ∧ y a < 1 := by simpa [fracSet] using ha
  have hyb : 0 < y b ∧ y b < 1 := by simpa [fracSet] using hb
  have hsum1 : y a + y b = 1 := by rw [hfr, sum_pair hab] at h2; exact h2
  set O := onesSet y with hO
  have haO : a ∉ O := by simp only [hO, onesSet, mem_filter, mem_univ, true_and]; linarith
  have hbO : b ∉ O := by simp only [hO, onesSet, mem_filter, mem_univ, true_and]; linarith
  set F : Finset (Fin n) → ℝ := fun S =>
    ∑ P : Finset (Fin n), indepProb (pbar x y) P * ∑ i ∈ gset ord I.k (S ∩ P), vbar I x i with hFdef
  have hcut : ∀ μ : Finset (Fin n) → ℝ, cutValue I x y ord μ = ∑ S, μ S * F S := by
    intro μ
    unfold cutValue
    have e1 : ∀ S P : Finset (Fin n),
        (∑ i, if i ∈ S ∧ i ∈ P ∧
          (univ.filter fun l => l ∈ S ∧ l ∈ P ∧ before ord l i).card < I.k then vbar I x i else 0)
          = ∑ i ∈ gset ord I.k (S ∩ P), vbar I x i := by
      intro S P
      rw [← sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext i
      simp only [gset, mem_filter, mem_univ, true_and, mem_inter, and_assoc]
    simp only [e1]
    rfl
  rw [hcut, hcut]
  -- the DR side
  have hne : insert a O ≠ insert b O := by
    intro h
    have : a ∈ insert b O := h ▸ mem_insert_self a O
    rcases mem_insert.1 this with h' | h'
    · exact hab h'
    · exact haO h'
  have hDRa : DR y (insert a O) = y a := by
    unfold DR
    have hsd : insert a O \ onesSet y = {a} := by
      ext i; simp only [mem_sdiff, mem_insert, mem_singleton, ← hO]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact h
        · exact absurd h h'
      · rintro rfl; exact ⟨Or.inl rfl, haO⟩
    rw [if_pos ⟨subset_insert _ _, insert_subset (mem_union_right _ ha) subset_union_left⟩,
      if_pos hF, hsd, card_singleton, if_pos rfl, sum_singleton]
  have hDRb : DR y (insert b O) = y b := by
    unfold DR
    have hsd : insert b O \ onesSet y = {b} := by
      ext i; simp only [mem_sdiff, mem_insert, mem_singleton, ← hO]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact h
        · exact absurd h h'
      · rintro rfl; exact ⟨Or.inl rfl, hbO⟩
    rw [if_pos ⟨subset_insert _ _, insert_subset (mem_union_right _ hb) subset_union_left⟩,
      if_pos hF, hsd, card_singleton, if_pos rfl, sum_singleton]
  have hDR0 : ∀ S, S ≠ insert a O ∧ S ≠ insert b O → DR y S * F S = 0 := by
    rintro S ⟨hSa, hSb⟩
    suffices DR y S = 0 by rw [this, zero_mul]
    unfold DR
    by_cases hc : onesSet y ⊆ S ∧ S ⊆ onesSet y ∪ fracSet y
    swap
    · rw [if_neg hc]
    rw [if_pos hc, if_pos hF]
    by_cases hcard : (S \ onesSet y).card = 1
    swap
    · rw [if_neg hcard]
    · exfalso
      obtain ⟨c, hc1⟩ := card_eq_one.1 hcard
      have hcS : c ∈ S \ onesSet y := by rw [hc1]; exact mem_singleton_self c
      have hcfr : c ∈ fracSet y := by
        have := hc.2 (mem_sdiff.1 hcS).1
        rcases mem_union.1 this with h | h
        · exact absurd h (mem_sdiff.1 hcS).2
        · exact h
      have hSeq : S = insert c O := by
        ext i
        simp only [mem_insert]
        constructor
        · intro hi
          by_cases hiO : i ∈ onesSet y
          · exact Or.inr hiO
          · left
            have : i ∈ S \ onesSet y := mem_sdiff.2 ⟨hi, hiO⟩
            rw [hc1] at this; exact mem_singleton.1 this
        · rintro (rfl | hi)
          · exact (mem_sdiff.1 hcS).1
          · exact hc.1 hi
      rw [hfr] at hcfr
      rcases mem_insert.1 hcfr with h | h
      · exact hSa (h ▸ hSeq)
      · exact hSb ((mem_singleton.1 h) ▸ hSeq)
  have hDR : ∑ S, DR y S * F S = y a * F (insert a O) + y b * F (insert b O) := by
    rw [sum_eq_add_of_mem (insert a O) (insert b O) (mem_univ _) (mem_univ _) hne
      (fun S _ h => hDR0 S h), hDRa, hDRb]
  -- the independent side
  set R : Finset (Fin n) := (univ.erase a).erase b with hR
  have hbR : b ∉ R := by simp [hR]
  have haR : a ∉ insert b R := by simp [hR, hab]
  have hu : (univ : Finset (Fin n)) = insert a (insert b R) := by
    ext i
    simp only [mem_univ, mem_insert, hR, mem_erase, ne_eq, true_iff]
    by_cases h1 : i = a
    · exact Or.inl h1
    · by_cases h2 : i = b
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨h2, h1, trivial⟩)
  have hR01 : ∀ i ∈ R, y i = 0 ∨ y i = 1 := by
    intro i hi
    simp only [hR, mem_erase, ne_eq, mem_univ, and_true] at hi
    have hni : i ∉ fracSet y := by rw [hfr]; simp [hi.1, hi.2]
    simp only [fracSet, mem_filter, mem_univ, true_and, not_and_or, not_lt] at hni
    rcases hni with h | h
    · left; linarith [(hy i).1]
    · right; linarith [(hy i).2]
  have hRO : R.filter (fun i => y i = 1) = O := by
    ext i
    simp only [hR, mem_filter, mem_erase, ne_eq, mem_univ, and_true, hO, onesSet, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨⟨?_, ?_⟩, h⟩
      · rintro rfl; linarith
      · rintro rfl; linarith
  have hind : ∑ S, indepProb y S * F S =
      (1 - y a) * ((1 - y b) * F O + y b * F (insert b O)) +
        y a * ((1 - y b) * F (insert a O) + y b * F (insert a (insert b O))) := by
    have e0 : ∑ S, indepProb y S * F S =
        ∑ S ∈ (univ : Finset (Fin n)).powerset, WW y univ S * F S := by
      rw [powerset_univ]; rfl
    rw [e0, hu, WW_insert y a _ haR, WW_insert y b R hbR, WW_insert y b R hbR,
      WW01 y R hR01, WW01 y R hR01, WW01 y R hR01, WW01 y R hR01, hRO]
  have hsub : F (insert a (insert b O)) + F O ≤ F (insert a O) + F (insert b O) := by
    simp only [hFdef, ← sum_add_distrib, ← mul_add]
    apply sum_le_sum
    intro P _
    have hw : 0 ≤ indepProb (pbar x y) P := by
      unfold indepProb
      apply prod_nonneg
      intro i _
      have := pbar_bounds I hI x y hf i
      split_ifs <;> linarith
    apply mul_le_mul_of_nonneg_left _ hw
    exact submod ord I.k (vbar I x) (vbar_nonneg I hI x y hf) hord O P a b haO hbO hab
  rw [hDR, hind]
  have hyb' : y b = 1 - y a := by linarith
  have key : y a * F (insert a O) + y b * F (insert b O) -
      ((1 - y a) * ((1 - y b) * F O + y b * F (insert b O)) +
        y a * ((1 - y b) * F (insert a O) + y b * F (insert a (insert b O)))) =
      y a * y b * (F (insert a O) + F (insert b O) - F (insert a (insert b O)) - F O) := by
    rw [hyb']; ring
  have : 0 ≤ y a * y b * (F (insert a O) + F (insert b O) - F (insert a (insert b O)) - F O) :=
    mul_nonneg (mul_nonneg hya.1.le hyb.1.le) (by linarith)
  linarith
