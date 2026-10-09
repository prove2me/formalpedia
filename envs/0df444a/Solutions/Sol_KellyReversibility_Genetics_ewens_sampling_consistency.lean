-- Prove2me | solution 1 for KellyReversibility.Genetics.ewens_sampling_consistency
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T12:01:46.647117+00:00
-- url     : https://prove2.me/submissions/bf1ba88d-54ab-4cfb-a17b-e18423ca8f8f

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal
import Definitions.Def_KellyReversibility_Genetics_Ewens
import Definitions.Def_KellyReversibility_Genetics_Sampling

set_option autoImplicit false

namespace EwensAux8fb

open Finset KellyReversibility.Genetics AppliedComb.GenFun

/-- class-size multiset of a labelling of a finite type -/
noncomputable def Dg {ι : Type*} [Fintype ι] (z : ι → ℕ) : Multiset ℕ :=
  (Finset.univ.image z).val.map (fun a => (Finset.univ.filter (fun j => z j = a)).card)

/-- size of the class of type `a` inside the subset `S` -/
def cnt {M : ℕ} (x : Fin M → ℕ) (S : Finset (Fin M)) (a : ℕ) : ℕ :=
  (S.filter (fun j => x j = a)).card

/-- class-size multiset of the sub-population `S` -/
def D {M : ℕ} (x : Fin M → ℕ) (S : Finset (Fin M)) : Multiset ℕ :=
  (S.image x).val.map (cnt x S)

lemma count_Dg {ι : Type*} [Fintype ι] (z : ι → ℕ) (i : ℕ) :
    (Dg z).count i = ((Finset.univ.image z).filter
      (fun a => (Finset.univ.filter (fun j => z j = a)).card = i)).card := by
  unfold Dg
  rw [Multiset.count_map, Finset.card, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro a _
  exact eq_comm

lemma alleleCount_eq {ι : Type*} [Fintype ι] (z : ι → ℕ) (i : ℕ) :
    alleleCount z i = (Dg z).count i := by
  rw [count_Dg]
  unfold alleleCount
  convert rfl

lemma hasDesc_iff {ι : Type*} [Fintype ι] {n : ℕ} (z : ι → ℕ) (q : Nat.Partition n) :
    HasDescription z q ↔ Dg z = q.parts := by
  unfold HasDescription
  simp_rw [alleleCount_eq]
  constructor
  · intro h
    ext i
    exact h i
  · intro h i
    rw [h]

lemma Dg_restr {M : ℕ} (x : Fin M → ℕ) (S : Finset (Fin M)) :
    Dg (fun j : ↥S => x j.1) = D x S := by
  unfold Dg D
  have h1 : (Finset.univ : Finset ↥S).image (fun j => x j.1) = S.image x := by
    ext a; simp
  rw [h1]
  apply Multiset.map_congr rfl
  intro a _
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter]
  exact Finset.sum_coe_sort S (fun j => if x j = a then 1 else 0)

lemma Dg_full {M : ℕ} (x : Fin M → ℕ) : Dg x = D x Finset.univ := rfl

lemma count_D {M : ℕ} (x : Fin M → ℕ) (S : Finset (Fin M)) (c : ℕ) :
    (D x S).count c = ((S.image x).filter (fun a => cnt x S a = c)).card := by
  unfold D
  rw [Multiset.count_map, Finset.card, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro a _
  exact eq_comm

lemma cnt_pos {M : ℕ} (x : Fin M → ℕ) (S : Finset (Fin M)) {a : ℕ} (ha : a ∈ S.image x) :
    0 < cnt x S a := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  unfold cnt
  exact Finset.card_pos.mpr ⟨j, by simp [hj]⟩

lemma D_pos {M : ℕ} (x : Fin M → ℕ) (S : Finset (Fin M)) : ∀ a ∈ D x S, 0 < a := by
  intro a ha
  unfold D at ha
  obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
  exact cnt_pos x S hb

lemma D_sum {M : ℕ} (x : Fin M → ℕ) (S : Finset (Fin M)) : (D x S).sum = S.card := by
  unfold D cnt
  rw [Finset.card_eq_sum_card_image x S]
  rfl

/-- one-step move on a class-size multiset: one class of size `c` loses a member -/
def mv (c : ℕ) (s : Multiset ℕ) : Multiset ℕ := s.erase c + if 2 ≤ c then {c - 1} else 0

lemma D_erase {M : ℕ} (x : Fin M → ℕ) (S : Finset (Fin M)) {j : Fin M} (hj : j ∈ S) :
    D x (S.erase j) = mv (cnt x S (x j)) (D x S) := by
  set a := x j with ha
  set c := cnt x S a with hc
  have hc1 : 1 ≤ c := cnt_pos x S (Finset.mem_image_of_mem x hj)
  have haimg : a ∈ S.image x := Finset.mem_image_of_mem x hj
  have hcnt : ∀ b, b ≠ a → cnt x (S.erase j) b = cnt x S b := by
    intro b hb
    unfold cnt
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
    simp only [Finset.mem_filter, not_and]
    intro _ h
    exact hb (by rw [← h])
  have hcnta : cnt x (S.erase j) a = c - 1 := by
    unfold cnt
    rw [hc, Finset.filter_erase, Finset.card_erase_of_mem]
    · rfl
    · simp [hj, ha]
  set R := ((S.image x).erase a).val.map (cnt x S) with hR
  have hDS : D x S = c ::ₘ R := by
    unfold D
    conv_lhs => rw [← Finset.insert_erase haimg]
    rw [Finset.insert_val_of_notMem (Finset.notMem_erase a _), Multiset.map_cons]
  by_cases h2 : 2 ≤ c
  · have himg : (S.erase j).image x = S.image x := by
      ext b
      simp only [Finset.mem_image, Finset.mem_erase]
      constructor
      · rintro ⟨k, ⟨_, hk⟩, hkb⟩
        exact ⟨k, hk, hkb⟩
      · rintro ⟨k, hk, hkb⟩
        by_cases hkj : k = j
        · have hlt : 1 < cnt x S a := by omega
          unfold cnt at hlt
          obtain ⟨k', hk', hne⟩ := Finset.exists_mem_ne hlt j
          rw [Finset.mem_filter] at hk'
          refine ⟨k', ⟨hne, hk'.1⟩, ?_⟩
          rw [hk'.2, ← hkb, hkj]
        · exact ⟨k, ⟨hkj, hk⟩, hkb⟩
    rw [show D x (S.erase j) = ((S.erase j).image x).val.map (cnt x (S.erase j)) from rfl, himg]
    conv_lhs => rw [← Finset.insert_erase haimg]
    rw [Finset.insert_val_of_notMem (Finset.notMem_erase a _), Multiset.map_cons, hcnta, hDS]
    unfold mv
    rw [if_pos h2, Multiset.erase_cons_head, add_comm, Multiset.singleton_add]
    congr 1
    apply Multiset.map_congr rfl
    intro b hb
    exact hcnt b (Finset.ne_of_mem_erase (Finset.mem_val.mp hb))
  · have hc1' : c = 1 := by omega
    have himg : (S.erase j).image x = (S.image x).erase a := by
      ext b
      simp only [Finset.mem_image, Finset.mem_erase]
      constructor
      · rintro ⟨k, ⟨hkj, hk⟩, hkb⟩
        refine ⟨?_, k, hk, hkb⟩
        intro hba
        have hka : x k = a := by rw [hkb, hba]
        have h2' : 2 ≤ cnt x S a := by
          unfold cnt
          have hsub : ({k, j} : Finset (Fin M)) ⊆ S.filter (fun i => x i = a) := by
            intro i hi
            rw [Finset.mem_insert, Finset.mem_singleton] at hi
            rw [Finset.mem_filter]
            rcases hi with h | h
            · rw [h]; exact ⟨hk, hka⟩
            · rw [h]; exact ⟨hj, ha.symm⟩
          have := Finset.card_le_card hsub
          rw [Finset.card_pair hkj] at this
          exact this
        omega
      · rintro ⟨hba, k, hk, hkb⟩
        refine ⟨k, ⟨?_, hk⟩, hkb⟩
        intro hkj
        apply hba
        rw [← hkb, hkj]
    rw [show D x (S.erase j) = ((S.erase j).image x).val.map (cnt x (S.erase j)) from rfl, himg, hDS]
    unfold mv
    rw [if_neg h2, hc1', Multiset.erase_cons_head, add_zero]
    apply Multiset.map_congr rfl
    intro b hb
    exact hcnt b (Finset.ne_of_mem_erase (Finset.mem_val.mp hb))

lemma card_class {M : ℕ} (x : Fin M → ℕ) (S : Finset (Fin M)) (c : ℕ) :
    (S.filter (fun j => cnt x S (x j) = c)).card = c * (D x S).count c := by
  rw [count_D]
  have H : ∀ j ∈ S.filter (fun j => cnt x S (x j) = c),
      x j ∈ (S.image x).filter (fun a => cnt x S a = c) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_image_of_mem x hj.1, hj.2⟩
  rw [Finset.card_eq_sum_card_fiberwise H]
  rw [Finset.sum_const_nat (m := c)]
  · ring
  intro a ha
  rw [Finset.mem_filter] at ha
  have : (S.filter (fun j => cnt x S (x j) = c)).filter (fun j => x j = a)
      = S.filter (fun j => x j = a) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro j _
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      exact ha.2
  rw [this]
  exact ha.2

/-- number of ways to remove one individual from a population with class sizes `s` and get
class sizes `s'` -/
def Nn (n : ℕ) (s s' : Multiset ℕ) : ℕ :=
  ∑ c ∈ Finset.Icc 1 n, c * s.count c * (if mv c s = s' then 1 else 0)

lemma card_erase_eq {M : ℕ} (x : Fin M → ℕ) (S : Finset (Fin M)) (s' : Multiset ℕ) :
    (S.filter (fun j => D x (S.erase j) = s')).card = Nn S.card (D x S) s' := by
  rw [Finset.card_filter]
  have h1 : ∀ j ∈ S, (if D x (S.erase j) = s' then 1 else 0)
      = (if mv (cnt x S (x j)) (D x S) = s' then 1 else 0) := by
    intro j hj
    rw [D_erase x S hj]
  rw [Finset.sum_congr rfl h1]
  have hmaps : ∀ j ∈ S, cnt x S (x j) ∈ Finset.Icc 1 S.card := by
    intro j hj
    rw [Finset.mem_Icc]
    exact ⟨cnt_pos x S (Finset.mem_image_of_mem x hj), Finset.card_filter_le _ _⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  unfold Nn
  apply Finset.sum_congr rfl
  intro c _
  have h2 : ∀ j ∈ S.filter (fun j => cnt x S (x j) = c),
      (if mv (cnt x S (x j)) (D x S) = s' then 1 else 0)
        = (if mv c (D x S) = s' then 1 else 0) := by
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, card_class]

lemma pair_count {M : ℕ} (x : Fin M → ℕ) (m : ℕ) (_hm : m < M) (s' : Multiset ℕ) :
    ∑ S ∈ (Finset.univ : Finset (Fin M)).powersetCard (m + 1),
        (S.filter (fun j => D x (S.erase j) = s')).card
      = (M - m) * (((Finset.univ : Finset (Fin M)).powersetCard m).filter
          (fun T => D x T = s')).card := by
  rw [← Finset.card_sigma]
  have hR : (M - m) * (((Finset.univ : Finset (Fin M)).powersetCard m).filter
          (fun T => D x T = s')).card
      = ∑ T ∈ ((Finset.univ : Finset (Fin M)).powersetCard m).filter (fun T => D x T = s'),
          (Finset.univ \ T).card := by
    rw [Finset.sum_congr rfl (g := fun _ => M - m), Finset.sum_const, smul_eq_mul, mul_comm]
    intro T hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
    rw [Finset.card_univ_sdiff, Fintype.card_fin, hT.1.2]
  rw [hR, ← Finset.card_sigma]
  refine Finset.card_bij' (fun p _ => (⟨p.1.erase p.2, p.2⟩ : (_ : Finset (Fin M)) × Fin M))
    (fun p _ => (⟨insert p.2 p.1, p.2⟩ : (_ : Finset (Fin M)) × Fin M)) ?_ ?_ ?_ ?_
  · rintro ⟨S, j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powersetCard] at h ⊢
    refine ⟨⟨⟨Finset.subset_univ _, ?_⟩, h.2.2⟩, ?_⟩
    · rw [Finset.card_erase_of_mem h.2.1, h.1.2]
      rfl
    · simp
  · rintro ⟨T, k⟩ h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at h ⊢
    refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self _ _, ?_⟩
    · rw [Finset.card_insert_of_notMem h.2, h.1.1.2]
    · rw [Finset.erase_insert h.2]
      exact h.1.2
  · rintro ⟨S, j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_filter] at h
    show (⟨insert j (S.erase j), j⟩ : (_ : Finset (Fin M)) × Fin M) = ⟨S, j⟩
    rw [Finset.insert_erase h.2.1]
  · rintro ⟨T, k⟩ h
    simp only [Finset.mem_sigma, Finset.mem_sdiff] at h
    show (⟨(insert k T).erase k, k⟩ : (_ : Finset (Fin M)) × Fin M) = ⟨T, k⟩
    rw [Finset.erase_insert h.2.2]

lemma group_sum {M : ℕ} (x : Fin M → ℕ) (n : ℕ) (f : Multiset ℕ → ℕ) :
    ∑ S ∈ (Finset.univ : Finset (Fin M)).powersetCard n, f (D x S)
      = ∑ r : Nat.Partition n, (((Finset.univ : Finset (Fin M)).powersetCard n).filter
          (fun S => D x S = r.parts)).card * f r.parts := by
  have h : ∀ S ∈ (Finset.univ : Finset (Fin M)).powersetCard n,
      f (D x S) = ∑ r : Nat.Partition n, if D x S = r.parts then f r.parts else 0 := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    let r0 : Nat.Partition n := ⟨D x S, fun h => D_pos x S _ h, by rw [D_sum, hS.2]⟩
    rw [Finset.sum_eq_single r0]
    · simp [r0]
    · intro r _ hr
      rw [if_neg]
      intro h
      exact hr (Nat.Partition.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ r0) h
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

lemma sdp_eq {M : ℕ} (x : Fin M → ℕ) (m : ℕ) (q : Nat.Partition m) :
    sampleDescProb x m q = ((((Finset.univ : Finset (Fin M)).powersetCard m).filter
      (fun T => D x T = q.parts)).card : ℝ) / (M.choose m : ℝ) := by
  unfold sampleDescProb
  congr 3
  ext T
  simp only [Finset.mem_filter, hasDesc_iff, Dg_restr]

lemma sdp_self {M : ℕ} (x : Fin M → ℕ) (p q : Nat.Partition M) (hx : HasDescription x p) :
    sampleDescProb x M q = if q = p then 1 else 0 := by
  rw [sdp_eq]
  have hP : (Finset.univ : Finset (Fin M)).powersetCard M = {Finset.univ} := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin M))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  rw [hP, Finset.filter_singleton, Nat.choose_self]
  rw [hasDesc_iff, Dg_full] at hx
  rw [hx]
  by_cases h : q = p
  · subst h
    simp
  · have : ¬ p.parts = q.parts := fun h' => h (Nat.Partition.ext h'.symm)
    simp [this, h]

lemma tower {M : ℕ} (x : Fin M → ℕ) (m : ℕ) (hm : m < M) (q : Nat.Partition m) :
    sampleDescProb x m q = ∑ r : Nat.Partition (m + 1),
      sampleDescProb x (m + 1) r * ((Nn (m + 1) r.parts q.parts : ℕ) : ℝ) / ((m : ℝ) + 1) := by
  have key : (M - m) * (((Finset.univ : Finset (Fin M)).powersetCard m).filter
        (fun T => D x T = q.parts)).card
      = ∑ r : Nat.Partition (m + 1), (((Finset.univ : Finset (Fin M)).powersetCard (m + 1)).filter
          (fun S => D x S = r.parts)).card * Nn (m + 1) r.parts q.parts := by
    rw [← pair_count x m hm, ← group_sum x (m + 1) (fun s => Nn (m + 1) s q.parts)]
    apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [card_erase_eq, hS.2]
  have key' : ((M - m : ℕ) : ℝ) * ((((Finset.univ : Finset (Fin M)).powersetCard m).filter
        (fun T => D x T = q.parts)).card : ℝ)
      = ∑ r : Nat.Partition (m + 1), ((((Finset.univ : Finset (Fin M)).powersetCard (m + 1)).filter
          (fun S => D x S = r.parts)).card : ℝ) * ((Nn (m + 1) r.parts q.parts : ℕ) : ℝ) := by
    exact_mod_cast key
  have hch : ((M.choose (m + 1) : ℕ) : ℝ) * ((m : ℝ) + 1) = (M.choose m : ℝ) * ((M - m : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq M m
  have hC : (M.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm.le).ne'
  have hMm : ((M - m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : M - m ≠ 0)
  simp only [sdp_eq]
  simp_rw [div_mul_eq_mul_div, div_div]
  rw [← Finset.sum_div, ← key', hch]
  field_simp

/-! ## Ewens algebra -/

noncomputable def Fv (ν : ℝ) (i c : ℕ) : ℝ := (ν / (i : ℝ)) ^ c / (c.factorial : ℝ)

noncomputable def Pv (ν : ℝ) (T : Finset ℕ) (s : Multiset ℕ) : ℝ := ∏ j ∈ T, Fv ν j (s.count j)

lemma Pv_eq_self (ν : ℝ) (T : Finset ℕ) (s : Multiset ℕ) (h : s.toFinset ⊆ T) :
    Pv ν T s = Pv ν s.toFinset s := by
  unfold Pv
  symm
  apply Finset.prod_subset h
  intro j _ hj
  have : s.count j = 0 := by
    rw [Multiset.count_eq_zero]; simpa using hj
  simp [Fv, this]

lemma Pv_congr (ν : ℝ) (T T' : Finset ℕ) (s : Multiset ℕ) (h : s.toFinset ⊆ T)
    (h' : s.toFinset ⊆ T') : Pv ν T s = Pv ν T' s := by
  rw [Pv_eq_self ν T s h, Pv_eq_self ν T' s h']

lemma Fv_step (ν : ℝ) (i c : ℕ) (hi : i ≠ 0) :
    ((c + 1 : ℕ) : ℝ) * (i : ℝ) * Fv ν i (c + 1) = ν * Fv ν i c := by
  unfold Fv
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast hi
  have key : ν / (i : ℝ) * (i : ℝ) = ν := div_mul_cancel₀ ν hi'
  generalize ν / (i : ℝ) = a at key ⊢
  subst key
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hf : (c.factorial : ℝ) ≠ 0 := by positivity
  have hc1 : (c : ℝ) + 1 ≠ 0 := by positivity
  field_simp

lemma Pv_cons (ν : ℝ) (T : Finset ℕ) (s : Multiset ℕ) (c : ℕ) (hcT : c ∈ T) (hc0 : c ≠ 0) :
    ((s.count c + 1 : ℕ) : ℝ) * (c : ℝ) * Pv ν T (c ::ₘ s) = ν * Pv ν T s := by
  unfold Pv
  rw [← Finset.mul_prod_erase T _ hcT, ← Finset.mul_prod_erase T _ hcT]
  have hrest : ∏ j ∈ T.erase c, Fv ν j ((c ::ₘ s).count j) = ∏ j ∈ T.erase c, Fv ν j (s.count j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, Multiset.count_cons_self]
  have h := Fv_step ν c (s.count c) hc0
  linear_combination (∏ j ∈ T.erase c, Fv ν j (s.count j)) * h

lemma term_c (ν : ℝ) (n : ℕ) (q : Nat.Partition n) (c : ℕ) (hc : c ∈ Finset.Icc 1 (n + 1)) :
    ∑ r : Nat.Partition (n + 1), Pv ν (Finset.Icc 1 (n + 1)) r.parts *
      ((c : ℝ) * (r.parts.count c : ℝ) * (if mv c r.parts = q.parts then 1 else 0))
      = Pv ν (Finset.Icc 1 (n + 1)) q.parts *
        (if c = 1 then ν else ((c - 1 : ℕ) : ℝ) * (q.parts.count (c - 1) : ℝ)) := by
  rw [Finset.mem_Icc] at hc
  set T := Finset.Icc 1 (n + 1) with hT
  set s := q.parts with hs
  set δ : Multiset ℕ := if 2 ≤ c then {c - 1} else 0 with hδ
  have hmv : ∀ t : Multiset ℕ, mv c t = t.erase c + δ := fun t => rfl
  have hsT : ∀ i ∈ s, i ∈ T := by
    intro i hi
    have h1 := q.parts_pos hi
    have h2 : i ≤ n := by rw [← q.parts_sum]; exact Multiset.le_sum_of_mem hi
    rw [hT, Finset.mem_Icc]; omega
  by_cases hδs : δ ≤ s
  · have hpos : ∀ {i : ℕ}, i ∈ c ::ₘ (s - δ) → 0 < i := by
      intro i hi
      rw [Multiset.mem_cons] at hi
      rcases hi with h | h
      · omega
      · exact q.parts_pos (Multiset.mem_of_le tsub_le_self h)
    have hsum : (c ::ₘ (s - δ)).sum = n + 1 := by
      have hsplit : s = (s - δ) + δ := (tsub_add_cancel_of_le hδs).symm
      have hss : s.sum = n := q.parts_sum
      rw [Multiset.sum_cons]
      by_cases h2 : 2 ≤ c
      · have hδv : δ = {c - 1} := by rw [hδ, if_pos h2]
        have := congrArg Multiset.sum hsplit
        rw [Multiset.sum_add, hδv, Multiset.sum_singleton] at this
        rw [hδv]
        omega
      · have hδv : δ = 0 := by rw [hδ, if_neg h2]
        rw [hδv, tsub_zero]
        omega
    let r0 : Nat.Partition (n + 1) := ⟨c ::ₘ (s - δ), hpos, hsum⟩
    have hmv0 : mv c r0.parts = s := by
      rw [hmv]
      show (c ::ₘ (s - δ)).erase c + δ = s
      rw [Multiset.erase_cons_head, tsub_add_cancel_of_le hδs]
    rw [Finset.sum_eq_single r0]
    · rw [if_pos hmv0, mul_one]
      show Pv ν T (c ::ₘ (s - δ)) * ((c : ℝ) * ((c ::ₘ (s - δ)).count c : ℝ)) = _
      have hcount : (s - δ).count c = s.count c := by
        rw [Multiset.count_sub]
        have : δ.count c = 0 := by
          rw [hδ]
          split_ifs with h2
          · rw [Multiset.count_singleton, if_neg (by omega)]
          · rfl
        rw [this, Nat.sub_zero]
      have hcT : c ∈ T := by rw [hT, Finset.mem_Icc]; omega
      have key := Pv_cons ν T (s - δ) c hcT (by omega)
      rw [hcount] at key
      rw [Multiset.count_cons_self, hcount]
      have lhs_eq : Pv ν T (c ::ₘ (s - δ)) * ((c : ℝ) * (((s.count c + 1 : ℕ)) : ℝ))
          = ν * Pv ν T (s - δ) := by
        rw [← key]; ring
      rw [lhs_eq]
      by_cases h2 : 2 ≤ c
      · have hδv : δ = {c - 1} := by rw [hδ, if_pos h2]
        have hmem : c - 1 ∈ s := by
          rw [hδv, Multiset.singleton_le] at hδs; exact hδs
        rw [if_neg (by omega), hδv, Multiset.sub_singleton]
        have hc1T : c - 1 ∈ T := hsT _ hmem
        have key2 := Pv_cons ν T (s.erase (c - 1)) (c - 1) hc1T (by omega)
        rw [Multiset.cons_erase hmem, Multiset.count_erase_self] at key2
        have hcnt : s.count (c - 1) - 1 + 1 = s.count (c - 1) :=
          Nat.sub_add_cancel (Multiset.count_pos.mpr hmem)
        rw [hcnt] at key2
        rw [← key2]
        ring
      · have hc1 : c = 1 := by omega
        have hδv : δ = 0 := by rw [hδ, if_neg h2]
        rw [if_pos hc1, hδv, tsub_zero]
        ring
    · intro r _ hr
      by_cases hm : mv c r.parts = s
      · have hcr : r.parts.count c = 0 := by
          by_contra hne
          apply hr
          apply Nat.Partition.ext
          show r.parts = c ::ₘ (s - δ)
          have hcm : c ∈ r.parts := Multiset.count_ne_zero.mp hne
          rw [hmv] at hm
          rw [← hm, add_tsub_cancel_right, Multiset.cons_erase hcm]
        rw [hcr]
        simp
      · rw [if_neg hm]
        simp
    · intro h
      exact absurd (Finset.mem_univ r0) h
  · have h2 : 2 ≤ c := by
      by_contra h2
      apply hδs
      rw [hδ, if_neg h2]
      exact Multiset.zero_le _
    have hδv : δ = {c - 1} := by rw [hδ, if_pos h2]
    have hnot : s.count (c - 1) = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      apply hδs
      rw [hδv, Multiset.singleton_le]
      exact hmem
    rw [if_neg (by omega), hnot]
    simp only [Nat.cast_zero, mul_zero]
    apply Finset.sum_eq_zero
    intro r _
    rw [if_neg]
    · simp
    intro hm
    apply hδs
    rw [← hm, hmv]
    exact Multiset.le_add_left _ _

lemma sum_w (ν : ℝ) (n : ℕ) (q : Nat.Partition n) :
    ∑ c ∈ Finset.Icc 1 (n + 1),
      (if c = 1 then ν else ((c - 1 : ℕ) : ℝ) * (q.parts.count (c - 1) : ℝ)) = ν + n := by
  have hI : Finset.Icc 1 (n + 1) = insert 1 (Finset.Icc 2 (n + 1)) := by
    ext c; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hI, Finset.sum_insert (by simp), if_pos rfl]
  congr 1
  have h2 : ∑ c ∈ Finset.Icc 2 (n + 1),
      (if c = 1 then ν else ((c - 1 : ℕ) : ℝ) * (q.parts.count (c - 1) : ℝ))
      = ∑ c ∈ Finset.Icc 2 (n + 1), ((c - 1 : ℕ) : ℝ) * (q.parts.count (c - 1) : ℝ) := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [if_neg (by omega)]
  rw [h2]
  have hmap : Finset.Icc 2 (n + 1) = (Finset.Icc 1 n).map (addRightEmbedding 1) := by
    rw [Finset.map_add_right_Icc]
  rw [hmap, Finset.sum_map]
  simp only [addRightEmbedding_apply, Nat.add_sub_cancel]
  have hsub : q.parts.toFinset ⊆ Finset.Icc 1 n := by
    intro i hi
    have hi' : i ∈ q.parts := Multiset.mem_toFinset.mp hi
    have h1 := q.parts_pos hi'
    have h2 : i ≤ n := by rw [← q.parts_sum]; exact Multiset.le_sum_of_mem hi'
    rw [Finset.mem_Icc]; omega
  have h1 : (n : ℝ) = ((q.parts.sum : ℕ) : ℝ) := by rw [q.parts_sum]
  rw [h1, Finset.sum_multiset_count q.parts, Nat.cast_sum]
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro i _
    rw [smul_eq_mul]
    push_cast
    ring
  · intro i _ hi
    have : q.parts.count i = 0 := Multiset.count_eq_zero.mpr (by simpa using hi)
    simp [this]

lemma fallingP_pos : ∀ (n : ℕ) (y : ℝ), (n : ℝ) - 1 < y → 0 < fallingP y n
  | 0, _, _ => by show (0 : ℝ) < 1; norm_num
  | k + 1, y, h => by
      show 0 < y * fallingP (y - 1) k
      push_cast at h
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      apply mul_pos (by linarith)
      exact fallingP_pos k (y - 1) (by linarith)

lemma binom_pos (ν : ℝ) (hν : 0 < ν) (n : ℕ) : 0 < binomReal (ν + (n : ℝ) - 1) n := by
  unfold binomReal
  apply div_pos
  · exact fallingP_pos n _ (by linarith)
  · positivity

lemma binom_succ (ν : ℝ) (n : ℕ) :
    binomReal (ν + ((n + 1 : ℕ) : ℝ) - 1) (n + 1)
      = (ν + n) / ((n : ℝ) + 1) * binomReal (ν + (n : ℝ) - 1) n := by
  have e1 : ν + ((n + 1 : ℕ) : ℝ) - 1 - 1 = ν + (n : ℝ) - 1 := by push_cast; ring
  have e2 : ν + ((n + 1 : ℕ) : ℝ) - 1 = ν + n := by push_cast; ring
  unfold binomReal
  rw [show fallingP (ν + ((n + 1 : ℕ) : ℝ) - 1) (n + 1)
      = (ν + ((n + 1 : ℕ) : ℝ) - 1) * fallingP (ν + ((n + 1 : ℕ) : ℝ) - 1 - 1) n from rfl,
    e1, e2, Nat.factorial_succ]
  push_cast
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

lemma Nn_cast (n : ℕ) (s s' : Multiset ℕ) :
    ((Nn n s s' : ℕ) : ℝ) = ∑ c ∈ Finset.Icc 1 n,
      (c : ℝ) * (s.count c : ℝ) * (if mv c s = s' then 1 else 0) := by
  unfold Nn
  push_cast
  rfl

lemma ewens_step (ν : ℝ) (hν : 0 < ν) (n : ℕ) (q : Nat.Partition n) :
    ∑ r : Nat.Partition (n + 1), ewens ν (n + 1) r * ((Nn (n + 1) r.parts q.parts : ℕ) : ℝ)
      = ((n : ℝ) + 1) * ewens ν n q := by
  have hE : ∀ (k : ℕ) (p : Nat.Partition k), ewens ν k p
      = (binomReal (ν + (k : ℝ) - 1) k)⁻¹ * Pv ν (Finset.Icc 1 k) p.parts := fun _ _ => rfl
  have step1 : ∀ r : Nat.Partition (n + 1),
      ewens ν (n + 1) r * ((Nn (n + 1) r.parts q.parts : ℕ) : ℝ)
        = ∑ c ∈ Finset.Icc 1 (n + 1), (binomReal (ν + ((n + 1 : ℕ) : ℝ) - 1) (n + 1))⁻¹ *
          (Pv ν (Finset.Icc 1 (n + 1)) r.parts *
            ((c : ℝ) * (r.parts.count c : ℝ) * (if mv c r.parts = q.parts then 1 else 0))) := by
    intro r
    rw [hE, Nn_cast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [Finset.sum_congr rfl (fun r _ => step1 r), Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun c hc => by rw [← Finset.mul_sum, term_c ν n q c hc])]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_w, hE, binom_succ]
  have hsub : q.parts.toFinset ⊆ Finset.Icc 1 n := by
    intro i hi
    have hi' : i ∈ q.parts := Multiset.mem_toFinset.mp hi
    have h1 := q.parts_pos hi'
    have h2 : i ≤ n := by rw [← q.parts_sum]; exact Multiset.le_sum_of_mem hi'
    rw [Finset.mem_Icc]; omega
  have hsub' : q.parts.toFinset ⊆ Finset.Icc 1 (n + 1) := by
    intro i hi
    have := hsub hi
    rw [Finset.mem_Icc] at this ⊢
    omega
  rw [Pv_congr ν (Finset.Icc 1 (n + 1)) (Finset.Icc 1 n) q.parts hsub' hsub]
  have hB := binom_pos ν hν n
  have hνn : ν + (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end EwensAux8fb

open KellyReversibility.Genetics in
theorem solution (ν : ℝ) (hν : 0 < ν) (M m : ℕ)
    (hM : 2 ≤ M) (hm : 1 ≤ m) (hmM : m ≤ M)
    (x : Nat.Partition M → (Fin M → ℕ)) (hx : ∀ p, HasDescription (x p) p)
    (q : Nat.Partition m) :
    ∑ p : Nat.Partition M, ewens ν M p * sampleDescProb (x p) m q = ewens ν m q := by
  have main : ∀ k : ℕ, ∀ m' : ℕ, m' + k = M → ∀ q' : Nat.Partition m',
      ∑ p : Nat.Partition M, ewens ν M p * sampleDescProb (x p) m' q' = ewens ν m' q' := by
    intro k
    induction k with
    | zero =>
      intro m' h q'
      have hm' : m' = M := by omega
      subst hm'
      rw [Finset.sum_congr rfl (fun p _ => by rw [EwensAux8fb.sdp_self (x p) p q' (hx p)])]
      simp
    | succ k ih =>
      intro m' h q'
      have hlt : m' < M := by omega
      rw [Finset.sum_congr rfl (fun p _ => by rw [EwensAux8fb.tower (x p) m' hlt q'])]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hr : ∀ r : Nat.Partition (m' + 1),
          ∑ p : Nat.Partition M, ewens ν M p * (sampleDescProb (x p) (m' + 1) r *
            ((EwensAux8fb.Nn (m' + 1) r.parts q'.parts : ℕ) : ℝ) / ((m' : ℝ) + 1))
          = (∑ p : Nat.Partition M, ewens ν M p * sampleDescProb (x p) (m' + 1) r) *
            ((EwensAux8fb.Nn (m' + 1) r.parts q'.parts : ℕ) : ℝ) / ((m' : ℝ) + 1) := by
        intro r
        rw [Finset.sum_mul, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro p _
        ring
      rw [Finset.sum_congr rfl (fun r _ => hr r)]
      simp_rw [ih (m' + 1) (by omega)]
      rw [← Finset.sum_div, EwensAux8fb.ewens_step ν hν m' q']
      have : (m' : ℝ) + 1 ≠ 0 := by positivity
      field_simp
  exact main (M - m) m (by omega) q
