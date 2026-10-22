-- Prove2me | solution 1 for MultiChoiceSecretary.Alg.card_inter_top_binomial
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:48:06.671229+00:00
-- url     : https://prove2.me/submissions/c5600f84-f47f-405a-917c-b3cde4567601

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting
set_option autoImplicit false
open MultiChoiceSecretary.Alg

lemma mc_perm_exists {n : ℕ} (B B' : Finset (Fin n)) (h : B.card = B'.card) :
    ∃ τ : Equiv.Perm (Fin n), B.map τ.toEmbedding = B' := by
  classical
  have e : {x // x ∈ B} ≃ {x // x ∈ B'} := Fintype.equivOfCardEq (by simp [h])
  refine ⟨Equiv.extendSubtype e, ?_⟩
  ext y
  simp only [Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Equiv.extendSubtype_apply_of_mem e x hx]
    exact (e ⟨x, hx⟩).2
  · intro hy
    refine ⟨(e.symm ⟨y, hy⟩).1, (e.symm ⟨y, hy⟩).2, ?_⟩
    rw [Equiv.extendSubtype_apply_of_mem e _ (e.symm ⟨y, hy⟩).2]
    simp

def mcP (n m : ℕ) : Finset (Fin n) := Finset.univ.filter (fun t : Fin n => t.val < m)

def mcImg {n : ℕ} (m : ℕ) (π : Equiv.Perm (Fin n)) : Finset (Fin n) := (mcP n m).map π.toEmbedding

lemma mc_img_card {n : ℕ} (m : ℕ) (hm : m ≤ n) (π : Equiv.Perm (Fin n)) : (mcImg m π).card = m := by
  unfold mcImg mcP
  rw [Finset.card_map]
  have h2 : (Finset.univ.filter (fun t : Fin n => t.val < m)).card = min n m := Fin.card_filter_val_lt
  omega

lemma mc_img_mul {n : ℕ} (m : ℕ) (σ π : Equiv.Perm (Fin n)) :
    mcImg m (σ * π) = (mcImg m π).map σ.toEmbedding := by
  unfold mcImg
  rw [Finset.map_map]
  rfl

lemma mc_fibre_const {n : ℕ} (m : ℕ) (B B' : Finset (Fin n)) (h : B.card = B'.card) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => mcImg m π = B)).card =
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => mcImg m π = B')).card := by
  classical
  obtain ⟨τ, hτ⟩ := mc_perm_exists B B' h
  apply Finset.card_bij (fun π _ => τ * π)
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    rw [mc_img_mul, hπ, hτ]
  · intro π _ π' _ h
    exact mul_left_cancel h
  · intro π' hπ'
    refine ⟨τ⁻¹ * π', ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ' ⊢
    rw [mc_img_mul, hπ', ← hτ, Finset.map_map]
    ext y
    simp

lemma mc_sum_fibre {n : ℕ} (m : ℕ) (hm : m ≤ n) (g : Finset (Fin n) → ℝ) :
    ((n.choose m : ℕ) : ℝ) * ∑ π : Equiv.Perm (Fin n), g (mcImg m π) =
      (n.factorial : ℝ) * ∑ B ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)), g B := by
  classical
  set Pm := Finset.powersetCard m (Finset.univ : Finset (Fin n)) with hPm
  have hmaps : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), mcImg m π ∈ Pm := by
    intro π _
    rw [hPm, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, mc_img_card m hm π⟩
  set c : Finset (Fin n) → ℕ := fun B =>
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => mcImg m π = B)).card with hc
  have h1 : ∑ π : Equiv.Perm (Fin n), g (mcImg m π) = ∑ B ∈ Pm, (c B : ℝ) * g B := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl
    intro B _
    rw [Finset.sum_congr rfl (fun π hπ => by rw [(Finset.mem_filter.1 hπ).2])]
    simp [hc, mul_comm]
  have h2 : ∑ B ∈ Pm, c B = n.factorial := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Equiv.Perm (Fin n)))) hmaps
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at this
    rw [← this]
  have hne : Pm.Nonempty := by
    rw [hPm, Finset.powersetCard_nonempty]
    simpa using hm
  obtain ⟨B0, hB0⟩ := hne
  have hcard : ∀ B ∈ Pm, B.card = m := fun B hB => (Finset.mem_powersetCard.1 hB).2
  have hconst : ∀ B ∈ Pm, c B = c B0 := by
    intro B hB
    exact mc_fibre_const m B B0 (by rw [hcard B hB, hcard B0 hB0])
  have h3 : n.factorial = n.choose m * c B0 := by
    rw [← h2, Finset.sum_congr rfl hconst, Finset.sum_const, hPm, Finset.card_powersetCard]
    simp
  rw [h1]
  have h4 : ∑ B ∈ Pm, (c B : ℝ) * g B = (c B0 : ℝ) * ∑ B ∈ Pm, g B := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    rw [hconst B hB]
  rw [h4]
  have h5 : (n.factorial : ℝ) = n.choose m * c B0 := by exact_mod_cast h3
  rw [h5]
  ring

lemma mc_prefixSet (S : Finset ℝ) (π : Equiv.Perm (Fin S.card)) (m : ℕ) :
    prefixSet S π m = (mcImg m π).map (S.orderEmbOfFin rfl).toEmbedding := by
  ext y
  simp only [prefixSet, mcImg, mcP, arrivals, Finset.mem_image, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨π t, ⟨t, ht, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, rfl⟩

lemma mc_binom (n : ℕ) (m : Fin (n + 1)) :
    ((PMF.binomial (1 / 2) half_le_one n) m).toReal = (n.choose m.val : ℝ) / 2 ^ n := by
  have hm : m.val ≤ n := Nat.lt_succ_iff.1 m.isLt
  have h := PMF.binomial_apply_of_le (x := (1 / 2 : NNReal)) hm half_le_one
  rw [Fin.ofNat_eq_cast, Fin.cast_val_eq_self] at h
  have e : (((1 / 2 : NNReal)) : ℝ) = 1 / 2 := by norm_num
  rw [e] at h
  rw [← h, ENNReal.toReal_ofReal (by
    have : (0:ℝ) ≤ 1 - 1 / 2 := by norm_num
    positivity)]
  have : (n.choose m.val : ℝ) / 2 ^ n = (n.choose m.val : ℝ) * (1 / 2) ^ m.val * (1 / 2) ^ (n - m.val) := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm, one_div, inv_pow, div_eq_mul_inv]
  rw [this]
  norm_num

lemma mc_pc_sum (S : Finset ℝ) (f : Finset ℝ → ℝ) (m : ℕ) :
    ∑ B ∈ Finset.powersetCard m (Finset.univ : Finset (Fin S.card)),
        f (B.map (S.orderEmbOfFin rfl).toEmbedding) =
      ∑ A ∈ Finset.powersetCard m S, f A := by
  have h : Finset.powersetCard m S =
      (Finset.powersetCard m (Finset.univ : Finset (Fin S.card))).map
        (Finset.mapEmbedding (S.orderEmbOfFin rfl).toEmbedding).toEmbedding := by
    rw [← Finset.powersetCard_map, Finset.map_orderEmbOfFin_univ]
  rw [h, Finset.sum_map]
  rfl

lemma mc_pc_total (S : Finset ℝ) (f : Finset ℝ → ℝ) :
    ∑ m : Fin (S.card + 1), ∑ A ∈ Finset.powersetCard m.val S, f A = ∑ A ∈ S.powerset, f A := by
  rw [Fin.sum_univ_eq_sum_range (fun m => ∑ A ∈ Finset.powersetCard m S, f A) (S.card + 1)]
  have hmaps : ∀ A ∈ S.powerset, A.card ∈ Finset.range (S.card + 1) := by
    intro A hA
    rw [Finset.mem_range]
    have := Finset.card_le_card (Finset.mem_powerset.1 hA)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.powersetCard_eq_filter]

theorem mc_splitAvg (S : Finset ℝ) (f : Finset ℝ → ℝ) :
    splitAvg S f = (1 / 2 : ℝ) ^ S.card * ∑ A ∈ S.powerset, f A := by
  unfold splitAvg SecretaryWD.DiscUpper.uniformAvg
  set n := S.card with hn
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have key : ∀ m : Fin (n + 1),
      (1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n),
        ((PMF.binomial (1 / 2) half_le_one n) m).toReal * f (prefixSet S π m)
      = (1 / 2 : ℝ) ^ n * ∑ A ∈ Finset.powersetCard m.val S, f A := by
    intro m
    have hm : m.val ≤ n := Nat.lt_succ_iff.1 m.isLt
    have hC : (0 : ℝ) < n.choose m.val := by exact_mod_cast Nat.choose_pos hm
    rw [← Finset.mul_sum, mc_binom]
    have h1 : ∑ π : Equiv.Perm (Fin n), f (prefixSet S π m) =
        ∑ π : Equiv.Perm (Fin n), (fun B : Finset (Fin n) => f (B.map (S.orderEmbOfFin rfl).toEmbedding)) (mcImg m.val π) := by
      apply Finset.sum_congr rfl
      intro π _
      rw [mc_prefixSet]
    rw [h1]
    have h2 := mc_sum_fibre m.val hm (fun B : Finset (Fin n) => f (B.map (S.orderEmbOfFin rfl).toEmbedding))
    rw [mc_pc_sum] at h2
    try simp only at h2
    have h3 : ∑ π : Equiv.Perm (Fin n), f ((mcImg m.val π).map (S.orderEmbOfFin rfl).toEmbedding)
        = (n.factorial : ℝ) / n.choose m.val * ∑ A ∈ Finset.powersetCard m.val S, f A := by
      field_simp
      linarith
    try simp only at h3
    rw [h3]
    have e : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
    field_simp
    linear_combination (-(∑ A ∈ Finset.powersetCard m.val S, f A)) * e
  calc 1 / (n.factorial : ℝ) * ∑ π : Equiv.Perm (Fin n), ∑ m : Fin (n + 1),
        ((PMF.binomial (1 / 2) half_le_one n) m).toReal * f (prefixSet S π m)
      = ∑ m : Fin (n + 1), (1 / (n.factorial : ℝ)) * ∑ π : Equiv.Perm (Fin n),
        ((PMF.binomial (1 / 2) half_le_one n) m).toReal * f (prefixSet S π m) := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ = ∑ m : Fin (n + 1), (1 / 2 : ℝ) ^ n * ∑ A ∈ Finset.powersetCard m.val S, f A :=
        Finset.sum_congr rfl (fun m _ => key m)
    _ = (1 / 2 : ℝ) ^ n * ∑ A ∈ S.powerset, f A := by
        rw [← Finset.mul_sum, mc_pc_total]

lemma mc_topK_sub (S : Finset ℝ) (k : ℕ) : topK S k ⊆ S := by
  intro x hx
  unfold topK at hx
  rw [List.mem_toFinset] at hx
  exact (Finset.mem_sort _).1 (List.mem_of_mem_take hx)

lemma mc_topK_nodup (S : Finset ℝ) (k : ℕ) : ((S.sort (· ≥ ·)).take k).Nodup :=
  (Finset.sort_nodup _ _).sublist (List.take_sublist _ _)

lemma mc_topK_card (S : Finset ℝ) (k : ℕ) (hk : k ≤ S.card) : (topK S k).card = k := by
  unfold topK
  rw [List.toFinset_card_of_nodup (mc_topK_nodup S k), List.length_take, Finset.length_sort]
  omega

lemma mc_topSum (S : Finset ℝ) (k : ℕ) : topSum S k = ∑ x ∈ topK S k, x := by
  unfold topSum topK
  rw [List.sum_toFinset _ (mc_topK_nodup S k)]
  simp

lemma mc_inter_sum {T S : Finset ℝ} (hT : T ⊆ S) (F : Finset ℝ → ℝ) :
    ∑ A ∈ S.powerset, F (A ∩ T) = 2 ^ (S \ T).card * ∑ B ∈ T.powerset, F B := by
  classical
  have h1 : ∑ A ∈ S.powerset, F (A ∩ T) = ∑ p ∈ T.powerset ×ˢ (S \ T).powerset, F p.1 := by
    symm
    apply Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun A => (A ∩ T, A \ T))
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_powerset] at hp ⊢
      exact Finset.union_subset (hp.1.trans hT) (hp.2.trans Finset.sdiff_subset)
    · intro A hA
      simp only [Finset.mem_product, Finset.mem_powerset] at hA ⊢
      exact ⟨Finset.inter_subset_right, Finset.sdiff_subset_sdiff hA subset_rfl⟩
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_powerset] at hp
      obtain ⟨hB, hC⟩ := hp
      have hB' : ∀ x, x ∈ p.1 → x ∈ T := fun x hx => hB hx
      have hC' : ∀ x, x ∈ p.2 → x ∈ S ∧ x ∉ T := fun x hx => Finset.mem_sdiff.1 (hC hx)
      refine Prod.ext ?_ ?_
      · ext x; simp only [Finset.mem_inter, Finset.mem_union]; have := hB' x; have := hC' x; tauto
      · ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; have := hB' x; have := hC' x; tauto
    · intro A hA
      ext x; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]; tauto
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_powerset] at hp
      obtain ⟨hB, hC⟩ := hp
      have hB' : ∀ x, x ∈ p.1 → x ∈ T := fun x hx => hB hx
      have hC' : ∀ x, x ∈ p.2 → x ∈ S ∧ x ∉ T := fun x hx => Finset.mem_sdiff.1 (hC hx)
      congr 1
      ext x; simp only [Finset.mem_inter, Finset.mem_union]; have := hB' x; have := hC' x; tauto
  rw [h1, Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B _
  push_cast
  ring

lemma mc_count (T : Finset ℝ) (x : ℝ) (hx : x ∈ T) (r : ℕ) :
    ((Finset.powersetCard (r + 1) T).filter (fun B => x ∈ B)).card = (T.card - 1).choose r := by
  classical
  have h : (Finset.powersetCard (r + 1) T).filter (fun B => x ∈ B) =
      (Finset.powersetCard r (T.erase x)).image (insert x) := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image]
    constructor
    · rintro ⟨⟨hB, hc⟩, hxB⟩
      refine ⟨B.erase x, ⟨Finset.erase_subset_erase x hB, ?_⟩, Finset.insert_erase hxB⟩
      rw [Finset.card_erase_of_mem hxB, hc]; rfl
    · rintro ⟨C, ⟨hC, hc⟩, rfl⟩
      have hxC : x ∉ C := fun h => (Finset.notMem_erase x T) (hC h)
      refine ⟨⟨Finset.insert_subset hx (hC.trans (Finset.erase_subset x T)), ?_⟩, Finset.mem_insert_self _ _⟩
      rw [Finset.card_insert_of_notMem hxC, hc]
  rw [h, Finset.card_image_of_injOn, Finset.card_powersetCard, Finset.card_erase_of_mem hx]
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_powersetCard] at ha hb
  have hxa : x ∉ a := fun h => (Finset.notMem_erase x T) (ha.1 h)
  have hxb : x ∉ b := fun h => (Finset.notMem_erase x T) (hb.1 h)
  have := congrArg (fun s => s.erase x) hab
  simpa [Finset.erase_insert hxa, Finset.erase_insert hxb] using this

lemma mc_double (T : Finset ℝ) (r : ℕ) :
    ∑ B ∈ Finset.powersetCard (r + 1) T, ∑ x ∈ B, x = ((T.card - 1).choose r : ℝ) * ∑ x ∈ T, x := by
  classical
  have h1 : ∀ B ∈ Finset.powersetCard (r + 1) T, ∑ x ∈ B, x = ∑ x ∈ T, if x ∈ B then x else 0 := by
    intro B hB
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (Finset.mem_powersetCard.1 hB).1]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_filter, Finset.sum_const, mc_count T x hx r]
  simp [mul_comm]

theorem mc_T1 (S : Finset ℝ) :
    ∀ A ⊆ S, splitAvg S (fun Y => if Y = A then 1 else 0) = (1 / 2 : ℝ) ^ S.card := by
  intro A hA
  rw [mc_splitAvg]
  simp [Finset.sum_ite_eq', Finset.mem_powerset, hA]

theorem mc_T2 (S : Finset ℝ) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ S.card) :
    ∀ r : ℕ, splitAvg S (fun Y => if (Y ∩ topK S k).card = r then 1 else 0) =
      (k.choose r : ℝ) / 2 ^ k := by
  intro r
  rw [mc_splitAvg]
  have hT := mc_topK_sub S k
  have h := mc_inter_sum hT (fun B : Finset ℝ => if B.card = r then (1 : ℝ) else 0)
  try simp only at h
  rw [h]
  have hc : ∑ B ∈ (topK S k).powerset, (if B.card = r then (1 : ℝ) else 0) = (k.choose r : ℝ) := by
    rw [Finset.sum_boole, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard, mc_topK_card S k hkn]
  rw [hc, Finset.card_sdiff_of_subset hT, mc_topK_card S k hkn]
  obtain ⟨d, hd⟩ : ∃ d, S.card = k + d := ⟨S.card - k, by omega⟩
  rw [hd, Nat.add_sub_cancel_left, pow_add]
  have e1 : (1 / 2 : ℝ) ^ d * 2 ^ d = 1 := by rw [← mul_pow]; norm_num
  have e2 : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
  have e3 : (k.choose r : ℝ) / 2 ^ k = (k.choose r : ℝ) * (1 / 2) ^ k := by
    rw [one_div, inv_pow, div_eq_mul_inv]
  rw [e3]
  linear_combination ((k.choose r : ℝ) * (1 / 2) ^ k) * e1

theorem mc_T3 (S : Finset ℝ) (hS : ∀ x ∈ S, 0 ≤ x) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ S.card) :
    ∀ r : ℕ, splitAvg S (fun Y => if (Y ∩ topK S k).card = r then modVal S k Y else 0) =
      (k.choose r : ℝ) / 2 ^ k * ((r : ℝ) / k * topSum S k) := by
  intro r
  rw [mc_splitAvg]
  have hT := mc_topK_sub S k
  have h := mc_inter_sum hT (fun B : Finset ℝ => if B.card = r then (∑ x ∈ B, x) else 0)
  have h' : ∀ A : Finset ℝ, (if (A ∩ topK S k).card = r then modVal S k A else 0) =
      (fun B : Finset ℝ => if B.card = r then (∑ x ∈ B, x) else 0) (A ∩ topK S k) := by
    intro A; simp only [modVal]
  rw [Finset.sum_congr rfl (fun A _ => h' A), h]
  have hc : ∑ B ∈ (topK S k).powerset, (if B.card = r then (∑ x ∈ B, x) else 0)
      = ((r : ℝ) / k * topSum S k) * (k.choose r : ℝ) := by
    rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter, mc_topSum]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [mc_double, mc_topK_card S k hkn]
      have hkk : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hid := Nat.add_one_mul_choose_eq k' r'
      have hid' : ((k' + 1 : ℕ) : ℝ) * (k'.choose r' : ℝ) = ((k' + 1).choose (r' + 1) : ℝ) * ((r' + 1 : ℕ) : ℝ) := by
        exact_mod_cast hid
      simp only [Nat.add_sub_cancel]
      push_cast at hid' hkk ⊢
      field_simp
      linear_combination (∑ x ∈ topK S (k' + 1), x) * hid'
  rw [hc, Finset.card_sdiff_of_subset hT, mc_topK_card S k hkn]
  obtain ⟨d, hd⟩ : ∃ d, S.card = k + d := ⟨S.card - k, by omega⟩
  rw [hd, Nat.add_sub_cancel_left, pow_add]
  have e1 : (1 / 2 : ℝ) ^ d * 2 ^ d = 1 := by rw [← mul_pow]; norm_num
  have e2 : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
  have e3 : (k.choose r : ℝ) / 2 ^ k = (k.choose r : ℝ) * (1 / 2) ^ k := by
    rw [one_div, inv_pow, div_eq_mul_inv]
  rw [e3]
  linear_combination (((r : ℝ) / k * topSum S k) * (k.choose r : ℝ) * (1 / 2) ^ k) * e1

theorem solution (S : Finset ℝ) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ S.card) :
    ∀ r : ℕ, splitAvg S (fun Y => if (Y ∩ topK S k).card = r then 1 else 0) =
      (k.choose r : ℝ) / 2 ^ k := mc_T2 S k hk hkn
