-- Prove2me | solution 1 for InterdepSOS.KHL.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-15T18:43:36.183729+00:00
-- url     : https://prove2.me/submissions/a2b6094b-0a3f-44ab-b256-8ba64248d0ea

import Definitions.Def_InterdepSOS_KHL_Setting
import Definitions.Def_InterdepSOS_KHL_Mechanisms

namespace InterdepSOS.KHL

open Finset

lemma khl_mono {n m k : ℕ} {v : Valuation n m} (hv : IsCombValuation k v)
    (i : Fin n) (T : Finset (Fin m)) {s s' : Signal n} (hs : InGrid k s) (hs' : InGrid k s')
    (h : s ≤ s') : v i T s ≤ v i T s' := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · rw [hv.2.1 i s hs, hv.2.1 i s' hs']
  · exact hv.2.2.1 i T hT s s' hs hs' h

lemma khl_keepOn_grid {n k : ℕ} (hk : 1 ≤ k) {s : Signal n} (hs : InGrid k s)
    (X : Finset (Fin n)) : InGrid k (keepOn X s) := by
  intro j; unfold keepOn; split_ifs
  · exact hs j
  · omega

lemma khl_keepOn_le {n : ℕ} (s : Signal n) (X : Finset (Fin n)) : keepOn X s ≤ s := by
  intro j; unfold keepOn; split_ifs <;> simp

lemma khl_update_keepOn_insert {n : ℕ} (s : Signal n) (Z : Finset (Fin n)) (j : Fin n) :
    Function.update (keepOn Z s) j (s j) = keepOn (insert j Z) s := by
  funext l
  by_cases hl : l = j
  · subst hl; simp [keepOn]
  · simp [Function.update_of_ne hl, keepOn, hl]

lemma khl_update_keepOn_zero {n : ℕ} (s : Signal n) (Z : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ Z) : Function.update (keepOn Z s) j 0 = keepOn Z s := by
  funext l
  by_cases hl : l = j
  · subst hl; simp [keepOn, hj]
  · simp [Function.update_of_ne hl]

lemma khl_submod {n k : ℕ} (hk : 1 ≤ k) {w : Signal n → ℝ} (hw : IsSOS k w)
    {s : Signal n} (hs : InGrid k s) (X Y : Finset (Fin n)) (hXY : Disjoint X Y) :
    w (keepOn (X ∪ Y) s) + w (keepOn ∅ s) ≤ w (keepOn X s) + w (keepOn Y s) := by
  induction Y using Finset.induction_on with
  | empty => simp
  | insert j Y hjY ih =>
    rw [Finset.disjoint_insert_right] at hXY
    have ih' := ih hXY.2
    have key := hw j 0 (s j) (keepOn (X ∪ Y) s) (keepOn Y s) (khl_keepOn_grid hk hs _)
      (khl_keepOn_grid hk hs _) (by simpa using hs j) (by
        intro l _; unfold keepOn; split_ifs with h1 h2 <;> simp_all)
    rw [zero_add, khl_update_keepOn_insert, khl_update_keepOn_insert,
      khl_update_keepOn_zero _ _ _ (by simp [hXY.1, hjY]),
      khl_update_keepOn_zero _ _ _ hjY] at key
    rw [Finset.union_insert]
    linarith

lemma khl_update_zero_eq {n : ℕ} (s : Signal n) (i : Fin n) :
    Function.update s i 0 = keepOn (univ.erase i) s := by
  funext l
  by_cases hl : l = i
  · subst hl; simp [keepOn]
  · simp [Function.update_of_ne hl, keepOn, hl]

lemma khl_count (n : ℕ) (i : Fin n) :
    (∑ B : Finset (Fin n), (if i ∈ B then (1 : ℝ) else 0)) = (2 ^ n : ℝ) / 2 := by
  have hinv : Function.Involutive (fun B : Finset (Fin n) => Bᶜ) := compl_compl
  have h1 : (∑ B : Finset (Fin n), (if i ∈ B then (1 : ℝ) else 0)) =
      ∑ B : Finset (Fin n), (if i ∈ Bᶜ then (1 : ℝ) else 0) :=
    (Equiv.sum_comp (Function.Involutive.toPerm _ hinv)
      (fun B => if i ∈ B then (1 : ℝ) else 0)).symm
  have h2 : (∑ B : Finset (Fin n), (if i ∈ B then (1 : ℝ) else 0)) +
      ∑ B : Finset (Fin n), (if i ∈ Bᶜ then (1 : ℝ) else 0) = 2 ^ n := by
    rw [← Finset.sum_add_distrib]
    have : ∀ B : Finset (Fin n), (if i ∈ B then (1 : ℝ) else 0) +
        (if i ∈ Bᶜ then (1 : ℝ) else 0) = 1 := by
      intro B; by_cases h : i ∈ B <;> simp [h]
    simp only [this]
    simp
  linarith

lemma khl_rs_single {n k : ℕ} (hk : 1 ≤ k) {w : Signal n → ℝ} (hw : IsSOS k w)
    {s : Signal n} (hs : InGrid k s) (hw0 : 0 ≤ w (keepOn ∅ s)) (i : Fin n) :
    (2 ^ n : ℝ) / 4 * w (Function.update s i 0) ≤
      ∑ B : Finset (Fin n), (if i ∈ B then w (keepOn Bᶜ s) else 0) := by
  classical
  let φ : Finset (Fin n) → Finset (Fin n) := fun B =>
    if i ∈ B then insert i Bᶜ else (Bᶜ).erase i
  have hφ : Function.Involutive φ := by
    intro B
    by_cases hB : i ∈ B
    · simp only [φ, hB, if_true, Finset.mem_insert, true_or]
      ext x; by_cases hx : x = i
      · subst hx; simp [hB]
      · simp [hx]
    · have : i ∉ (Bᶜ).erase i := by simp
      simp only [φ, hB, if_false, this]
      ext x; by_cases hx : x = i
      · subst hx; simp [hB]
      · simp [hx]
  have hS : (∑ B : Finset (Fin n), (if i ∈ B then w (keepOn Bᶜ s) else 0)) =
      ∑ B : Finset (Fin n), (if i ∈ B then w (keepOn (B.erase i) s) else 0) := by
    rw [← Equiv.sum_comp (Function.Involutive.toPerm _ hφ)]
    apply Finset.sum_congr rfl
    intro B _
    simp only [Function.Involutive.coe_toPerm]
    by_cases hB : i ∈ B
    · have h1 : i ∈ φ B := by simp [φ, hB]
      have h2 : (φ B)ᶜ = B.erase i := by
        ext x; by_cases hx : x = i
        · subst hx; simp [φ, hB]
        · simp [φ, hB, hx]
      simp [h1, hB, h2]
    · have h1 : i ∉ φ B := by simp [φ, hB]
      simp [h1, hB]
  have hpt : ∀ B : Finset (Fin n),
      (if i ∈ B then w (keepOn (univ.erase i) s) else 0) ≤
        (if i ∈ B then w (keepOn Bᶜ s) else 0) +
          (if i ∈ B then w (keepOn (B.erase i) s) else 0) := by
    intro B
    by_cases hB : i ∈ B
    · simp only [if_pos hB]
      have hd : Disjoint Bᶜ (B.erase i) := by
        rw [Finset.disjoint_left]; intro x hx hx'
        simp at hx hx'; exact hx hx'.2
      have hu : Bᶜ ∪ B.erase i = univ.erase i := by
        ext x; by_cases hx : x = i
        · subst hx; simp [hB]
        · simp [hx]; tauto
      have := khl_submod hk hw hs Bᶜ (B.erase i) hd
      rw [hu] at this
      linarith
    · simp [hB]
  have hsum := Finset.sum_le_sum (fun B (_ : B ∈ (univ : Finset (Finset (Fin n)))) => hpt B)
  rw [Finset.sum_add_distrib, ← hS] at hsum
  have hc : (∑ B : Finset (Fin n), (if i ∈ B then w (keepOn (univ.erase i) s) else 0)) =
      w (keepOn (univ.erase i) s) * ((2 ^ n : ℝ) / 2) := by
    rw [← khl_count n i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _; by_cases hB : i ∈ B <;> simp [hB]
  rw [hc] at hsum
  rw [khl_update_zero_eq]
  linarith

lemma khl_other_le {n m k : ℕ} (hk : 1 ≤ k) {v : Valuation n m} (hv : IsCombValuation k v)
    (hsos : ∀ i T, IsSOS k (v i T))
    {rsSel : Finset (Fin n) → Signal n → Allocation n m} (hrs : IsRSSelector k v rsSel)
    {s : Signal n} (hs : InGrid k s) (Tstar : Allocation n m)
    (hT : IsAllocOn Finset.univ Tstar) :
    other v Tstar s ≤ 4 * rsAvg v rsSel s := by
  classical
  have hB : ∀ B : Finset (Fin n),
      (∑ i, (if i ∈ B then v i (Tstar i) (keepOn Bᶜ s) else 0)) ≤
        welfare v (rsAlloc rsSel B s) s := by
    intro B
    obtain ⟨hA, hopt⟩ := hrs B s hs
    let T' : Allocation n m := fun i => if i ∈ B then Tstar i else ∅
    have hT' : IsAllocOn B T' := by
      refine ⟨?_, ?_⟩
      · intro a b hab
        simp only [T']
        split_ifs
        · exact hT.1 hab
        · exact disjoint_bot_right
        · exact disjoint_bot_left
        · exact disjoint_bot_left
      · intro a ha; simp [T', ha]
    have h1 := hopt T' hT'
    have h2 : (∑ i, (if i ∈ B then v i (Tstar i) (keepOn Bᶜ s) else 0)) =
        ∑ i ∈ B, v i (T' i) (keepOn Bᶜ s) := by
      rw [← Finset.sum_filter]
      have : (univ.filter fun i => i ∈ B) = B := by ext; simp
      rw [this]
      apply Finset.sum_congr rfl; intro i hi; simp [T', hi]
    have h3 : (∑ i ∈ B, v i (rsAlloc rsSel B s i) (keepOn Bᶜ s)) ≤
        ∑ i ∈ B, v i (rsAlloc rsSel B s i) s :=
      Finset.sum_le_sum fun i _ => khl_mono hv i _ (khl_keepOn_grid hk hs _) hs
        (khl_keepOn_le s _)
    have h4 : (∑ i ∈ B, v i (rsAlloc rsSel B s i) s) ≤ welfare v (rsAlloc rsSel B s) s :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hv.1 i _ s hs)
    linarith
  have hsingle : ∀ i, (2 ^ n : ℝ) / 4 * v i (Tstar i) (Function.update s i 0) ≤
      ∑ B : Finset (Fin n), (if i ∈ B then v i (Tstar i) (keepOn Bᶜ s) else 0) := by
    intro i
    exact khl_rs_single hk (hsos i (Tstar i)) hs
      (hv.1 i _ _ (khl_keepOn_grid hk hs _)) i
  have htot : (2 ^ n : ℝ) / 4 * other v Tstar s ≤
      ∑ B : Finset (Fin n), welfare v (rsAlloc rsSel B s) s := by
    unfold other
    rw [Finset.mul_sum]
    calc ∑ i, (2 ^ n : ℝ) / 4 * v i (Tstar i) (Function.update s i 0)
        ≤ ∑ i, ∑ B : Finset (Fin n), (if i ∈ B then v i (Tstar i) (keepOn Bᶜ s) else 0) :=
          Finset.sum_le_sum fun i _ => hsingle i
      _ = ∑ B : Finset (Fin n), ∑ i, (if i ∈ B then v i (Tstar i) (keepOn Bᶜ s) else 0) :=
          Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun B _ => hB B
  unfold rsAvg InterdepSOS.RSV.avgB
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [← mul_assoc]
  have : 4 * (2 ^ n : ℝ)⁻¹ = ((2 ^ n : ℝ) / 4)⁻¹ := by field_simp
  rw [this, le_inv_mul_iff₀ (by positivity)]
  linarith

lemma khl_rt_le {n m k : ℕ} {v : Valuation n m} (hv : IsCombValuation k v)
    {rtSel : ℕ → Signal n → Allocation n m} (hrt : IsRTSelector k v rtSel)
    {s : Signal n} (hs : InGrid k s) (Tstar : Allocation n m)
    (hT : IsAllocOn Finset.univ Tstar) (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (k - 1)) :
    (∑ i ∈ univ.filter (fun i => s i = ℓ),
      v i (Tstar i) (Function.update (0 : Signal n) i (s i))) ≤
      welfare v (rtAlloc rtSel ℓ s) s := by
  classical
  have hℓ' := Finset.mem_Icc.mp hℓ
  obtain ⟨hA, hopt⟩ := hrt ℓ hℓ s hs
  have hgR : InGrid k (rtProfile s ℓ) := by
    intro j; unfold rtProfile; split_ifs with h
    · have := hs j; omega
    · exact hs j
  have hRle : rtProfile s ℓ ≤ s := by
    intro j; unfold rtProfile; split_ifs with h
    · exact h
    · exact le_refl _
  let T' : Allocation n m := fun i => if i ∈ high s ℓ then Tstar i else ∅
  have hT' : IsAllocOn (high s ℓ) T' := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      simp only [T']
      split_ifs
      · exact hT.1 hab
      · exact disjoint_bot_right
      · exact disjoint_bot_left
      · exact disjoint_bot_left
    · intro a ha; simp [T', ha]
  have h1 := hopt T' hT'
  have hk0 : 0 < k := by omega
  have e1 : (∑ i ∈ univ.filter (fun i => s i = ℓ),
      v i (Tstar i) (Function.update (0 : Signal n) i (s i))) ≤
      ∑ i ∈ univ.filter (fun i => s i = ℓ), v i (Tstar i) (rtProfile s ℓ) := by
    apply Finset.sum_le_sum
    intro i hi
    have hsi : s i = ℓ := (Finset.mem_filter.mp hi).2
    apply khl_mono hv i _ _ hgR
    · intro j
      by_cases hj : j = i
      · subst hj; simp [rtProfile, hsi]
      · simp [Function.update_of_ne hj]
    · intro j
      by_cases hj : j = i
      · subst hj; simp; exact hs j
      · simp [Function.update_of_ne hj]; exact hk0
  have e2 : (∑ i ∈ univ.filter (fun i => s i = ℓ), v i (Tstar i) (rtProfile s ℓ)) ≤
      ∑ i ∈ high s ℓ, v i (Tstar i) (rtProfile s ℓ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [high, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      omega
    · intro i _ _; exact hv.1 i _ _ hgR
  have e3 : (∑ i ∈ high s ℓ, v i (Tstar i) (rtProfile s ℓ)) =
      ∑ i ∈ high s ℓ, v i (T' i) (rtProfile s ℓ) := by
    apply Finset.sum_congr rfl; intro i hi; simp [T', hi]
  have e4 : (∑ i ∈ high s ℓ, v i (rtAlloc rtSel ℓ s i) (rtProfile s ℓ)) ≤
      ∑ i ∈ high s ℓ, v i (rtAlloc rtSel ℓ s i) s :=
    Finset.sum_le_sum fun i _ => khl_mono hv i _ hgR hs hRle
  have e5 : (∑ i ∈ high s ℓ, v i (rtAlloc rtSel ℓ s i) s) ≤ welfare v (rtAlloc rtSel ℓ s) s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hv.1 i _ s hs)
  linarith

lemma khl_decomp {n m k : ℕ} (hk : 1 ≤ k) {v : Valuation n m} (hv : IsCombValuation k v)
    (hsos : ∀ i T, IsSOS k (v i T)) {s : Signal n} (hs : InGrid k s) (T : Allocation n m) :
    welfare v T s ≤ other v T s + self k v T s := by
  classical
  have hself : self k v T s = ∑ i, (if s i ∈ Finset.Icc 1 (k - 1) then
      v i (T i) (Function.update (0 : Signal n) i (s i)) else 0) := by
    unfold self
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq]
  rw [hself]
  unfold other welfare
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h0 : InGrid k (0 : Signal n) := fun j => by simp; omega
  by_cases hi : s i ∈ Finset.Icc 1 (k - 1)
  · rw [if_pos hi]
    have key := hsos i (T i) i 0 (s i) s 0 hs h0 (by simpa using hs i)
      (fun l _ => by simp)
    simp only [zero_add, Function.update_eq_self] at key
    have : Function.update (0 : Signal n) i 0 = 0 := by simp
    rw [this] at key
    have := hv.1 i (T i) 0 h0
    linarith
  · rw [if_neg hi]
    have : s i = 0 := by
      have := hs i; simp only [Finset.mem_Icc] at hi; omega
    have he : Function.update s i 0 = s := by rw [← this]; simp
    rw [he]; simp

theorem theorem_6_1 {n m : ℕ} (k : ℕ) (hk : 1 ≤ k) (v : Valuation n m)
    (hv : IsCombValuation k v) (hsos : ∀ i T, IsSOS k (v i T))
    (rtSel : ℕ → Signal n → Allocation n m) (hrt : IsRTSelector k v rtSel)
    (rsSel : Finset (Fin n) → Signal n → Allocation n m) (hrs : IsRSSelector k v rsSel) :
    (∀ ℓ ∈ Finset.Icc 1 (k - 1),
        IsExPostIC k v (rtAlloc rtSel ℓ) (rtPay v rtSel ℓ) ∧
        IsExPostIR k v (rtAlloc rtSel ℓ) (rtPay v rtSel ℓ)) ∧
    (∀ B : Finset (Fin n),
        IsExPostIC k v (rsAlloc rsSel B) 0 ∧ IsExPostIR k v (rsAlloc rsSel B) 0) ∧
    ∀ s : Signal n, InGrid k s → ∀ Tstar : Allocation n m, IsAllocOn Finset.univ Tstar →
      welfare v Tstar s ≤ ((k : ℝ) + 3) * khlWelfare k v rtSel rsSel s := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- Random Threshold
    intro ℓ hℓ
    have hℓ' := Finset.mem_Icc.mp hℓ
    have hgu : ∀ (s : Signal n) (i : Fin n) (y : ℕ), InGrid k s → y < k →
        InGrid k (Function.update s i y) := by
      intro s i y hs hy j
      by_cases hj : j = i
      · subst hj; simpa using hy
      · simp [Function.update_of_ne hj]; exact hs j
    have hempty : ∀ s' : Signal n, InGrid k s' → ∀ i, s' i < ℓ → rtAlloc rtSel ℓ s' i = ∅ := by
      intro s' hs' i hi
      apply (hrt ℓ hℓ s' hs').1.2 i
      simp [high]; omega
    have hutil : ∀ i s y, utility v (rtAlloc rtSel ℓ) (rtPay v rtSel ℓ) i s y =
        v i (rtAlloc rtSel ℓ (Function.update s i y) i) s -
          v i (rtAlloc rtSel ℓ (Function.update s i y) i) (Function.update s i (ℓ - 1)) := by
      intro i s y
      simp [utility, rtPay]
    have hIR : ∀ i s, InGrid k s → 0 ≤ utility v (rtAlloc rtSel ℓ) (rtPay v rtSel ℓ) i s (s i) := by
      intro i s hs
      rw [hutil]
      have hs2 := hgu s i (ℓ - 1) hs (by omega)
      by_cases hsi : s i < ℓ
      · rw [Function.update_eq_self, hempty s hs i hsi, hv.2.1 i s hs, hv.2.1 i _ hs2]
        simp
      · have : Function.update s i (ℓ - 1) ≤ s := by
          intro j; by_cases hj : j = i
          · subst hj; simp; omega
          · simp [Function.update_of_ne hj]
        have := khl_mono hv i (rtAlloc rtSel ℓ (Function.update s i (s i)) i) hs2 hs this
        linarith
    refine ⟨?_, hIR⟩
    intro i s y hs hy
    have hIRs := hIR i s hs
    rw [hutil] at hIRs
    rw [hutil, hutil]
    have hs2 := hgu s i (ℓ - 1) hs (by omega)
    have hsy := hgu s i y hs hy
    by_cases hyl : y < ℓ
    · have := hempty _ hsy i (by simpa using hyl)
      rw [this, hv.2.1 i s hs, hv.2.1 i _ hs2, sub_self]
      exact hIRs
    · by_cases hsi : s i < ℓ
      · have : s ≤ Function.update s i (ℓ - 1) := by
          intro j; by_cases hj : j = i
          · subst hj; simp; omega
          · simp [Function.update_of_ne hj]
        have := khl_mono hv i (rtAlloc rtSel ℓ (Function.update s i y) i) hs hs2 this
        linarith
      · have hp : rtProfile (Function.update s i y) ℓ = rtProfile (Function.update s i (s i)) ℓ := by
          funext j
          by_cases hj : j = i
          · subst hj
            have h1 : ℓ ≤ y := by omega
            have h2 : ℓ ≤ s j := by omega
            simp [rtProfile, h1, h2]
          · simp [rtProfile, Function.update_of_ne hj]
        have : rtAlloc rtSel ℓ (Function.update s i y) = rtAlloc rtSel ℓ (Function.update s i (s i)) := by
          simp only [rtAlloc, hp]
        rw [this]
  · -- Random Sampling
    intro B
    have hgu : ∀ (s : Signal n) (i : Fin n) (y : ℕ), InGrid k s → y < k →
        InGrid k (Function.update s i y) := by
      intro s i y hs hy j
      by_cases hj : j = i
      · subst hj; simpa using hy
      · simp [Function.update_of_ne hj]; exact hs j
    refine ⟨?_, ?_⟩
    · intro i s y hs hy
      simp only [utility, Pi.zero_apply, sub_zero]
      by_cases hiB : i ∈ B
      · have hk' : keepOn Bᶜ (Function.update s i y) = keepOn Bᶜ (Function.update s i (s i)) := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [keepOn, hiB]
          · simp [keepOn, Function.update_of_ne hj]
        have : rsAlloc rsSel B (Function.update s i y) =
            rsAlloc rsSel B (Function.update s i (s i)) := by
          simp only [rsAlloc, hk']
        rw [this]
      · have h1 := (hrs B _ (hgu s i y hs hy)).1.2 i hiB
        have h2 := (hrs B _ (hgu s i (s i) hs (hs i))).1.2 i hiB
        rw [h1, h2]
    · intro i s hs
      simp only [utility, Pi.zero_apply, sub_zero]
      exact hv.1 i _ s hs
  · -- welfare bound
    intro s hs Tstar hT
    have hdec := khl_decomp hk hv hsos hs Tstar
    have hoth := khl_other_le hk hv hsos hrs hs Tstar hT
    have hself : self k v Tstar s ≤
        ∑ ℓ ∈ Finset.Icc 1 (k - 1), welfare v (rtAlloc rtSel ℓ s) s := by
      unfold self
      exact Finset.sum_le_sum fun ℓ hℓ => khl_rt_le hv hrt hs Tstar hT ℓ hℓ
    have h1 : ((k : ℝ) + 3) * pRT k = (k : ℝ) - 1 := by
      unfold pRT; field_simp
    have h2 : ((k : ℝ) + 3) * (1 - pRT k) = 4 := by
      unfold pRT; field_simp; ring
    have h3 : ((k : ℝ) - 1) * rtAvg k v rtSel s =
        ∑ ℓ ∈ Finset.Icc 1 (k - 1), welfare v (rtAlloc rtSel ℓ s) s := by
      unfold rtAvg
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have : k = 1 := by omega
        subst this
        simp
      · have hc : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub hk]; simp
        rw [← hc, ← mul_assoc, mul_inv_cancel₀ (by
          have : (1 : ℕ) ≤ k - 1 := by omega
          exact_mod_cast (by omega : k - 1 ≠ 0)), one_mul]
    have hfin : ((k : ℝ) + 3) * khlWelfare k v rtSel rsSel s =
        (∑ ℓ ∈ Finset.Icc 1 (k - 1), welfare v (rtAlloc rtSel ℓ s) s) + 4 * rsAvg v rsSel s := by
      unfold khlWelfare
      linear_combination (rtAvg k v rtSel s) * h1 + (rsAvg v rsSel s) * h2 + h3
    rw [hfin]
    linarith

end InterdepSOS.KHL


-- Platform entry point: restates the target verbatim.
namespace InterdepSOS.KHL
theorem _root_.solution {n m : ℕ} (k : ℕ) (hk : 1 ≤ k) (v : Valuation n m)
    (hv : IsCombValuation k v) (hsos : ∀ i T, IsSOS k (v i T))
    (rtSel : ℕ → Signal n → Allocation n m) (hrt : IsRTSelector k v rtSel)
    (rsSel : Finset (Fin n) → Signal n → Allocation n m) (hrs : IsRSSelector k v rsSel) :
    (∀ ℓ ∈ Finset.Icc 1 (k - 1),
        IsExPostIC k v (rtAlloc rtSel ℓ) (rtPay v rtSel ℓ) ∧
        IsExPostIR k v (rtAlloc rtSel ℓ) (rtPay v rtSel ℓ)) ∧
    (∀ B : Finset (Fin n),
        IsExPostIC k v (rsAlloc rsSel B) 0 ∧ IsExPostIR k v (rsAlloc rsSel B) 0) ∧
    ∀ s : Signal n, InGrid k s → ∀ Tstar : Allocation n m, IsAllocOn Finset.univ Tstar →
      welfare v Tstar s ≤ ((k : ℝ) + 3) * khlWelfare k v rtSel rsSel s := by
  apply @InterdepSOS.KHL.theorem_6_1 <;> assumption
end InterdepSOS.KHL
