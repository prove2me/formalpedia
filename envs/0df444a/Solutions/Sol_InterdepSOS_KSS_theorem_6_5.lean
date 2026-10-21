-- Prove2me | solution 1 for InterdepSOS.KSS.theorem_6_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:11:56.807747+00:00
-- url     : https://prove2.me/submissions/9e574e33-3592-4630-83ec-7da6d8e026b4

import Mathlib
import Definitions.Def_InterdepSOS_KSS_Setting
import Definitions.Def_InterdepSOS_KSS_Mechanisms
set_option autoImplicit false

/-! Lemmas `khl_*` in the first namespace block are taken from the accepted proof of
`InterdepSOS.KHL.theorem_6_1` by @frknbls (https://prove2.me/submissions/a2b6094b-0a3f-44ab-b256-8ba64248d0ea),
lightly adapted (`khl_rs_icir` is the Random Sampling branch of that proof, extracted as a lemma). -/

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
    welfare v T s ≤ other v T s + InterdepSOS.KHL.self k v T s := by
  classical
  have hself : InterdepSOS.KHL.self k v T s = ∑ i, (if s i ∈ Finset.Icc 1 (k - 1) then
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


lemma khl_rs_icir {n m k : ℕ} {v : Valuation n m} (hv : IsCombValuation k v)
    {rsSel : Finset (Fin n) → Signal n → Allocation n m} (hrs : IsRSSelector k v rsSel)
    (B : Finset (Fin n)) :
    IsExPostIC k v (rsAlloc rsSel B) 0 ∧ IsExPostIR k v (rsAlloc rsSel B) 0 := by
  classical
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

end InterdepSOS.KHL

open InterdepSOS.KSS

/-- one-dimensional bound: a concave-increment, monotone, nonnegative function on `[0,K)`
satisfies `g t ≤ 2 g c` whenever `c ≤ t < 2c`. -/
lemma agent_bound (g : ℕ → ℝ) (K : ℕ) (g0 : 0 ≤ g 0)
    (gmono : ∀ a b, a ≤ b → b < K → g a ≤ g b)
    (gcon : ∀ c δ, c + δ < K → g (c + δ) - g c ≤ g δ - g 0)
    (c t : ℕ) (hct : c ≤ t) (ht : t < 2 * c) (htK : t < K) : g t ≤ 2 * g c := by
  obtain ⟨δ, rfl⟩ := Nat.exists_eq_add_of_le hct
  have h1 := gcon c δ htK
  have h2 := gmono δ c (by omega) (by omega)
  linarith

theorem display9_aux {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (hv : InterdepSOS.KHL.IsCombValuation (2 ^ q) v) (hss : ∀ i T, IsStrongSOS (2 ^ q) (v i T))
    (s : InterdepSOS.KHL.Signal n) (hs : InterdepSOS.KHL.InGrid (2 ^ q) s) (T : InterdepSOS.KHL.Allocation n m) :
    InterdepSOS.KHL.self (2 ^ q) v T s ≤
      2 * ∑ ℓ ∈ Finset.Icc 1 q,
        ∑ i ∈ Finset.univ.filter (fun i => 2 ^ (ℓ - 1) ≤ s i ∧ s i < 2 ^ ℓ),
          v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i (2 ^ (ℓ - 1))) := by
  classical
  obtain ⟨hnn, hemp, hmono, -⟩ := hv
  have hgrid0 : ∀ (i : Fin n) (t : ℕ), t < 2 ^ q →
      InterdepSOS.KHL.InGrid (2 ^ q) (Function.update (0 : InterdepSOS.KHL.Signal n) i t) := by
    intro i t ht j
    by_cases hj : j = i
    · subst hj; simpa using ht
    · simp only [Function.update_of_ne hj, Pi.zero_apply]; positivity
  have gnn : ∀ (i : Fin n) (t : ℕ), t < 2 ^ q →
      0 ≤ v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i t) :=
    fun i t ht => hnn i (T i) _ (hgrid0 i t ht)
  have gmono : ∀ (i : Fin n) (a b : ℕ), a ≤ b → b < 2 ^ q →
      v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i a) ≤
        v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i b) := by
    intro i a b hab hb
    by_cases hT : (T i).Nonempty
    · refine hmono i (T i) hT _ _ (hgrid0 i a (lt_of_le_of_lt hab hb)) (hgrid0 i b hb) ?_
      intro j
      by_cases hj : j = i
      · subst hj; simpa using hab
      · simp [Function.update_of_ne hj]
    · have hE : T i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      rw [hE, hemp i _ (hgrid0 i a (lt_of_le_of_lt hab hb)), hemp i _ (hgrid0 i b hb)]
  have gcon : ∀ (i : Fin n) (c δ : ℕ), c + δ < 2 ^ q →
      v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i (c + δ)) -
        v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i c) ≤
      v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i δ) -
        v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i 0) := by
    intro i c δ hcδ
    have h := hss i (T i) i δ (Function.update (0 : InterdepSOS.KHL.Signal n) i c) 0
      (hgrid0 i c (by omega)) (fun j => by simp) (fun j => by simp) (by simpa using hcδ)
    simpa using h
  have hbd : ∀ (i : Fin n), 1 ≤ s i →
      v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i (s i)) ≤
        2 * ∑ ℓ ∈ Finset.Icc 1 q, if (2 ^ (ℓ - 1) ≤ s i ∧ s i < 2 ^ ℓ) then
          v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i (2 ^ (ℓ - 1))) else 0 := by
    intro i hi
    have hsi := hs i
    set ℓ0 := Nat.log 2 (s i) + 1 with hℓ0
    have hlog : Nat.log 2 (s i) < q := by
      rw [Nat.log_lt_iff_lt_pow (by norm_num) (by omega)]; exact hsi
    have hlo : 2 ^ (ℓ0 - 1) ≤ s i := by
      simpa [hℓ0] using Nat.pow_log_le_self 2 (by omega : s i ≠ 0)
    have hhi : s i < 2 ^ ℓ0 := Nat.lt_pow_succ_log_self (by norm_num) _
    have hb := agent_bound (fun t => v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i t))
      (2 ^ q) (by simpa using gnn i 0 (by positivity)) (fun a b hab hb => gmono i a b hab hb)
      (fun c δ h => gcon i c δ h) (2 ^ (ℓ0 - 1)) (s i) hlo
      (by have : 2 ^ ℓ0 = 2 * 2 ^ (ℓ0 - 1) := by
            rw [hℓ0]; simp [pow_succ, mul_comm]
          omega) hsi
    refine le_trans hb ?_
    have hmem : ℓ0 ∈ Finset.Icc 1 q := by
      rw [Finset.mem_Icc]; omega
    have hle := Finset.single_le_sum (f := fun ℓ => if (2 ^ (ℓ - 1) ≤ s i ∧ s i < 2 ^ ℓ) then
          v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i (2 ^ (ℓ - 1))) else 0)
      (s := Finset.Icc 1 q) (fun ℓ hℓ => by
        have hℓq : ℓ - 1 < q := by rw [Finset.mem_Icc] at hℓ; omega
        split_ifs
        · exact gnn i _ (lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hℓq) le_rfl)
        · exact le_rfl) hmem
    simp only [hlo, hhi, and_self, if_true] at hle
    linarith
  unfold InterdepSOS.KHL.self
  have hL : ∑ ℓ ∈ Finset.Icc 1 (2 ^ q - 1), ∑ i ∈ Finset.univ.filter (fun i => s i = ℓ),
      v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i (s i)) =
      ∑ i, if 1 ≤ s i then v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i (s i)) else 0 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsi := hs i
    by_cases h1 : 1 ≤ s i
    · rw [if_pos h1, Finset.sum_eq_single (s i)]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro hn; exfalso; apply hn; rw [Finset.mem_Icc]; omega
    · rw [if_neg h1]
      apply Finset.sum_eq_zero
      intro b hb
      rw [Finset.mem_Icc] at hb
      rw [if_neg]; omega
  have hR : ∑ ℓ ∈ Finset.Icc 1 q, ∑ i ∈ Finset.univ.filter (fun i => 2 ^ (ℓ - 1) ≤ s i ∧ s i < 2 ^ ℓ),
      v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i (2 ^ (ℓ - 1))) =
      ∑ i, ∑ ℓ ∈ Finset.Icc 1 q, if (2 ^ (ℓ - 1) ≤ s i ∧ s i < 2 ^ ℓ) then
          v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i (2 ^ (ℓ - 1))) else 0 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h1 : 1 ≤ s i
  · rw [if_pos h1]; exact hbd i h1
  · rw [if_neg h1]
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro ℓ hℓ
    have hℓq : ℓ - 1 < q := by rw [Finset.mem_Icc] at hℓ; omega
    split_ifs
    · exact gnn i _ (Nat.pow_lt_pow_right (by norm_num) hℓq)
    · exact le_rfl

namespace KK
open InterdepSOS.KHL

lemma mono_all {n m : ℕ} {q : ℕ} {v : Valuation n m} (hv : IsCombValuation (2 ^ q) v)
    (i : Fin n) (T : Finset (Fin m)) (s s' : Signal n) (hs : InGrid (2 ^ q) s)
    (hs' : InGrid (2 ^ q) s') (h : s ≤ s') : v i T s ≤ v i T s' := by
  by_cases hT : T.Nonempty
  · exact hv.2.2.1 i T hT s s' hs hs' h
  · have hE : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    rw [hE, hv.2.1 i s hs, hv.2.1 i s' hs']

lemma grid_update {n : ℕ} {k : ℕ} (s : Signal n) (hs : InGrid k s) (i : Fin n) (y : ℕ) (hy : y < k) :
    InGrid k (Function.update s i y) := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hy
  · simpa [Function.update_of_ne hj] using hs j

lemma grid_rt {n : ℕ} {k : ℕ} (s : Signal n) (hs : InGrid k s) (c : ℕ) : InGrid k (rtProfile s c) := by
  intro j
  unfold rtProfile
  split_ifs with h
  · exact lt_of_le_of_lt h (hs j)
  · exact hs j

lemma rb_icir {n m : ℕ} (q : ℕ) (v : Valuation n m) (hv : IsCombValuation (2 ^ q) v)
    (rbSel : ℕ → Signal n → Allocation n m) (hrb : InterdepSOS.KSS.IsRBSelector q v rbSel)
    (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 q) :
    IsExPostIC (2 ^ q) v (InterdepSOS.KSS.rbAlloc rbSel ℓ) (InterdepSOS.KSS.rbPay v rbSel ℓ) ∧
      IsExPostIR (2 ^ q) v (InterdepSOS.KSS.rbAlloc rbSel ℓ) (InterdepSOS.KSS.rbPay v rbSel ℓ) := by
  have hℓ' := Finset.mem_Icc.mp hℓ
  set c : ℕ := 2 ^ (ℓ - 1) with hc
  have hc1 : 1 ≤ c := Nat.one_le_two_pow
  have hcq : c < 2 ^ q := Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- low report: utility zero
  have hlow : ∀ (i : Fin n) (s : Signal n) (y : ℕ), InGrid (2 ^ q) s → y < c →
      utility v (InterdepSOS.KSS.rbAlloc rbSel ℓ) (InterdepSOS.KSS.rbPay v rbSel ℓ) i s y = 0 := by
    intro i s y hs hy
    have hg : InGrid (2 ^ q) (Function.update s i y) := grid_update s hs i y (lt_trans hy hcq)
    have hE : InterdepSOS.KSS.rbAlloc rbSel ℓ (Function.update s i y) i = ∅ := by
      have := (hrb ℓ hℓ _ hg).1.2 i (by
        simp only [high, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
        simpa using hy)
      exact this
    unfold utility InterdepSOS.KSS.rbPay
    rw [hE, hv.2.1 i s hs, hv.2.1 i _ (grid_update _ hg i _ (by omega))]
    simp
  -- high report: utility independent of the report
  set A : Fin n → Signal n → Finset (Fin m) := fun i s =>
    InterdepSOS.KSS.rbAlloc rbSel ℓ (Function.update s i c) i with hA
  have hhigh : ∀ (i : Fin n) (s : Signal n) (y : ℕ), c ≤ y →
      utility v (InterdepSOS.KSS.rbAlloc rbSel ℓ) (InterdepSOS.KSS.rbPay v rbSel ℓ) i s y =
        v i (A i s) s - v i (A i s) (Function.update s i (c - 1)) := by
    intro i s y hy
    have hal : InterdepSOS.KSS.rbAlloc rbSel ℓ (Function.update s i y) =
        InterdepSOS.KSS.rbAlloc rbSel ℓ (Function.update s i c) := by
      unfold InterdepSOS.KSS.rbAlloc
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [rtProfile, Function.update_self]
        rw [if_pos hy, if_pos le_rfl]
      · simp [rtProfile, Function.update_of_ne hj]
    unfold utility InterdepSOS.KSS.rbPay
    rw [hal]
    simp only [Function.update_idem, hA]
    rfl
  have hsign : ∀ (i : Fin n) (s : Signal n), InGrid (2 ^ q) s →
      (c ≤ s i → 0 ≤ v i (A i s) s - v i (A i s) (Function.update s i (c - 1))) ∧
      (s i < c → v i (A i s) s - v i (A i s) (Function.update s i (c - 1)) ≤ 0) := by
    intro i s hs
    have hg : InGrid (2 ^ q) (Function.update s i (c - 1)) := grid_update s hs i _ (by omega)
    constructor
    · intro h
      have : Function.update s i (c - 1) ≤ s := by
        intro j
        by_cases hj : j = i
        · subst hj; simp; omega
        · simp [Function.update_of_ne hj]
      linarith [mono_all hv i (A i s) _ _ hg hs this]
    · intro h
      have : s ≤ Function.update s i (c - 1) := by
        intro j
        by_cases hj : j = i
        · subst hj; simp; omega
        · simp [Function.update_of_ne hj]
      linarith [mono_all hv i (A i s) _ _ hs hg this]
  constructor
  · intro i s y hs hy
    obtain ⟨h1, h2⟩ := hsign i s hs
    by_cases hsi : c ≤ s i
    · have htr := hhigh i s (s i) hsi
      by_cases hyc : c ≤ y
      · rw [hhigh i s y hyc, htr]
      · rw [hlow i s y hs (by omega), htr]; exact h1 hsi
    · push_neg at hsi
      have htr := hlow i s (s i) hs hsi
      by_cases hyc : c ≤ y
      · rw [hhigh i s y hyc, htr]; exact h2 hsi
      · rw [hlow i s y hs (by omega), htr]
  · intro i s hs
    obtain ⟨h1, h2⟩ := hsign i s hs
    by_cases hsi : c ≤ s i
    · rw [hhigh i s (s i) hsi]; exact h1 hsi
    · push_neg at hsi
      rw [hlow i s (s i) hs hsi]

lemma bucket_le {n m : ℕ} (q : ℕ) (v : Valuation n m) (hv : IsCombValuation (2 ^ q) v)
    (rbSel : ℕ → Signal n → Allocation n m) (hrb : InterdepSOS.KSS.IsRBSelector q v rbSel)
    (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 q) (s : Signal n) (hs : InGrid (2 ^ q) s)
    (T : Allocation n m) (hT : IsAllocOn Finset.univ T) :
    ∑ i ∈ Finset.univ.filter (fun i => 2 ^ (ℓ - 1) ≤ s i ∧ s i < 2 ^ ℓ),
        v i (T i) (Function.update (0 : Signal n) i (2 ^ (ℓ - 1))) ≤
      welfare v (InterdepSOS.KSS.rbAlloc rbSel ℓ s) s := by
  have hℓ' := Finset.mem_Icc.mp hℓ
  set c : ℕ := 2 ^ (ℓ - 1) with hc
  have hcq : c < 2 ^ q := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hP : InGrid (2 ^ q) (rtProfile s c) := grid_rt s hs c
  have hPs : rtProfile s c ≤ s := by
    intro j; unfold rtProfile; split_ifs with h
    · exact h
    · exact le_rfl
  obtain ⟨hAlloc, hopt⟩ := hrb ℓ hℓ s hs
  set H := high s c with hH
  set B := Finset.univ.filter (fun i => c ≤ s i ∧ s i < 2 ^ ℓ) with hB
  have hBH : B ⊆ H := by
    intro i hi
    simp only [hB, hH, high, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.1
  set T' : Allocation n m := fun i => if i ∈ H then T i else ∅ with hT'
  have hT'alloc : IsAllocOn H T' := by
    refine ⟨?_, fun i hi => by simp [hT', hi]⟩
    intro i j hij
    have := hT.1 hij
    simp only [hT']
    split_ifs
    · exact this
    · simp
    · simp
    · simp
  have hopt' := hopt T' hT'alloc
  have step1 : ∑ i ∈ B, v i (T i) (Function.update (0 : Signal n) i c) ≤
      ∑ i ∈ B, v i (T' i) (rtProfile s c) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hiH : i ∈ H := hBH hi
    have hci : c ≤ s i := by simp only [hB, Finset.mem_filter] at hi; exact hi.2.1
    have : T' i = T i := by simp [hT', hiH]
    rw [this]
    refine mono_all hv i (T i) _ _ (grid_update 0 (fun j => by simp) i c hcq) hP ?_
    intro j
    by_cases hj : j = i
    · subst hj; simp [rtProfile, hci]
    · simp [Function.update_of_ne hj]
  have step2 : ∑ i ∈ B, v i (T' i) (rtProfile s c) ≤ ∑ i ∈ H, v i (T' i) (rtProfile s c) :=
    Finset.sum_le_sum_of_subset_of_nonneg hBH (fun i _ _ => hv.1 i _ _ hP)
  have step3 : ∑ i ∈ H, v i (rbSel ℓ (rtProfile s c) i) (rtProfile s c) ≤
      ∑ i ∈ H, v i (rbSel ℓ (rtProfile s c) i) s :=
    Finset.sum_le_sum fun i _ => mono_all hv i _ _ _ hP hs hPs
  have step4 : ∑ i ∈ H, v i (rbSel ℓ (rtProfile s c) i) s ≤ welfare v (InterdepSOS.KSS.rbAlloc rbSel ℓ s) s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hv.1 i _ _ hs)
  have e : (fun i => v i (InterdepSOS.KSS.rbAlloc rbSel ℓ s i) (rtProfile s c)) =
      fun i => v i (rbSel ℓ (rtProfile s c) i) (rtProfile s c) := rfl
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ ∑ i ∈ H, v i (rbSel ℓ (rtProfile s c) i) (rtProfile s c) := hopt'
    _ ≤ _ := step3
    _ ≤ _ := step4

end KK


lemma strong_to_sos {n : ℕ} (k : ℕ) (w : InterdepSOS.KHL.Signal n → ℝ) (h : IsStrongSOS k w) :
    InterdepSOS.KHL.IsSOS k w := by
  intro j x δ s s' hs hs' hxδ hle
  have hxk : x < k := by omega
  have hgrid : ∀ t : InterdepSOS.KHL.Signal n, InterdepSOS.KHL.InGrid k t →
      InterdepSOS.KHL.InGrid k (Function.update t j x) := by
    intro t ht i
    by_cases hi : i = j
    · subst hi; simpa using hxk
    · simpa [Function.update_of_ne hi] using ht i
  have hle' : Function.update s' j x ≤ Function.update s j x := by
    intro i
    by_cases hi : i = j
    · subst hi; simp
    · simpa [Function.update_of_ne hi] using hle i hi
  have := h j δ (Function.update s j x) (Function.update s' j x) (hgrid s hs) (hgrid s' hs') hle'
    (by simpa using hxδ)
  simpa using this

lemma self_le {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (hv : InterdepSOS.KHL.IsCombValuation (2 ^ q) v) (hss : ∀ i T, IsStrongSOS (2 ^ q) (v i T))
    (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (hrb : IsRBSelector q v rbSel)
    (s : InterdepSOS.KHL.Signal n) (hs : InterdepSOS.KHL.InGrid (2 ^ q) s)
    (T : InterdepSOS.KHL.Allocation n m) (hT : InterdepSOS.KHL.IsAllocOn Finset.univ T) :
    InterdepSOS.KHL.self (2 ^ q) v T s ≤ 2 * ∑ ℓ ∈ Finset.Icc 1 q, InterdepSOS.KHL.welfare v (rbAlloc rbSel ℓ s) s := by
  refine (display9_aux q v hv hss s hs T).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact Finset.sum_le_sum fun ℓ hℓ => KK.bucket_le q v hv rbSel hrb ℓ hℓ s hs T hT

lemma kss_mix {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m)
    (rsSel : Finset (Fin n) → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m)
    (s : InterdepSOS.KHL.Signal n) :
    (2 * (q : ℝ) + 4) * kssWelfare q v rbSel rsSel s =
      2 * ∑ ℓ ∈ Finset.Icc 1 q, InterdepSOS.KHL.welfare v (rbAlloc rbSel ℓ s) s +
        4 * InterdepSOS.KHL.rsAvg v rsSel s := by
  unfold kssWelfare pRB rbAvg
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have hq' : (q : ℝ) ≠ 0 := by positivity
    have h2 : (q : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

theorem solution {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (hv : InterdepSOS.KHL.IsCombValuation (2 ^ q) v) (hss : ∀ i T, IsStrongSOS (2 ^ q) (v i T))
    (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (hrb : IsRBSelector q v rbSel)
    (rsSel : Finset (Fin n) → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (hrs : InterdepSOS.KHL.IsRSSelector (2 ^ q) v rsSel) :
    (∀ ℓ ∈ Finset.Icc 1 q,
        InterdepSOS.KHL.IsExPostIC (2 ^ q) v (rbAlloc rbSel ℓ) (rbPay v rbSel ℓ) ∧
        InterdepSOS.KHL.IsExPostIR (2 ^ q) v (rbAlloc rbSel ℓ) (rbPay v rbSel ℓ)) ∧
    (∀ B : Finset (Fin n),
        InterdepSOS.KHL.IsExPostIC (2 ^ q) v (InterdepSOS.KHL.rsAlloc rsSel B) 0 ∧ InterdepSOS.KHL.IsExPostIR (2 ^ q) v (InterdepSOS.KHL.rsAlloc rsSel B) 0) ∧
    ∀ s : InterdepSOS.KHL.Signal n, InterdepSOS.KHL.InGrid (2 ^ q) s → ∀ Tstar : InterdepSOS.KHL.Allocation n m, InterdepSOS.KHL.IsAllocOn Finset.univ Tstar →
      InterdepSOS.KHL.welfare v Tstar s ≤ (2 * q + 4) * kssWelfare q v rbSel rsSel s := by
  refine ⟨fun ℓ hℓ => KK.rb_icir q v hv rbSel hrb ℓ hℓ, fun B => InterdepSOS.KHL.khl_rs_icir hv hrs B, ?_⟩
  intro s hs T hT
  have hsos : ∀ i T, InterdepSOS.KHL.IsSOS (2 ^ q) (v i T) := fun i T => strong_to_sos _ _ (hss i T)
  have h0 := InterdepSOS.KHL.khl_decomp (Nat.one_le_two_pow) hv hsos hs T
  have h1 := self_le q v hv hss rbSel hrb s hs T hT
  have h2 := InterdepSOS.KHL.khl_other_le (Nat.one_le_two_pow) hv hsos hrs hs T hT
  have h3 := kss_mix q v rbSel rsSel s
  linarith
