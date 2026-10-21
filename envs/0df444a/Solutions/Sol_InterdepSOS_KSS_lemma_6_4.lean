-- Prove2me | solution 1 for InterdepSOS.KSS.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:04:34.599689+00:00
-- url     : https://prove2.me/submissions/83fd9fab-b345-4d27-aeb3-b1aaed1b6d74

import Mathlib
import Definitions.Def_InterdepSOS_KSS_Setting
import Definitions.Def_InterdepSOS_KSS_Mechanisms
set_option autoImplicit false
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

theorem solution {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (hv : InterdepSOS.KHL.IsCombValuation (2 ^ q) v) (hss : ∀ i T, IsStrongSOS (2 ^ q) (v i T))
    (rbSel : ℕ → InterdepSOS.KHL.Signal n → InterdepSOS.KHL.Allocation n m) (hrb : IsRBSelector q v rbSel) :
    (∀ ℓ ∈ Finset.Icc 1 q,
        InterdepSOS.KHL.IsExPostIC (2 ^ q) v (rbAlloc rbSel ℓ) (rbPay v rbSel ℓ) ∧
        InterdepSOS.KHL.IsExPostIR (2 ^ q) v (rbAlloc rbSel ℓ) (rbPay v rbSel ℓ)) ∧
    ∀ s : InterdepSOS.KHL.Signal n, InterdepSOS.KHL.InGrid (2 ^ q) s → ∀ T : InterdepSOS.KHL.Allocation n m, InterdepSOS.KHL.IsAllocOn Finset.univ T →
      InterdepSOS.KHL.self (2 ^ q) v T s ≤ 2 * ∑ ℓ ∈ Finset.Icc 1 q, InterdepSOS.KHL.welfare v (rbAlloc rbSel ℓ s) s := by
  refine ⟨fun ℓ hℓ => KK.rb_icir q v hv rbSel hrb ℓ hℓ, ?_⟩
  intro s hs T hT
  refine (display9_aux q v hv hss s hs T).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact Finset.sum_le_sum fun ℓ hℓ => KK.bucket_le q v hv rbSel hrb ℓ hℓ s hs T hT
