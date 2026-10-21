-- Prove2me | solution 1 for InterdepSOS.KSS.display_9_corrected
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:01:01.002244+00:00
-- url     : https://prove2.me/submissions/c668496e-9dec-4741-a9ff-cc4ab756c7ac

import Mathlib
import Definitions.Def_InterdepSOS_KSS_Setting
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

theorem solution {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
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
