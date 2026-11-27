-- Prove2me | solution 1 for HLambdaG.Main.Supplement.theorem_2_corrected
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:24:30.558648+00:00
-- url     : https://prove2.me/submissions/7ed3bfd9-cdf4-4c69-a281-027a109313c2

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_Discrete

open scoped NNReal

open HLambdaG
open HLambdaG.Main
open HLambdaG.Main.Supplement

open Filter Topology

/-- Theorem 2, p. 640, with the lower summation index of (17) corrected to `n + 1`:
in the setting of §1.1, (17) is equivalent to (14) for `F(s, t) = Σ_{k ≤ [s]} F_k(t)` and
`T₁(s) = T_{[s]}`. -/
theorem solution (D : DiscreteSetting) :
    D.Cond17 ↔ Cond14 D.input D.T1 := by
      have hIcc : ∀ (t : ℝ≥0) (n : ℕ), ∑ k ∈ Finset.Icc 1 n, D.F k t
          = ∑ k ∈ Finset.range (n+1), D.F k t := by
        intro t n
        induction n with
        | zero => simp [D.F_zero]
        | succ m ih =>
          rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (m+1)]
      have htsum : ∀ (t : ℝ≥0) (n : ℕ), ∑' k, D.F k t
          = ∑ k ∈ Finset.Icc 1 n, D.F k t + ∑' j, D.F (n + 1 + j) t := by
        intro t n
        rw [hIcc, ← (D.F_summable t).sum_add_tsum_nat_add (n+1)]
        congr 1
        refine tsum_congr (fun j => ?_)
        rw [add_comm]
      have hFinf : ∀ t, FInfT D.input t = ∑' k, D.F k t := by
        intro t
        show (⨆ s : ℝ≥0, ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k t) = _
        apply le_antisymm
        · exact ciSup_le (fun s => (D.F_summable t).sum_le_tsum _ (fun k _ => D.F_nonneg k t))
        · refine Real.tsum_le_of_sum_range_le (fun k => D.F_nonneg k t) (fun n => ?_)
          have hb : BddAbove (Set.range (fun s : ℝ≥0 => ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k t)) :=
            D.input.bdd_s t
          calc ∑ k ∈ Finset.range n, D.F k t ≤ ∑ k ∈ Finset.range (n+1), D.F k t :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_succ n))
                  (fun k _ _ => D.F_nonneg k t)
            _ = ∑ k ∈ Finset.Icc 1 ⌊((n:ℝ≥0))⌋₊, D.F k t := by rw [Nat.floor_natCast, hIcc]
            _ ≤ _ := le_ciSup hb (n : ℝ≥0)
      have hleft : ∀ (s : ℝ≥0) (n : ℕ), (n : ℝ≥0) < s → s ≤ (n : ℝ≥0) + 1 →
          leftLim D.T1 s = D.T n := by
        intro s n h1 h2
        unfold leftLim
        apply IsGreatest.csSup_eq
        refine ⟨⟨(n : ℝ≥0), h1, ?_⟩, ?_⟩
        · show D.T ⌊(n:ℝ≥0)⌋₊ = D.T n
          rw [Nat.floor_natCast]
        · rintro _ ⟨u, hu, rfl⟩
          show D.T ⌊u⌋₊ ≤ D.T n
          apply D.T_mono
          have hu2 : u < ((n + 1 : ℕ) : ℝ≥0) := by push_cast; exact lt_of_lt_of_le hu h2
          have := (Nat.floor_lt (by positivity)).2 hu2
          omega
      set a : ℕ → ℝ := fun n => ∑' j, D.F (n + 1 + j) (D.T n) with ha
      have ha0 : ∀ n, 0 ≤ a n := fun n => tsum_nonneg (fun j => D.F_nonneg _ _)
      have hexpr : ∀ (s : ℝ≥0) (n : ℕ), (n : ℝ≥0) < s → s ≤ (n : ℝ≥0) + 1 →
          D.input.F s (leftLim D.T1 s) - FInfT D.input (leftLim D.T1 s) =
            ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k (D.T n) - ∑ k ∈ Finset.Icc 1 n, D.F k (D.T n) - a n := by
        intro s n h1 h2
        rw [hleft s n h1 h2, hFinf, htsum _ n]
        show ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k (D.T n) - _ = _
        ring
      have hlo : ∀ (s : ℝ≥0) (n : ℕ), (n : ℝ≥0) < s →
          ∑ k ∈ Finset.Icc 1 n, D.F k (D.T n) ≤ ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k (D.T n) := by
        intro s n h1
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc le_rfl (Nat.le_floor h1.le)) (fun k _ _ => D.F_nonneg k _)
      have hup : ∀ (s : ℝ≥0) (n : ℕ),
          ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k (D.T n) ≤ ∑ k ∈ Finset.Icc 1 n, D.F k (D.T n) + a n := by
        intro s n
        rw [← htsum]
        exact (D.F_summable _).sum_le_tsum _ (fun k _ => D.F_nonneg k _)
      constructor
      · intro h17
        unfold Cond14
        have hc : Tendsto (fun s : ℝ≥0 => ⌈s⌉₊ - 1) atTop atTop :=
          (tendsto_sub_atTop_nat 1).comp tendsto_nat_ceil_atTop
        refine squeeze_zero_norm' ?_ (h17.comp hc)
        filter_upwards [eventually_gt_atTop (1 : ℝ≥0)] with s hs
        have hc1 : 1 < ⌈s⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast hs)
        obtain ⟨n, hn⟩ : ∃ n, ⌈s⌉₊ = n + 1 := ⟨⌈s⌉₊ - 1, by omega⟩
        have hn' : ⌈s⌉₊ - 1 = n := by omega
        have hn1 : 1 ≤ n := by omega
        have hlt : (⌈s⌉₊ : ℝ≥0) < s + 1 := Nat.ceil_lt_add_one (by positivity)
        have hle : s ≤ (⌈s⌉₊ : ℝ≥0) := Nat.le_ceil s
        rw [hn] at hlt hle
        push_cast at hlt hle
        have h1 : (n : ℝ≥0) < s := lt_of_add_lt_add_right hlt
        simp only [Function.comp, hn']
        rw [hexpr s n h1 hle]
        have hl := hlo s n h1
        have hu := hup s n
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
        have hsn : (n : ℝ) ≤ (s : ℝ) := by exact_mod_cast h1.le
        have hspos : (0 : ℝ) < s := lt_of_lt_of_le hnpos hsn
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hspos)]
        calc (s : ℝ)⁻¹ * |∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k (D.T n) - ∑ k ∈ Finset.Icc 1 n, D.F k (D.T n) - a n|
            ≤ (s : ℝ)⁻¹ * a n := by
              apply mul_le_mul_of_nonneg_left _ (inv_pos.2 hspos).le
              rw [abs_le]
              constructor <;> linarith [ha0 n]
          _ ≤ (n : ℝ)⁻¹ * a n := mul_le_mul_of_nonneg_right (inv_anti₀ hnpos hsn) (ha0 n)
      · intro h14
        unfold DiscreteSetting.Cond17
        have hsn : Tendsto (fun n : ℕ => (n : ℝ≥0) + 2⁻¹) atTop atTop :=
          tendsto_atTop_mono (fun n => le_add_of_nonneg_right (by positivity))
            (tendsto_natCast_atTop_atTop (R := ℝ≥0))
        have h := h14.comp hsn
        have h2 : Tendsto (fun n : ℕ => 2 * ‖((((n : ℝ≥0) + 2⁻¹ : ℝ≥0) : ℝ))⁻¹ *
            (D.input.F ((n : ℝ≥0) + 2⁻¹) (leftLim D.T1 ((n : ℝ≥0) + 2⁻¹)) -
              FInfT D.input (leftLim D.T1 ((n : ℝ≥0) + 2⁻¹)))‖) atTop (𝓝 0) := by
          simpa using (h.norm.const_mul 2)
        refine squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (ha0 n))) ?_ h2
        filter_upwards [eventually_ge_atTop 1] with n hn1
        have h1 : (n : ℝ≥0) < (n : ℝ≥0) + 2⁻¹ := by
          apply lt_add_of_pos_right; positivity
        have h2' : (n : ℝ≥0) + 2⁻¹ ≤ (n : ℝ≥0) + 1 := by
          gcongr
          exact inv_le_one_of_one_le₀ one_le_two
        have hfl : ⌊(n : ℝ≥0) + 2⁻¹⌋₊ = n := by
          rw [Nat.floor_eq_iff (by positivity)]
          exact ⟨h1.le, by
            gcongr
            exact inv_lt_one_of_one_lt₀ one_lt_two⟩
        rw [hexpr _ n h1 h2', hfl, sub_self, zero_sub]
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
        have hc : (((n : ℝ≥0) + 2⁻¹ : ℝ≥0) : ℝ) = (n : ℝ) + 2⁻¹ := by push_cast; rfl
        rw [hc, Real.norm_eq_abs, mul_neg, abs_neg, abs_mul, abs_of_pos (by positivity),
          abs_of_nonneg (ha0 n)]
        have hinv : (n : ℝ)⁻¹ ≤ 2 * ((n : ℝ) + 2⁻¹)⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, mul_one,
            div_le_div_iff₀ (by positivity) (by positivity)]
          have : (1:ℝ) ≤ n := by exact_mod_cast hn1
          nlinarith
        calc (n : ℝ)⁻¹ * a n ≤ 2 * ((n : ℝ) + 2⁻¹)⁻¹ * a n :=
              mul_le_mul_of_nonneg_right hinv (ha0 n)
          _ = _ := by ring
