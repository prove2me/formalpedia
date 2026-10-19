-- Prove2me | solution 1 for LandauFunction.landau_log_asymptotic_expansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T05:21:06.435732+00:00
-- url     : https://prove2.me/submissions/d6acb357-9d42-4c83-a907-99b37e7e3852

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_psi_prime_number_theorem
import Definitions.Def_LandauFunction_landau

-- ===== LG/A =====
section
open Finset Real Filter Topology

namespace LGA

/-- Primes `≤ N`. -/
def P (N : ℕ) : Finset ℕ := (range (N + 1)).filter Nat.Prime

noncomputable def th (N : ℕ) : ℝ := ∑ p ∈ P N, Real.log p

lemma th_eq (N : ℕ) : th N = Chebyshev.theta N := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, th, P]
  congr 1
  ext p; simp

lemma log_div_sqrt_tendsto : Tendsto (fun N : ℕ => Real.log N / Real.sqrt N) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have h2 := h.comp tendsto_natCast_atTop_atTop
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with N _
  simp [Function.comp, Real.sqrt_eq_rpow]

theorem th_tendsto : Tendsto (fun N : ℕ => th N / N) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := ArtinPrimitiveRoots.psi_prime_number_theorem 1 one_pos
  have hpsi : ∀ N : ℕ, Chebyshev.psi N = ∑ n ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt n := by
    intro N; simp [Chebyshev.psi]
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- (ψ N - N) / N → 0
  have h1 : Tendsto (fun N : ℕ => (Chebyshev.psi N - N) / N) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => |C| / Real.log N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have := hC N (by omega)
    rw [← hpsi, Real.rpow_neg_one] at this
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hN0, div_le_div_iff₀ hN0 hl]
    calc |Chebyshev.psi N - N| * Real.log N ≤ (C * (N * (Real.log N)⁻¹)) * Real.log N := by gcongr
      _ = C * N := by field_simp
      _ ≤ |C| * N := by gcongr; exact le_abs_self C
  -- (ψ N - θ N) / N → 0
  have h2 : Tendsto (fun N : ℕ => (Chebyshev.psi N - Chebyshev.theta N) / N) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => 2 * (Real.log N / Real.sqrt N)) atTop (𝓝 0) := by
      simpa using log_div_sqrt_tendsto.const_mul 2
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
    have := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := (N : ℝ)) (by exact_mod_cast hN)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hN0]
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
    rw [div_le_iff₀ hN0]
    calc _ ≤ 2 * Real.sqrt N * Real.log N := this
      _ = 2 * (Real.log N / Real.sqrt N) * N := by field_simp; rw [sq, hsq]; ring
  have h3 := (h1.sub h2)
  rw [sub_zero] at h3
  have h4 := h3.const_add 1
  rw [add_zero] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [th_eq]
  field_simp
  ring


noncomputable def S1 (N : ℕ) : ℝ := ∑ p ∈ P N, (p : ℝ) * Real.log p
noncomputable def S0 (N : ℕ) : ℝ := ∑ p ∈ P N, (p : ℝ)
noncomputable def pc (N : ℕ) : ℝ := ((P N).card : ℝ)

lemma P_succ (N : ℕ) : P (N + 1) = if (N + 1).Prime then insert (N + 1) (P N) else P N := by
  unfold P
  rw [Finset.range_add_one, filter_insert]

lemma not_mem_P (N : ℕ) : N + 1 ∉ P N := by simp [P]

lemma th_succ (N : ℕ) : th (N + 1) = th N + if (N + 1).Prime then Real.log (N + 1 : ℕ) else 0 := by
  unfold th; rw [P_succ]; split_ifs <;> simp [sum_insert (not_mem_P N), add_comm]

lemma S1_succ (N : ℕ) :
    S1 (N + 1) = S1 N + if (N + 1).Prime then ((N + 1 : ℕ) : ℝ) * Real.log (N + 1 : ℕ) else 0 := by
  unfold S1; rw [P_succ]; split_ifs <;> simp [sum_insert (not_mem_P N), add_comm]

lemma S1_id (N : ℕ) : S1 N = N * th N - ∑ m ∈ range N, th m := by
  induction N with
  | zero => simp [S1, P, Finset.filter_singleton, Nat.not_prime_zero]
  | succ N ih =>
    rw [S1_succ, th_succ, sum_range_succ, ih]
    split_ifs <;> push_cast <;> ring

lemma sum_range_cast (N : ℕ) : ∑ m ∈ range N, (m : ℝ) = N * (N - 1) / 2 := by
  have := Finset.sum_range_id_mul_two N
  have h : ((∑ m ∈ range N, m : ℕ) : ℝ) * 2 = (N * (N - 1) : ℕ) := by exact_mod_cast this
  push_cast at h
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp
  · rw [Nat.cast_sub (by omega)] at h; push_cast at h; linarith

lemma sum_th_tendsto : Tendsto (fun N : ℕ => (∑ m ∈ range N, th m) / (N : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  -- e m = th m - m is o(m)
  have he : (fun m : ℕ => th m - m) =o[atTop] (fun m : ℕ => (m : ℝ)) := by
    rw [Asymptotics.isLittleO_iff_tendsto']
    · have := th_tendsto.sub_const 1
      rw [sub_self] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with m hm
      have : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      field_simp
    · filter_upwards [eventually_ge_atTop 1] with m hm h
      exact absurd h (by exact_mod_cast (by omega : m ≠ 0))
  have hsum := he.sum_range (fun m => by positivity) (by
    simp_rw [sum_range_cast]
    have : Tendsto (fun N : ℕ => (N : ℝ) * (N - 1)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    exact this.atTop_div_const two_pos)
  have h1 := hsum.tendsto_div_nhds_zero
  simp_rw [sum_range_cast] at h1
  have h2 : Tendsto (fun N : ℕ => ((N : ℝ) * (N - 1) / 2) / (N : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
    have : Tendsto (fun N : ℕ => (1 - 1 / (N : ℝ)) / 2) atTop (𝓝 ((1 - 0) / 2)) :=
      ((tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat).div_const 2)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  have h3 := (h1.mul h2).add h2
  rw [zero_mul, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN2
  have h2N : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN : (N : ℝ) * (N - 1) / 2 ≠ 0 := by
    have : (0 : ℝ) < N * (N - 1) / 2 := by nlinarith
    exact this.ne'
  rw [sum_sub_distrib, sum_range_cast]
  have : (N : ℝ) ≠ 0 := by positivity
  have h1' : (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem S1_tendsto : Tendsto (fun N : ℕ => S1 N / (N : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  have h := th_tendsto.sub sum_th_tendsto
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [S1_id]
  field_simp


lemma pc_upper (N : ℕ) {y : ℝ} (hy : 1 < y) : pc N ≤ (y + 1) + th N / Real.log y := by
  have hly : 0 < Real.log y := Real.log_pos hy
  unfold pc th
  rw [← card_filter_add_card_filter_not (s := P N) (fun p : ℕ => (p : ℝ) ≤ y)]
  push_cast
  have h1 : (((P N).filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℝ) ≤ y + 1 := by
    have hsub : (P N).filter (fun p : ℕ => (p : ℝ) ≤ y) ⊆ range (⌊y⌋₊ + 1) := by
      intro p hp
      simp only [mem_filter] at hp
      rw [mem_range, Nat.lt_succ_iff]
      exact Nat.le_floor hp.2
    have := card_le_card hsub
    rw [card_range] at this
    have h2 : (((P N).filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℝ) ≤ ⌊y⌋₊ + 1 := by exact_mod_cast this
    linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ y)]
  have h2 : (((P N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℝ) * Real.log y ≤
      ∑ p ∈ P N, Real.log p := by
    rw [← nsmul_eq_mul, ← sum_const]
    calc ∑ _p ∈ (P N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), Real.log y
        ≤ ∑ p ∈ (P N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), Real.log p := by
          refine sum_le_sum fun p hp => ?_
          simp only [mem_filter, not_le] at hp
          exact Real.log_le_log (by linarith) hp.2.le
      _ ≤ ∑ p ∈ P N, Real.log p := by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ => ?_
          exact Real.log_natCast_nonneg p
  have h3 : (((P N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℝ) ≤ (∑ p ∈ P N, Real.log p) / Real.log y := by
    rw [le_div_iff₀ hly]; exact h2
  linarith

lemma S0_upper (N : ℕ) {y : ℝ} (hy : 1 < y) : S0 N ≤ y * (y + 1) + S1 N / Real.log y := by
  have hly : 0 < Real.log y := Real.log_pos hy
  unfold S0 S1
  rw [← sum_filter_add_sum_filter_not (P N) (fun p : ℕ => (p : ℝ) ≤ y)]
  have h1 : ∑ p ∈ (P N).filter (fun p : ℕ => (p : ℝ) ≤ y), (p : ℝ) ≤ y * (y + 1) := by
    calc ∑ p ∈ (P N).filter (fun p : ℕ => (p : ℝ) ≤ y), (p : ℝ)
        ≤ ∑ _p ∈ (P N).filter (fun p : ℕ => (p : ℝ) ≤ y), y := by
          refine sum_le_sum fun p hp => ?_
          simp only [mem_filter] at hp; exact hp.2
      _ = (((P N).filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℝ) * y := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (y + 1) * y := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          · have hsub : (P N).filter (fun p : ℕ => (p : ℝ) ≤ y) ⊆ range (⌊y⌋₊ + 1) := by
              intro p hp
              simp only [mem_filter] at hp
              rw [mem_range, Nat.lt_succ_iff]
              exact Nat.le_floor hp.2
            have := card_le_card hsub
            rw [card_range] at this
            have h2 : (((P N).filter (fun p : ℕ => (p : ℝ) ≤ y)).card : ℝ) ≤ ⌊y⌋₊ + 1 := by
              exact_mod_cast this
            linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ y)]
      _ = y * (y + 1) := by ring
  have h2 : ∑ p ∈ (P N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), (p : ℝ) ≤
      (∑ p ∈ P N, (p : ℝ) * Real.log p) / Real.log y := by
    rw [le_div_iff₀ hly, sum_mul]
    calc ∑ p ∈ (P N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), (p : ℝ) * Real.log y
        ≤ ∑ p ∈ (P N).filter (fun p : ℕ => ¬ (p : ℝ) ≤ y), (p : ℝ) * Real.log p := by
          refine sum_le_sum fun p hp => ?_
          simp only [mem_filter, not_le] at hp
          exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hp.2.le) (by positivity)
      _ ≤ ∑ p ∈ P N, (p : ℝ) * Real.log p := by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ => ?_
          exact mul_nonneg (by positivity) (Real.log_natCast_nonneg p)
  linarith

lemma th_le_pc (N : ℕ) : th N ≤ pc N * Real.log N := by
  unfold th pc
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun p hp => ?_
  simp only [P, mem_filter, mem_range] at hp
  exact Real.log_le_log (by exact_mod_cast hp.2.pos) (by exact_mod_cast (by omega : p ≤ N))

lemma S1_le_S0 (N : ℕ) : S1 N ≤ S0 N * Real.log N := by
  unfold S1 S0
  rw [sum_mul]
  refine sum_le_sum fun p hp => ?_
  simp only [P, mem_filter, mem_range] at hp
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by exact_mod_cast hp.2.pos) (by exact_mod_cast (by omega : p ≤ N))) (by positivity)

lemma log_tendsto : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma lg2_tendsto : Tendsto (fun N : ℕ => Real.log N ^ 2 / N) atTop (𝓝 0) := by
  have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp tendsto_natCast_atTop_atTop
  refine this.congr' ?_
  filter_upwards with N
  simp

lemma loglog_tendsto : Tendsto (fun N : ℕ => Real.log (Real.log N) / Real.log N) atTop (𝓝 0) := by
  have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp log_tendsto
  refine this.congr' ?_
  filter_upwards with N
  simp

/-- `y N = N / log² N`. -/
noncomputable def yy (N : ℕ) : ℝ := N / Real.log N ^ 2

lemma yy_gt_one : ∀ᶠ N : ℕ in atTop, 1 < yy N := by
  filter_upwards [lg2_tendsto.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_ge_atTop 3] with N h1 h3
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hN : (0 : ℝ) < N := by positivity
  unfold yy
  rw [lt_div_iff₀ (by positivity), one_mul]
  rwa [div_lt_one hN] at h1

lemma ratio_tendsto : Tendsto (fun N : ℕ => Real.log N / Real.log (yy N)) atTop (𝓝 1) := by
  have h := ((loglog_tendsto.const_mul 2).const_sub 1).inv₀ (by norm_num)
  rw [mul_zero, sub_zero, inv_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with N h3
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hN : (0 : ℝ) < N := by positivity
  unfold yy
  rw [Real.log_div hN.ne' (by positivity), Real.log_pow]
  field_simp
  push_cast; ring

theorem pc_tendsto : Tendsto (fun N : ℕ => pc N * Real.log N / N) atTop (𝓝 1) := by
  have hup : Tendsto (fun N : ℕ => (1 / Real.log N + Real.log N / N) + th N / N *
      (Real.log N / Real.log (yy N))) atTop (𝓝 ((0 + 0) + 1 * 1)) := by
    refine Tendsto.add (Tendsto.add (tendsto_const_nhds.div_atTop log_tendsto) ?_)
      (th_tendsto.mul ratio_tendsto)
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
    refine this.congr' ?_
    filter_upwards with N; simp
  norm_num at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' th_tendsto hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    exact div_le_div_of_nonneg_right (th_le_pc N) hN0.le
  · filter_upwards [yy_gt_one, eventually_ge_atTop 3] with N hy h3
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hN0 : (0 : ℝ) < N := by positivity
    have hly : 0 < Real.log (yy N) := Real.log_pos hy
    have := pc_upper N hy
    have e : (yy N + 1) * Real.log N / N = 1 / Real.log N + Real.log N / N := by
      unfold yy; field_simp
    calc pc N * Real.log N / N ≤ (yy N + 1 + th N / Real.log (yy N)) * Real.log N / N := by
          gcongr
      _ = (yy N + 1) * Real.log N / N + th N / N * (Real.log N / Real.log (yy N)) := by ring
      _ = _ := by rw [e]; ring

theorem S0_tendsto : Tendsto (fun N : ℕ => S0 N * Real.log N / (N : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  have hup : Tendsto (fun N : ℕ => (1 / Real.log N ^ 3 + 1 / (N * Real.log N)) + S1 N / (N : ℝ) ^ 2 *
      (Real.log N / Real.log (yy N))) atTop (𝓝 ((0 + 0) + 1 / 2 * 1)) := by
    refine Tendsto.add (Tendsto.add ?_ ?_) (S1_tendsto.mul ratio_tendsto)
    · exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (3:ℕ) ≠ 0)).comp log_tendsto)
    · exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ log_tendsto)
  norm_num at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' S1_tendsto hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    exact div_le_div_of_nonneg_right (S1_le_S0 N) (by positivity)
  · filter_upwards [yy_gt_one, eventually_ge_atTop 3] with N hy h3
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hN0 : (0 : ℝ) < N := by positivity
    have hly : 0 < Real.log (yy N) := Real.log_pos hy
    have := S0_upper N hy
    have e : yy N * (yy N + 1) * Real.log N / (N : ℝ) ^ 2 = 1 / Real.log N ^ 3 + 1 / (N * Real.log N) := by
      unfold yy; field_simp
    calc S0 N * Real.log N / (N : ℝ) ^ 2 ≤ (yy N * (yy N + 1) + S1 N / Real.log (yy N)) * Real.log N / (N : ℝ) ^ 2 := by
          gcongr
      _ = yy N * (yy N + 1) * Real.log N / (N : ℝ) ^ 2 + S1 N / (N : ℝ) ^ 2 * (Real.log N / Real.log (yy N)) := by
          field_simp
      _ = _ := by rw [e]; ring

end LGA
end

-- ===== LG/B =====
section
open Finset Real Filter Topology
open LandauFunction

namespace LandauPartition

lemma lcm_eq_one_of_le_one (s : Multiset ℕ) (h : ∀ a ∈ s, a ≤ 1) (hpos : ∀ a ∈ s, 0 < a) :
    s.lcm = 1 := by
  apply Nat.eq_one_of_dvd_one
  rw [Multiset.lcm_dvd]
  intro b hb
  have : b = 1 := le_antisymm (h b hb) (hpos b hb)
  rw [this]

/-- The partition of `n` attached to a permutation of `Fin n`. -/
def permPartition (n : ℕ) (σ : Equiv.Perm (Fin n)) : Nat.Partition n where
  parts := σ.cycleType + Multiset.replicate (n - σ.support.card) 1
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.mp hi with h | h
    · exact lt_of_lt_of_le (by norm_num) (Equiv.Perm.two_le_of_mem_cycleType h)
    · rw [Multiset.eq_of_mem_replicate h]; norm_num
  parts_sum := by
    have h1 := Equiv.Perm.sum_cycleType σ
    have h2 : σ.support.card ≤ n := by
      have := Finset.card_le_univ σ.support
      simpa using this
    rw [Multiset.sum_add, h1, Multiset.sum_replicate, smul_eq_mul, mul_one]
    omega

lemma permPartition_lcm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permPartition n σ).parts.lcm = orderOf σ := by
  simp only [permPartition]
  rw [Multiset.lcm_add, lcm_eq_one_of_le_one (Multiset.replicate _ 1)
    (fun a ha => by rw [Multiset.eq_of_mem_replicate ha])
    (fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; norm_num),
    lcm_one_right, Equiv.Perm.lcm_cycleType]
  exact normalize_eq _

lemma exists_perm (n : ℕ) (p : Nat.Partition n) :
    ∃ σ : Equiv.Perm (Fin n), orderOf σ = p.parts.lcm := by
  set m := p.parts.filter (fun a => 2 ≤ a) with hm
  have hsum : m.sum ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin, ← p.parts_sum]
    calc m.sum ≤ m.sum + (p.parts.filter (fun a => ¬ 2 ≤ a)).sum := Nat.le_add_right _ _
      _ = p.parts.sum := by rw [← Multiset.sum_add, hm, Multiset.filter_add_not]
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (α := Fin n)).mpr
    ⟨hsum, fun a ha => (Multiset.mem_filter.mp ha).2⟩
  refine ⟨σ, ?_⟩
  rw [← Equiv.Perm.lcm_cycleType, hσ]
  conv_rhs => rw [← Multiset.filter_add_not (fun a => 2 ≤ a) p.parts]
  rw [Multiset.lcm_add, lcm_eq_one_of_le_one (p.parts.filter (fun a => ¬ 2 ≤ a))
    (fun a ha => by have := (Multiset.mem_filter.mp ha).2; omega)
    (fun a ha => p.parts_pos (Multiset.mem_filter.mp ha).1), lcm_one_right]
  exact (normalize_eq _).symm

end LandauPartition

open LandauPartition in
theorem landau_eq_sup (n : ℕ) :
    landau n = (Finset.univ : Finset (Nat.Partition n)).sup fun p => p.parts.lcm := by
  unfold landau
  apply le_antisymm
  · refine Finset.sup_le fun σ _ => ?_
    rw [← permPartition_lcm]
    exact Finset.le_sup (f := fun p : Nat.Partition n => p.parts.lcm) (Finset.mem_univ _)
  · refine Finset.sup_le fun p _ => ?_
    obtain ⟨σ, hσ⟩ := exists_perm n p
    rw [← hσ]
    exact Finset.le_sup (f := fun σ : Equiv.Perm (Fin n) => orderOf σ) (Finset.mem_univ _)

namespace LandauPartition

lemma le_landau (n : ℕ) (l : Multiset ℕ) (h1 : ∀ i ∈ l, 0 < i) (h2 : l.sum = n) :
    l.lcm ≤ landau n := by
  rw [landau_eq_sup]
  exact Finset.le_sup (f := fun p : Nat.Partition n => p.parts.lcm)
    (b := ⟨l, fun hi => h1 _ hi, h2⟩) (Finset.mem_univ _)

end LandauPartition


namespace LGB
open LGA

lemma sum_le_prod (S : Finset ℕ) (f : ℕ → ℕ) (h : ∀ p ∈ S, 2 ≤ f p) : ∑ p ∈ S, f p ≤ ∏ p ∈ S, f p := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    rw [sum_insert hx, prod_insert hx]
    have hS := ih (fun p hp => h p (mem_insert_of_mem hp))
    have hfx := h x (mem_insert_self x S)
    rcases S.eq_empty_or_nonempty with h0 | ⟨y, hy⟩
    · subst h0; simp
    · have hP : 2 ≤ ∏ p ∈ S, f p := by
        refine le_trans (h y (mem_insert_of_mem hy)) ?_
        exact Finset.single_le_prod' (fun p hp => by have := h p (mem_insert_of_mem hp); omega) hy
      nlinarith

lemma prod_sub_le (a : ℕ) (ha : a ≠ 0) (A : Finset ℕ) (hA : A ⊆ a.primeFactors) :
    ∏ p ∈ A, p ^ a.factorization p ≤ a := by
  calc ∏ p ∈ A, p ^ a.factorization p ≤ ∏ p ∈ a.primeFactors, p ^ a.factorization p := by
        refine prod_le_prod_of_subset_of_one_le' hA fun p hp _ => ?_
        exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos
    _ = a := by
        conv_rhs => rw [← Nat.prod_factorization_pow_eq_self ha]
        rfl

lemma sum_sub_le (a : ℕ) (ha : a ≠ 0) (A : Finset ℕ) (hA : A ⊆ a.primeFactors) :
    ∑ p ∈ A, p ^ a.factorization p ≤ a := by
  refine le_trans (sum_le_prod A _ fun p hp => ?_) (prod_sub_le a ha A hA)
  have hp := hA hp
  have h1 := Nat.prime_of_mem_primeFactors hp
  have h2 : 1 ≤ a.factorization p := by
    rw [← Nat.support_factorization] at hp
    exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hp)
  calc 2 ≤ p := h1.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ a.factorization p := Nat.pow_le_pow_right h1.pos h2

/-- Key lemma: the maximal prime powers dividing `lcm s` have sum at most `sum s`. -/
lemma Q (s : Multiset ℕ) (hs : ∀ a ∈ s, 0 < a) :
    ∑ p ∈ s.lcm.primeFactors, p ^ s.lcm.factorization p ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have ha : a ≠ 0 := (hs a (Multiset.mem_cons_self a t)).ne'
    have ht : ∀ b ∈ t, 0 < b := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    have hLt : t.lcm ≠ 0 := by
      intro h
      rw [Multiset.lcm_eq_zero_iff] at h
      exact (ht 0 h).ne' rfl
    have IH := ih ht
    rw [Multiset.lcm_cons, Multiset.sum_cons]
    change ∑ p ∈ (Nat.lcm a t.lcm).primeFactors, p ^ (Nat.lcm a t.lcm).factorization p ≤ a + t.sum
    rw [Nat.factorization_lcm ha hLt]
    set L := Nat.lcm a t.lcm
    rw [← sum_filter_add_sum_filter_not L.primeFactors (fun p => t.lcm.factorization p ≤ a.factorization p)]
    have hsupp : ∀ p, p ∈ L.primeFactors → 0 < (a.factorization ⊔ t.lcm.factorization) p := by
      intro p hp
      have : L.factorization p ≠ 0 := by
        rw [← Nat.support_factorization] at hp; exact Finsupp.mem_support_iff.1 hp
      rw [show L.factorization = a.factorization ⊔ t.lcm.factorization from
        Nat.factorization_lcm ha hLt] at this
      omega
    apply add_le_add
    · calc ∑ p ∈ L.primeFactors.filter (fun p => t.lcm.factorization p ≤ a.factorization p),
            p ^ (a.factorization ⊔ t.lcm.factorization) p
          = ∑ p ∈ L.primeFactors.filter (fun p => t.lcm.factorization p ≤ a.factorization p),
            p ^ a.factorization p := by
            refine sum_congr rfl fun p hp => ?_
            simp only [mem_filter] at hp
            rw [Finsupp.sup_apply, max_eq_left hp.2]
        _ ≤ a := by
            refine sum_sub_le a ha _ fun p hp => ?_
            simp only [mem_filter] at hp
            have h0 := hsupp p hp.1
            rw [Finsupp.sup_apply, max_eq_left hp.2] at h0
            rw [← Nat.support_factorization]
            exact Finsupp.mem_support_iff.2 h0.ne'
    · calc ∑ p ∈ L.primeFactors.filter (fun p => ¬ t.lcm.factorization p ≤ a.factorization p),
            p ^ (a.factorization ⊔ t.lcm.factorization) p
          = ∑ p ∈ L.primeFactors.filter (fun p => ¬ t.lcm.factorization p ≤ a.factorization p),
            p ^ t.lcm.factorization p := by
            refine sum_congr rfl fun p hp => ?_
            simp only [mem_filter, not_le] at hp
            rw [Finsupp.sup_apply, max_eq_right hp.2.le]
        _ ≤ ∑ p ∈ t.lcm.primeFactors, p ^ t.lcm.factorization p := by
            refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => Nat.zero_le _
            simp only [mem_filter, not_le] at hp
            rw [← Nat.support_factorization]
            exact Finsupp.mem_support_iff.2 (by omega)
        _ ≤ t.sum := IH


lemma log_lcm (L : ℕ) (hL : L ≠ 0) :
    Real.log L = ∑ p ∈ L.primeFactors, (L.factorization p : ℝ) * Real.log p := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hL]
  rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod, Real.log_prod]
  · refine sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity

lemma term_le (M : ℕ) (hM : 3 ≤ M) (p v : ℕ) (hp : p.Prime) (hv : 1 ≤ v) :
    (v : ℝ) * Real.log p - Real.log M / M * ((p : ℝ) ^ v) ≤
      if p ≤ M then Real.log M - Real.log M / M * p else 0 := by
  have hM0 : (0 : ℝ) < M := by positivity
  have hlM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlam : 0 < Real.log M / M := div_pos hlM hM0
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hpq : (p : ℝ) ≤ (p : ℝ) ^ v := by
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ v := pow_le_pow_right₀ hp1 hv
  have hlog : (v : ℝ) * Real.log p = Real.log ((p : ℝ) ^ v) := (Real.log_pow (p : ℝ) v).symm
  have hg0 : 0 ≤ (if p ≤ M then Real.log M - Real.log M / M * p else 0) := by
    split_ifs with h
    · have : (p : ℝ) ≤ M := by exact_mod_cast h
      have : Real.log M / M * p ≤ Real.log M / M * M := mul_le_mul_of_nonneg_left this hlam.le
      rw [div_mul_cancel₀ _ hM0.ne'] at this
      linarith
    · exact le_refl _
  by_cases hq : (p : ℝ) ^ v ≤ M
  · have hpM : p ≤ M := by
      have : (p : ℝ) ≤ M := hpq.trans hq
      exact_mod_cast this
    rw [if_pos hpM, hlog]
    have h1 : Real.log ((p : ℝ) ^ v) ≤ Real.log M := Real.log_le_log (by positivity) hq
    have h2 : Real.log M / M * p ≤ Real.log M / M * (p : ℝ) ^ v := mul_le_mul_of_nonneg_left hpq hlam.le
    linarith
  · push Not at hq
    have he : Real.exp 1 ≤ (M : ℝ) := by
      have := Real.exp_one_lt_d9
      have : (3 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hanti := Real.log_div_self_antitoneOn (show (M : ℝ) ∈ Set.Ici (Real.exp 1) from he)
      (show (p : ℝ) ^ v ∈ Set.Ici (Real.exp 1) from le_trans he hq.le) hq.le
    simp only at hanti
    have hq0 : (0 : ℝ) < (p : ℝ) ^ v := by positivity
    rw [div_le_div_iff₀ hq0 hM0] at hanti
    have : Real.log ((p : ℝ) ^ v) ≤ Real.log M / M * (p : ℝ) ^ v := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hM0]; linarith
    rw [hlog]
    linarith

/-- Upper bound (Landau's Lagrangian argument). -/
lemma upper (s : Multiset ℕ) (hs : ∀ a ∈ s, 0 < a) (M : ℕ) (hM : 3 ≤ M) :
    Real.log (s.lcm) ≤ pc M * Real.log M - Real.log M / M * S0 M + s.sum * Real.log M / M := by
  have hL : s.lcm ≠ 0 := by
    intro h; rw [Multiset.lcm_eq_zero_iff] at h; exact (hs 0 h).ne' rfl
  set L := s.lcm
  set lam := Real.log M / M with hlam_def
  have hM0 : (0 : ℝ) < M := by positivity
  have hlM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlam : 0 < lam := div_pos hlM hM0
  have hQ : (∑ p ∈ L.primeFactors, ((p : ℝ) ^ L.factorization p)) ≤ s.sum := by
    have := Q s hs
    exact_mod_cast this
  have hterm : ∀ p ∈ L.primeFactors, (L.factorization p : ℝ) * Real.log p - lam * ((p : ℝ) ^ L.factorization p) ≤
      if p ≤ M then Real.log M - lam * p else 0 := by
    intro p hp
    have hv : 1 ≤ L.factorization p := by
      rw [← Nat.support_factorization] at hp
      exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hp)
    exact term_le M hM p _ (Nat.prime_of_mem_primeFactors hp) hv
  have hsum := sum_le_sum hterm
  rw [sum_sub_distrib, ← mul_sum] at hsum
  have hg : ∑ p ∈ L.primeFactors, (if p ≤ M then Real.log M - lam * p else 0) ≤
      ∑ p ∈ P M, (Real.log M - lam * p) := by
    rw [← sum_filter]
    refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p hp _ => ?_)
    · simp only [mem_filter] at hp
      simp only [P, mem_filter, mem_range]
      exact ⟨by omega, Nat.prime_of_mem_primeFactors hp.1⟩
    · simp only [P, mem_filter, mem_range] at hp
      have : (p : ℝ) ≤ M := by exact_mod_cast (by omega : p ≤ M)
      have : lam * p ≤ lam * M := mul_le_mul_of_nonneg_left this hlam.le
      rw [hlam_def, div_mul_cancel₀ _ hM0.ne'] at this
      linarith
  have hPM : ∑ p ∈ P M, (Real.log M - lam * p) = pc M * Real.log M - lam * S0 M := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    rfl
  rw [log_lcm L hL]
  have : lam * (∑ p ∈ L.primeFactors, ((p : ℝ) ^ L.factorization p)) ≤ lam * s.sum :=
    mul_le_mul_of_nonneg_left hQ hlam.le
  have e : (s.sum : ℝ) * Real.log M / M = lam * s.sum := by rw [hlam_def]; ring
  rw [e]
  linarith

/-- Lower bound: the primes up to `N` form part of a partition of `n`. -/
lemma lower (n N : ℕ) (h : ∑ p ∈ P N, p ≤ n) : th N ≤ Real.log (landau n) := by
  set l : Multiset ℕ := (P N).val + Multiset.replicate (n - ∑ p ∈ P N, p) 1 with hl
  have hpos : ∀ i ∈ l, 0 < i := by
    intro i hi
    rcases Multiset.mem_add.1 hi with h1 | h1
    · have : i ∈ P N := h1
      simp only [P, mem_filter] at this
      exact this.2.pos
    · rw [Multiset.eq_of_mem_replicate h1]; norm_num
  have hsum : l.sum = n := by
    rw [hl, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
    have : (P N).val.sum = ∑ p ∈ P N, p := by rw [Finset.sum_eq_multiset_sum]; simp
    omega
  have hle := LandauPartition.le_landau n l hpos hsum
  have hdvd : ∏ p ∈ P N, p ∣ l.lcm := by
    refine Finset.prod_primes_dvd _ (fun p hp => ?_) (fun p hp => ?_)
    · simp only [P, mem_filter] at hp; exact hp.2.prime
    · exact Multiset.dvd_lcm (Multiset.mem_add.2 (Or.inl hp))
  have hl0 : l.lcm ≠ 0 := by
    intro h0; rw [Multiset.lcm_eq_zero_iff] at h0; exact (hpos 0 h0).ne' rfl
  have hprod_le : ∏ p ∈ P N, p ≤ landau n := (Nat.le_of_dvd (Nat.pos_of_ne_zero hl0) hdvd).trans hle
  have hprod_pos : 0 < ∏ p ∈ P N, p := prod_pos fun p hp => by
    simp only [P, mem_filter] at hp; exact hp.2.pos
  have hth : th N = Real.log ((∏ p ∈ P N, p : ℕ) : ℝ) := by
    rw [th, Nat.cast_prod, Real.log_prod]
    intro p hp; simp only [P, mem_filter] at hp; exact_mod_cast hp.2.pos.ne'
  rw [hth]
  exact Real.log_le_log (by exact_mod_cast hprod_pos) (by exact_mod_cast hprod_le)

end LGB
end

-- ===== LE/T =====
section
open Finset Real Filter Topology

namespace LET

/-- `log x ^ (k+1) ≤ C √x` for `x ≥ 1`. -/
lemma logpow_le_sqrt (k : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ^ (k + 1) ≤ (2 * (k + 1 : ℝ)) ^ (k + 1) * √x := by
  have hε : (0:ℝ) < 1 / (2 * (k + 1)) := by positivity
  have h := Real.log_le_rpow_div (by linarith : (0:ℝ) ≤ x) hε
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : Real.log x ≤ 2 * (k + 1) * x ^ (1 / (2 * (k + 1 : ℝ))) := by
    rw [div_div_eq_mul_div, div_one] at h; linarith
  calc Real.log x ^ (k + 1) ≤ (2 * (k + 1) * x ^ (1 / (2 * (k + 1 : ℝ)))) ^ (k + 1) :=
        pow_le_pow_left₀ hl h2 _
    _ = (2 * (k + 1 : ℝ)) ^ (k + 1) * (x ^ (1 / (2 * (k + 1 : ℝ)))) ^ (k + 1) := by rw [mul_pow]
    _ = (2 * (k + 1 : ℝ)) ^ (k + 1) * √x := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.sqrt_eq_rpow]
        congr 1; push_cast; field_simp

lemma log_floor_ge (x : ℝ) (hx : 2 ≤ x) : Real.log x / 2 ≤ Real.log (⌊x⌋₊ : ℝ) := by
  have hX : (2:ℝ) ≤ ⌊x⌋₊ := by
    have : (2:ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast this
  have hX2 : x / 2 ≤ ⌊x⌋₊ := by
    have := Nat.lt_floor_add_one x; linarith
  rcases le_or_gt 4 x with h4 | h4
  · have h1 : Real.log (x / 2) ≤ Real.log ⌊x⌋₊ := Real.log_le_log (by linarith) hX2
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) h4
    have e : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  · have h1 : Real.log 2 ≤ Real.log ⌊x⌋₊ := Real.log_le_log (by norm_num) hX
    have : Real.log x ≤ Real.log 4 := Real.log_le_log (by linarith) h4.le
    have e : Real.log (4:ℝ) = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    linarith

/-- Chebyshev θ with a power-of-log error term, for all `x ≥ 2`. -/
theorem theta_bound (A : ℕ) (hA : 1 ≤ A) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
    |Chebyshev.theta x - x| ≤ C * x / Real.log x ^ A := by
  obtain ⟨C0, hC0⟩ := ArtinPrimitiveRoots.psi_prime_number_theorem (A : ℝ) (by exact_mod_cast hA)
  set K := (2 * (A + 1 : ℝ)) ^ (A + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|C0| * 2 ^ A + 2 * K + K / Real.log 2, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx0 : 0 < Real.log x := by linarith
  have hLA : 0 < Real.log x ^ A := by positivity
  set X := ⌊x⌋₊ with hXdef
  have hX2 : 2 ≤ X := Nat.le_floor (by exact_mod_cast hx)
  have hXr : (2:ℝ) ≤ X := by exact_mod_cast hX2
  have hXx : (X:ℝ) ≤ x := Nat.floor_le hx0.le
  have hxX : x < X + 1 := Nat.lt_floor_add_one x
  have hlX := log_floor_ge x hx
  have hlX0 : 0 < Real.log (X:ℝ) := Real.log_pos (by linarith)
  -- psi part
  have hpsi : |Chebyshev.psi x - X| ≤ |C0| * 2 ^ A * x / Real.log x ^ A := by
    have h := hC0 X hX2
    have hr : Real.log (X:ℝ) ^ (-(A:ℝ)) = (Real.log (X:ℝ) ^ A)⁻¹ := by
      rw [Real.rpow_neg hlX0.le, Real.rpow_natCast]
    rw [hr] at h
    have e : Chebyshev.psi x = ∑ n ∈ Ioc 0 X, ArithmeticFunction.vonMangoldt n := rfl
    rw [e]
    refine h.trans ?_
    have h1 : (Real.log x / 2) ^ A ≤ Real.log (X:ℝ) ^ A := pow_le_pow_left₀ (by positivity) hlX A
    rw [div_pow] at h1
    have h2 : (X:ℝ) * (Real.log (X:ℝ) ^ A)⁻¹ ≤ 2 ^ A * x / Real.log x ^ A := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hLA]
      have h1' : Real.log x ^ A ≤ 2 ^ A * Real.log (X:ℝ) ^ A := by
        rw [div_le_iff₀ (by positivity)] at h1; linarith
      calc (X:ℝ) * Real.log x ^ A ≤ x * Real.log x ^ A := by gcongr
        _ ≤ x * (2 ^ A * Real.log (X:ℝ) ^ A) := by gcongr
        _ = _ := by ring
    calc C0 * (X * (Real.log (X:ℝ) ^ A)⁻¹) ≤ |C0| * (X * (Real.log (X:ℝ) ^ A)⁻¹) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C0| * (2 ^ A * x / Real.log x ^ A) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = _ := by ring
  -- psi - theta
  have hpt : |Chebyshev.theta x - Chebyshev.psi x| ≤ 2 * K * x / Real.log x ^ A := by
    have h1 := Chebyshev.psi_sub_theta_le (by linarith : (1:ℝ) ≤ x)
    have h2 := Chebyshev.theta_le_psi x
    have h3 := logpow_le_sqrt A x (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    refine h1.trans ?_
    rw [le_div_iff₀ hLA]
    have hs : √x * √x = x := Real.mul_self_sqrt hx0.le
    calc 2 * √x * Real.log x * Real.log x ^ A = 2 * √x * Real.log x ^ (A + 1) := by ring
      _ ≤ 2 * √x * (K * √x) := by gcongr
      _ = 2 * K * (√x * √x) := by ring
      _ = 2 * K * x := by rw [hs]
  -- floor part
  have hfl : |(X:ℝ) - x| ≤ K / Real.log 2 * x / Real.log x ^ A := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have h3 := logpow_le_sqrt A x (by linarith)
    have hsx : √x ≤ x := by
      have h1 : 1 ≤ √x := Real.one_le_sqrt.mpr (by linarith)
      nlinarith [Real.mul_self_sqrt hx0.le]
    have : Real.log x ^ A * Real.log 2 ≤ K * x := by
      calc Real.log x ^ A * Real.log 2 ≤ Real.log x ^ A * Real.log x := by gcongr
        _ = Real.log x ^ (A + 1) := by ring
        _ ≤ K * √x := h3
        _ ≤ K * x := by gcongr
    have key : 1 ≤ K / Real.log 2 * x / Real.log x ^ A := by
      rw [le_div_iff₀ hLA, div_mul_eq_mul_div, le_div_iff₀ hl2]; linarith
    linarith
  calc |Chebyshev.theta x - x| = |(Chebyshev.theta x - Chebyshev.psi x) + (Chebyshev.psi x - X) + (X - x)| := by ring_nf
    _ ≤ |Chebyshev.theta x - Chebyshev.psi x| + |Chebyshev.psi x - X| + |(X:ℝ) - x| := abs_add_three _ _ _
    _ ≤ 2 * K * x / Real.log x ^ A + |C0| * 2 ^ A * x / Real.log x ^ A + K / Real.log 2 * x / Real.log x ^ A := by
        gcongr
    _ = _ := by ring

end LET
end

-- ===== LE/S =====
section
open Finset Real Filter Topology MeasureTheory
open Chebyshev

namespace LES

noncomputable def g (t : ℝ) : ℝ := t / Real.log t

lemma hasDerivAt_g (t : ℝ) (ht : 1 < t) :
    HasDerivAt g (1 / Real.log t - 1 / Real.log t ^ 2) t := by
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have t0 : t ≠ 0 := by positivity
  have := (hasDerivAt_id t).div (Real.hasDerivAt_log t0) hl
  have h2 : HasDerivAt g ((1 * Real.log t - id t * t⁻¹) / Real.log t ^ 2) t := this
  refine h2.congr_deriv ?_
  rw [id_eq]; field_simp

lemma deriv_g (t : ℝ) (ht : 1 < t) : deriv g t = 1 / Real.log t - 1 / Real.log t ^ 2 :=
  (hasDerivAt_g t ht).deriv

lemma cont_g' (a b : ℝ) (ha : 1 < a) :
    ContinuousOn (fun t => 1 / Real.log t - 1 / Real.log t ^ 2) (Set.Icc a b) := by
  intro t ht
  have h1 : 1 < t := by linarith [ht.1]
  have hl : Real.log t ≠ 0 := (Real.log_pos h1).ne'
  have t0 : t ≠ 0 := by positivity
  apply ContinuousAt.continuousWithinAt
  have : ContinuousAt Real.log t := Real.continuousAt_log t0
  exact (continuousAt_const.div this hl).sub (continuousAt_const.div (this.pow 2) (pow_ne_zero _ hl))

/-- Abel summation for the sum of primes. -/
theorem S0_abel (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ Icc 0 ⌊x⌋₊ with p.Prime, (p : ℝ)) =
      x / Real.log x * θ x - ∫ t in (2:ℝ)..x, (1 / Real.log t - 1 / Real.log t ^ 2) * θ t := by
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) (fun n ↦ Real.log n)
  have ha : ∀ n, a n = if n.Prime then Real.log n else 0 := by
    intro n; by_cases h : n.Prime
    · rw [if_pos h]; exact Set.indicator_of_mem (s := Set.ofPred Nat.Prime) h _
    · rw [if_neg h]; exact Set.indicator_of_notMem h _
  have hsum : (∑ p ∈ Icc 0 ⌊x⌋₊ with p.Prime, (p : ℝ)) = ∑ n ∈ Icc 0 ⌊x⌋₊, g n * a n := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    by_cases h : n.Prime
    · have : Real.log n ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (mod_cast h.pos) (mod_cast h.ne_one)
      simp [ha, h, g]; field_simp
    · simp [ha, h]
  have hθ : ∀ t : ℝ, ∑ k ∈ Icc 0 ⌊t⌋₊, a k = θ t := by
    intro t; rw [theta_eq_sum_Icc, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    by_cases h : n.Prime <;> simp [ha, h]
  rw [hsum, sum_mul_eq_sub_integral_mul₁ a (by simp [ha, Nat.not_prime_zero])
    (by simp [ha, Nat.not_prime_one]) x
    (fun t ht => (hasDerivAt_g t (by linarith [ht.1])).differentiableAt) ?hint,
    ← intervalIntegral.integral_of_le hx, hθ]
  case hint =>
    refine ((cont_g' 2 x (by norm_num)).integrableOn_Icc).congr_fun (fun t ht => ?_) measurableSet_Icc
    rw [deriv_g t (by linarith [ht.1])]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le hx] at ht
  simp only [hθ, deriv_g t (by linarith [ht.1])]

noncomputable def J (x : ℝ) : ℝ := ∫ t in (2:ℝ)..x, t / Real.log t

lemma cont_div_logpow (k : ℕ) (a b : ℝ) (ha : 1 < a) :
    ContinuousOn (fun t => t / Real.log t ^ k) (Set.Icc a b) := by
  intro t ht
  have h1 : 1 < t := by linarith [ht.1]
  have hl : Real.log t ≠ 0 := (Real.log_pos h1).ne'
  apply ContinuousAt.continuousWithinAt
  exact continuousAt_id.div ((Real.continuousAt_log (by positivity)).pow k) (pow_ne_zero _ hl)

lemma int_identity (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, (1 / Real.log t - 1 / Real.log t ^ 2) * t =
      x ^ 2 / Real.log x - 4 / Real.log 2 - J x := by
  have hd : ∀ t ∈ Set.uIcc 2 x, HasDerivAt (fun t => t ^ 2 / Real.log t)
      (2 * (t / Real.log t) - t / Real.log t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have h1 : 1 < t := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos h1).ne'
    have t0 : t ≠ 0 := by positivity
    have := (hasDerivAt_pow 2 t).div (Real.hasDerivAt_log t0) hl
    refine this.congr_deriv ?_
    field_simp; ring
  have c1 := (cont_div_logpow 1 2 x (by norm_num)).intervalIntegrable_of_Icc (μ := volume) hx
  have c2 := (cont_div_logpow 2 2 x (by norm_num)).intervalIntegrable_of_Icc (μ := volume) hx
  simp only [pow_one] at c1
  have hint : IntervalIntegrable (fun t => 2 * (t / Real.log t) - t / Real.log t ^ 2) volume 2 x :=
    (c1.const_mul 2).sub c2
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_sub (c1.const_mul 2) c2, intervalIntegral.integral_const_mul] at hF
  have e : (fun t => (1 / Real.log t - 1 / Real.log t ^ 2) * t) = fun t => t / Real.log t - t / Real.log t ^ 2 := by
    funext t; ring
  rw [e, intervalIntegral.integral_sub c1 c2]
  unfold J
  norm_num at hF ⊢
  linarith

lemma theta_sum (t : ℝ) : θ t = ∑ k ∈ Icc 0 ⌊t⌋₊, (if k.Prime then Real.log k else 0) := by
  rw [theta_eq_sum_Icc, sum_filter]

lemma theta_int (x : ℝ) (hx : 2 ≤ x) :
    IntervalIntegrable (fun t => (1 / Real.log t - 1 / Real.log t ^ 2) * θ t) volume 2 x := by
  have h := integrableOn_mul_sum_Icc (fun k : ℕ => if k.Prime then Real.log k else 0) (m := 0)
    (a := 2) (b := x) (by norm_num) ((cont_g' 2 x (by norm_num)).integrableOn_Icc)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  refine (h.mono_set Set.Ioc_subset_Icc_self).congr_fun (fun t _ => ?_) measurableSet_Ioc
  simp only [theta_sum]

lemma int_split_bound (A : ℕ) (x : ℝ) (hx : 4 ≤ x) :
    ∫ t in (2:ℝ)..x, t / Real.log t ^ A ≤ x / Real.log 2 ^ A + 2 ^ A * x ^ 2 / Real.log x ^ A := by
  have hsx : 2 ≤ √x := by
    rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hss : √x * √x = x := Real.mul_self_sqrt (by linarith)
  have hsxx : √x ≤ x := by nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have i1 := (cont_div_logpow A 2 √x (by norm_num)).intervalIntegrable_of_Icc (μ := volume) hsx
  have i2 := (cont_div_logpow A √x x (by linarith)).intervalIntegrable_of_Icc (μ := volume) hsxx
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  have hA : ∫ t in (2:ℝ)..√x, t / Real.log t ^ A ≤ ∫ t in (2:ℝ)..√x, √x / Real.log 2 ^ A := by
    apply intervalIntegral.integral_mono_on hsx i1 intervalIntegrable_const
    intro t ht
    have h1 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
    have : Real.log 2 ^ A ≤ Real.log t ^ A := pow_le_pow_left₀ hl2.le h1 A
    have ht0 : 0 ≤ t := by linarith [ht.1]
    calc t / Real.log t ^ A ≤ √x / Real.log t ^ A := div_le_div_of_nonneg_right ht.2 (pow_nonneg (by linarith) A)
      _ ≤ √x / Real.log 2 ^ A := by gcongr
  have hB : ∫ t in √x..x, t / Real.log t ^ A ≤ ∫ t in √x..x, 2 ^ A * x / Real.log x ^ A := by
    apply intervalIntegral.integral_mono_on hsxx i2 intervalIntegrable_const
    intro t ht
    have h1 : Real.log x / 2 ≤ Real.log t := by
      rw [← Real.log_sqrt (by linarith)]; exact Real.log_le_log (by linarith) ht.1
    have h2 : (Real.log x / 2) ^ A ≤ Real.log t ^ A := pow_le_pow_left₀ (by positivity) h1 A
    rw [div_pow] at h2
    have hlt : 0 < Real.log t := by linarith [hlx]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h2
    have ht0 : 0 ≤ t := by linarith [ht.1]
    calc t * Real.log x ^ A ≤ x * Real.log x ^ A := by gcongr; exact ht.2
      _ ≤ x * (Real.log t ^ A * 2 ^ A) := by gcongr
      _ = _ := by ring
  rw [intervalIntegral.integral_const, smul_eq_mul] at hA hB
  have e1 : (√x - 2) * (√x / Real.log 2 ^ A) ≤ x / Real.log 2 ^ A := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]; nlinarith
  have e2 : (x - √x) * (2 ^ A * x / Real.log x ^ A) ≤ 2 ^ A * x ^ 2 / Real.log x ^ A := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
    have : 0 ≤ 2 ^ A * x := by positivity
    nlinarith [Real.sqrt_nonneg x]
  linarith

theorem S0_bound (A : ℕ) (hA : 1 ≤ A) (C : ℝ) (hC : 0 ≤ C)
    (hθb : ∀ x : ℝ, 2 ≤ x → |θ x - x| ≤ C * x / Real.log x ^ A) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x : ℝ, 4 ≤ x →
      |(∑ p ∈ Icc 0 ⌊x⌋₊ with p.Prime, (p:ℝ)) - J x - 4 / Real.log 2| ≤ C' * x ^ 2 / Real.log x ^ A := by
  obtain ⟨m, rfl⟩ : ∃ m, A = m + 1 := ⟨A - 1, by omega⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K := (2 * (m + 1 : ℝ)) ^ (m + 1) with hK
  set B := C * (1 + 1 / Real.log 2) with hB
  refine ⟨C / Real.log 2 + B * (K / Real.log 2 ^ (m + 2) + 2 ^ (m + 2) / Real.log 2), by positivity,
    fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2x : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
  have hab := S0_abel x (by linarith)
  have hid := int_identity x (by linarith)
  have ti := theta_int x (by linarith)
  have ci : IntervalIntegrable (fun t => (1 / Real.log t - 1 / Real.log t ^ 2) * t) volume 2 x := by
    have : ContinuousOn (fun t => (1 / Real.log t - 1 / Real.log t ^ 2) * t) (Set.Icc 2 x) :=
      (cont_g' 2 x (by norm_num)).mul continuousOn_id
    exact this.intervalIntegrable_of_Icc (by linarith)
  have hsub := intervalIntegral.integral_sub ti ci
  have eD : (∑ p ∈ Icc 0 ⌊x⌋₊ with p.Prime, (p:ℝ)) - J x - 4 / Real.log 2 =
      x / Real.log x * (θ x - x) -
        ∫ t in (2:ℝ)..x, ((1 / Real.log t - 1 / Real.log t ^ 2) * θ t - (1 / Real.log t - 1 / Real.log t ^ 2) * t) := by
    rw [hab, hsub, hid]; field_simp; ring
  rw [eD]
  -- bound 1
  have b1 : |x / Real.log x * (θ x - x)| ≤ C / Real.log 2 * x ^ 2 / Real.log x ^ (m + 1) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have h := hθb x (by linarith)
    calc x / Real.log x * |θ x - x| ≤ x / Real.log x * (C * x / Real.log x ^ (m + 1)) := by gcongr
      _ = C * x ^ 2 / (Real.log x * Real.log x ^ (m + 1)) := by field_simp
      _ ≤ C * x ^ 2 / (Real.log 2 * Real.log x ^ (m + 1)) := by gcongr
      _ = _ := by field_simp
  -- bound 2
  have hpt : ∀ t ∈ Set.Icc (2:ℝ) x,
      |(1 / Real.log t - 1 / Real.log t ^ 2) * θ t - (1 / Real.log t - 1 / Real.log t ^ 2) * t| ≤
        B * (t / Real.log t ^ (m + 2)) := by
    intro t ht
    have hlt2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
    have hlt : 0 < Real.log t := by linarith
    rw [← mul_sub, abs_mul]
    have hg : |1 / Real.log t - 1 / Real.log t ^ 2| ≤ (1 + 1 / Real.log 2) / Real.log t := by
      have h1 : 1 / Real.log t ^ 2 ≤ (1 / Real.log 2) * (1 / Real.log t) := by
        rw [pow_two, one_div_mul_one_div]
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have h2 : 0 ≤ 1 / Real.log t ^ 2 := by positivity
      rw [abs_le]; constructor
      · have : (1 + 1 / Real.log 2) / Real.log t = 1 / Real.log t + 1 / Real.log 2 * (1 / Real.log t) := by ring
        rw [this]; have : 0 ≤ 1 / Real.log t := by positivity
        linarith
      · have : (1 + 1 / Real.log 2) / Real.log t = 1 / Real.log t + 1 / Real.log 2 * (1 / Real.log t) := by ring
        rw [this]; have : 0 ≤ 1 / Real.log 2 * (1 / Real.log t) := by positivity
        linarith
    have he := hθb t ht.1
    calc |1 / Real.log t - 1 / Real.log t ^ 2| * |θ t - t|
        ≤ (1 + 1 / Real.log 2) / Real.log t * (C * t / Real.log t ^ (m + 1)) := by gcongr
      _ = B * (t / Real.log t ^ (m + 2)) := by rw [hB]; field_simp; ring
  have b2 : |∫ t in (2:ℝ)..x, ((1 / Real.log t - 1 / Real.log t ^ 2) * θ t - (1 / Real.log t - 1 / Real.log t ^ 2) * t)|
      ≤ B * (x / Real.log 2 ^ (m + 2) + 2 ^ (m + 2) * x ^ 2 / Real.log x ^ (m + 2)) := by
    refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
    have hc := (cont_div_logpow (m + 2) 2 x (by norm_num)).intervalIntegrable_of_Icc (μ := volume) (by linarith)
    calc _ ≤ ∫ t in (2:ℝ)..x, B * (t / Real.log t ^ (m + 2)) :=
          intervalIntegral.integral_mono_on (by linarith) (ti.sub ci).abs (hc.const_mul B) hpt
      _ = B * ∫ t in (2:ℝ)..x, t / Real.log t ^ (m + 2) := intervalIntegral.integral_const_mul _ _
      _ ≤ _ := by gcongr; exact int_split_bound (m + 2) x hx
  -- conversions
  have hL : Real.log x ^ (m + 1) ≤ K * x := by
    have h3 := LET.logpow_le_sqrt m x (by linarith)
    have : √x ≤ x := by
      have h1 : 1 ≤ √x := Real.one_le_sqrt.mpr (by linarith)
      nlinarith [Real.mul_self_sqrt hx0.le]
    calc _ ≤ K * √x := h3
      _ ≤ K * x := by gcongr
  have c1 : x / Real.log 2 ^ (m + 2) ≤ K / Real.log 2 ^ (m + 2) * x ^ 2 / Real.log x ^ (m + 1) := by
    have hx1 : x ≤ K * x ^ 2 / Real.log x ^ (m + 1) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    calc x / Real.log 2 ^ (m + 2) ≤ (K * x ^ 2 / Real.log x ^ (m + 1)) / Real.log 2 ^ (m + 2) := by gcongr
      _ = _ := by ring
  have c2 : 2 ^ (m + 2) * x ^ 2 / Real.log x ^ (m + 2) ≤ 2 ^ (m + 2) / Real.log 2 * x ^ 2 / Real.log x ^ (m + 1) := by
    have hp : Real.log x ^ (m + 1) * Real.log 2 ≤ Real.log x ^ (m + 2) := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left hl2x (by positivity)
    calc 2 ^ (m + 2) * x ^ 2 / Real.log x ^ (m + 2) ≤ 2 ^ (m + 2) * x ^ 2 / (Real.log x ^ (m + 1) * Real.log 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hp
      _ = _ := by field_simp
  have hB0 : 0 ≤ B := by positivity
  calc |x / Real.log x * (θ x - x) - _| ≤ |x / Real.log x * (θ x - x)| + |∫ t in (2:ℝ)..x, _| := abs_sub _ _
    _ ≤ C / Real.log 2 * x ^ 2 / Real.log x ^ (m + 1) +
        B * (K / Real.log 2 ^ (m + 2) * x ^ 2 / Real.log x ^ (m + 1) +
          2 ^ (m + 2) / Real.log 2 * x ^ 2 / Real.log x ^ (m + 1)) := by
        gcongr
        exact b2.trans (by gcongr)
    _ = _ := by ring

end LES
end

-- ===== LE/U =====
section
open Finset Real Filter Topology
open LandauFunction

namespace LEU
open LGA LGB LandauPartition

lemma lam_le (M : ℕ) (hM : 4 ≤ M) (p : ℕ) (hp : p.Prime) (hpM : p ≤ M) :
    Real.log M / M * p ≤ Real.log p := by
  have hM0 : (0 : ℝ) < M := by positivity
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have key : Real.log M / M ≤ Real.log p / p := by
    rcases Nat.lt_or_ge p 3 with h | h
    · have hp2 : p = 2 := by have := hp.two_le; omega
      subst hp2
      have h4 : Real.log (M : ℝ) / M ≤ Real.log 4 / 4 := by
        have he : Real.exp 1 ≤ (4 : ℝ) := by have := Real.exp_one_lt_d9; linarith
        exact Real.log_div_self_antitoneOn (show (4:ℝ) ∈ Set.Ici (Real.exp 1) from he)
          (show (M:ℝ) ∈ Set.Ici (Real.exp 1) from le_trans he (by exact_mod_cast hM)) (by exact_mod_cast hM)
      have : Real.log (4:ℝ) / 4 = Real.log 2 / 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
      push_cast; linarith
    · have he : Real.exp 1 ≤ (p : ℝ) := by
        have := Real.exp_one_lt_d9; have : (3:ℝ) ≤ p := by exact_mod_cast h
        linarith
      exact Real.log_div_self_antitoneOn (show (p:ℝ) ∈ Set.Ici (Real.exp 1) from he)
        (show (M:ℝ) ∈ Set.Ici (Real.exp 1) from le_trans he (by exact_mod_cast hpM)) (by exact_mod_cast hpM)
  rw [div_le_div_iff₀ hM0 hp0] at key
  rw [div_mul_eq_mul_div, div_le_iff₀ hM0]; linarith

/-- per-prime bound -/
lemma term_le2 (M : ℕ) (hM : 4 ≤ M) (p v : ℕ) (hp : p.Prime) (hv : 1 ≤ v) :
    (v : ℝ) * Real.log p - Real.log M / M * ((p : ℝ) ^ v) ≤
      (if p ≤ M then Real.log p - Real.log M / M * p else 0) +
      (if p ≤ Nat.sqrt M then Real.log M else 0) := by
  have hM0 : (0 : ℝ) < M := by positivity
  have hlM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlam : 0 < Real.log M / M := div_pos hlM hM0
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hlog : (v : ℝ) * Real.log p = Real.log ((p : ℝ) ^ v) := (Real.log_pow (p : ℝ) v).symm
  have hA : 0 ≤ (if p ≤ M then Real.log p - Real.log M / M * p else 0) := by
    split_ifs with h
    · linarith [lam_le M hM p hp h]
    · exact le_refl _
  have hB : 0 ≤ (if p ≤ Nat.sqrt M then Real.log M else 0) := by split_ifs <;> linarith
  by_cases hq : (p : ℝ) ^ v ≤ M
  · rcases Nat.lt_or_ge v 2 with hv1 | hv2
    · have : v = 1 := by omega
      subst this
      have hpM : p ≤ M := by simpa using hq
      rw [if_pos hpM]; simp; linarith
    · -- p^2 ≤ M
      have hp2 : p * p ≤ M := by
        have : (p : ℝ) ^ 2 ≤ M := le_trans (pow_le_pow_right₀ hp1 hv2) hq
        exact_mod_cast (by push_cast; nlinarith : ((p * p : ℕ) : ℝ) ≤ M)
      have hps : p ≤ Nat.sqrt M := Nat.le_sqrt.2 hp2
      rw [if_pos hps, hlog]
      have h1 : Real.log ((p : ℝ) ^ v) ≤ Real.log M := Real.log_le_log (by positivity) hq
      have h2 : 0 ≤ Real.log M / M * (p : ℝ) ^ v := by positivity
      linarith
  · push Not at hq
    have he : Real.exp 1 ≤ (M : ℝ) := by
      have := Real.exp_one_lt_d9
      have : (4 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have hanti := Real.log_div_self_antitoneOn (show (M : ℝ) ∈ Set.Ici (Real.exp 1) from he)
      (show (p : ℝ) ^ v ∈ Set.Ici (Real.exp 1) from le_trans he hq.le) hq.le
    simp only at hanti
    have hq0 : (0 : ℝ) < (p : ℝ) ^ v := by positivity
    rw [div_le_div_iff₀ hq0 hM0] at hanti
    have : Real.log ((p : ℝ) ^ v) ≤ Real.log M / M * (p : ℝ) ^ v := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hM0]; linarith
    rw [hlog]
    linarith

/-- Sharper upper bound (Landau's Lagrangian argument with exact `θ`). -/
lemma upper2 (s : Multiset ℕ) (hs : ∀ a ∈ s, 0 < a) (M : ℕ) (hM : 4 ≤ M) :
    Real.log (s.lcm) ≤ th M - Real.log M / M * S0 M + s.sum * Real.log M / M
      + (Nat.sqrt M + 1) * Real.log M := by
  have hL : s.lcm ≠ 0 := by
    intro h; rw [Multiset.lcm_eq_zero_iff] at h; exact (hs 0 h).ne' rfl
  set L := s.lcm
  set lam := Real.log M / M with hlam_def
  have hM0 : (0 : ℝ) < M := by positivity
  have hlM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlam : 0 < lam := div_pos hlM hM0
  have hQ : (∑ p ∈ L.primeFactors, ((p : ℝ) ^ L.factorization p)) ≤ s.sum := by
    have := Q s hs
    exact_mod_cast this
  have hterm : ∀ p ∈ L.primeFactors, (L.factorization p : ℝ) * Real.log p - lam * ((p : ℝ) ^ L.factorization p) ≤
      (if p ≤ M then Real.log p - lam * p else 0) + (if p ≤ Nat.sqrt M then Real.log M else 0) := by
    intro p hp
    have hv : 1 ≤ L.factorization p := by
      rw [← Nat.support_factorization] at hp
      exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hp)
    exact term_le2 M hM p _ (Nat.prime_of_mem_primeFactors hp) hv
  have hsum := sum_le_sum hterm
  rw [sum_sub_distrib, ← mul_sum, sum_add_distrib] at hsum
  have hg : ∑ p ∈ L.primeFactors, (if p ≤ M then Real.log p - lam * p else 0) ≤
      ∑ p ∈ P M, (Real.log p - lam * p) := by
    rw [← sum_filter]
    refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p hp _ => ?_)
    · simp only [mem_filter] at hp
      simp only [P, mem_filter, mem_range]
      exact ⟨by omega, Nat.prime_of_mem_primeFactors hp.1⟩
    · simp only [P, mem_filter, mem_range] at hp
      linarith [lam_le M hM p hp.2 (by omega)]
  have hg2 : ∑ p ∈ L.primeFactors, (if p ≤ Nat.sqrt M then Real.log M else 0) ≤
      (Nat.sqrt M + 1) * Real.log M := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hlM.le
    have : (L.primeFactors.filter (fun p => p ≤ Nat.sqrt M)) ⊆ range (Nat.sqrt M + 1) := by
      intro p hp; simp only [mem_filter] at hp; simp; omega
    have := card_le_card this
    simp at this
    exact_mod_cast this
  have hPM : ∑ p ∈ P M, (Real.log p - lam * p) = th M - lam * S0 M := by
    rw [sum_sub_distrib, ← mul_sum]
    rfl
  rw [log_lcm L hL]
  have : lam * (∑ p ∈ L.primeFactors, ((p : ℝ) ^ L.factorization p)) ≤ lam * s.sum :=
    mul_le_mul_of_nonneg_left hQ hlam.le
  have e : (s.sum : ℝ) * Real.log M / M = lam * s.sum := by rw [hlam_def]; ring
  rw [e]
  linarith

lemma landau_upper (n M : ℕ) (hM : 4 ≤ M) :
    Real.log (landau n) ≤ th M - Real.log M / M * S0 M + n * Real.log M / M
      + (Nat.sqrt M + 1) * Real.log M := by
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Nat.Partition n))
    Finset.univ_nonempty (fun p => p.parts.lcm)
  have hg : landau n = p.parts.lcm := by rw [landau_eq_sup, hp]
  have hup := upper2 p.parts (fun i hi => p.parts_pos hi) M hM
  rw [p.parts_sum, ← hg] at hup
  exact hup

end LEU
end

-- ===== RP/A =====
section
namespace RPAux

noncomputable def f (L : ℝ) : ℝ := 1/L + 1/L^2 + 2/L^3 + 6/L^4 + 24/L^5

lemma main_poly (L : ℝ) (hL : 10 ≤ L) : f L ^ 2 - f (L-1) / L ≤ -1/(2*L^6) := by
  have h0 : 0 < L := by linarith
  have h1 : 0 < L - 1 := by linarith
  have key : f L ^ 2 - f (L-1) / L + 1/(2*L^6) =
      ((-1152) + 5184*L - 8904*L^2 + 6936*L^3 - 2049*L^4 + 85*L^5 - 444*L^6 + 560*L^7
        - 263*L^8 - L^9) / (2 * L^10 * (L-1)^5) := by
    unfold f; field_simp; ring
  have hP : (-1152) + 5184*L - 8904*L^2 + 6936*L^3 - 2049*L^4 + 85*L^5 - 444*L^6 + 560*L^7
        - 263*L^8 - L^9 ≤ 0 := by
    obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ L = 10 + s := ⟨L - 10, by linarith, by ring⟩
    have := pow_nonneg hs 2; have := pow_nonneg hs 3; have := pow_nonneg hs 4
    have := pow_nonneg hs 5; have := pow_nonneg hs 6; have := pow_nonneg hs 7
    have := pow_nonneg hs 8; have := pow_nonneg hs 9
    ring_nf; linarith
  have : ((-1152) + 5184*L - 8904*L^2 + 6936*L^3 - 2049*L^4 + 85*L^5 - 444*L^6 + 560*L^7
        - 263*L^8 - L^9) / (2 * L^10 * (L-1)^5) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hP (by positivity)
  have e : -1/(2*L^6) = - (1/(2*L^6)) := by ring
  linarith

lemma f_nonneg (L : ℝ) (hL : 0 < L) : 0 ≤ f L := by unfold f; positivity

lemma f_le (L : ℝ) (hL : 10 ≤ L) : f L ≤ 2 / L := by
  have h0 : 0 < L := by linarith
  unfold f
  rw [div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity) (by positivity),
    div_add_div _ _ (by positivity) (by positivity), div_add_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) h0]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ L = 10 + s := ⟨L - 10, by linarith, by ring⟩
  have := pow_nonneg hs 2; have := pow_nonneg hs 3; have := pow_nonneg hs 4
  have := pow_nonneg hs 5; have := pow_nonneg hs 6; have := pow_nonneg hs 7
  have := pow_nonneg hs 8; have := pow_nonneg hs 9; have := pow_nonneg hs 10
  have := pow_nonneg hs 11; have := pow_nonneg hs 12; have := pow_nonneg hs 13
  have := pow_nonneg hs 14; have := pow_nonneg hs 15; have := pow_nonneg hs 16
  ring_nf; nlinarith

/-- the final algebraic step -/
lemma alg (K : ℝ) (hK : 0 ≤ K) : ∃ L0 : ℝ, ∀ L, L0 ≤ L → ∀ x : ℝ, 0 < x → ∀ a b : ℝ,
    |a - x * f L| ≤ K * x / L^6 → |b - x / Real.exp 1 * f (L-1)| ≤ K * (x / Real.exp 1) / (L-1)^6 →
    a^2 < Real.exp 1 * x / L * b := by
  refine ⟨10 + 2 * (K^2 + 68*K), fun L hL x hx a b ha hb => ?_⟩
  have hL10 : 10 ≤ L := by nlinarith
  have h0 : 0 < L := by linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  -- normalise
  set α := a / x with hα
  set β := b * Real.exp 1 / x with hβ
  have ha' : |α - f L| ≤ K / L^6 := by
    have : α - f L = (a - x * f L) / x := by rw [hα]; field_simp
    rw [this, abs_div, abs_of_pos hx, div_le_iff₀ hx]; calc _ ≤ K * x / L^6 := ha
      _ = _ := by ring
  have hb' : |β - f (L-1)| ≤ K / (L-1)^6 := by
    have : β - f (L-1) = (b - x / Real.exp 1 * f (L-1)) * (Real.exp 1 / x) := by
      rw [hβ]; field_simp
    rw [this, abs_mul, abs_of_pos (by positivity : 0 < Real.exp 1 / x)]
    calc _ ≤ K * (x / Real.exp 1) / (L-1)^6 * (Real.exp 1 / x) := by gcongr
      _ = _ := by field_simp
  suffices hs : α^2 < β / L by
    have e1 : a = α * x := by rw [hα]; field_simp
    have e2 : b = β * x / Real.exp 1 := by rw [hβ]; field_simp
    rw [e1, e2]
    have : Real.exp 1 * x / L * (β * x / Real.exp 1) = β / L * x^2 := by field_simp
    rw [this, mul_pow]; exact mul_lt_mul_of_pos_right hs (by positivity)
  have hM := main_poly L hL10
  have hf0 := f_nonneg L h0
  have hf2 := f_le L hL10
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha'
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb'
  have hL1 : L / 2 ≤ L - 1 := by linarith
  have hinv : K / (L-1)^6 ≤ 64 * K / L^6 := by
    rw [div_le_div_iff₀ (pow_pos (by linarith) 6) (by positivity)]
    have : L^6 ≤ 64 * (L-1)^6 := by
      have := pow_le_pow_left₀ (by positivity) hL1 6
      nlinarith
    nlinarith
  -- α^2 ≤ (f + ε)^2 with |ε| ≤ K/L^6
  set ε := K / L^6 with hε
  have hε0 : 0 ≤ ε := by positivity
  have hα2 : α^2 ≤ f L ^ 2 + 2 * (2 / L) * ε + ε^2 := by
    have hαabs : |α| ≤ f L + ε := by
      calc |α| = |f L + (α - f L)| := by ring_nf
        _ ≤ |f L| + |α - f L| := abs_add_le _ _
        _ ≤ f L + ε := by rw [abs_of_nonneg hf0]; linarith
    have : α^2 ≤ (f L + ε)^2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hαabs 2
    nlinarith
  have hβL : f (L-1) / L - 64 * ε / L ≤ β / L := by
    have e64 : 64 * K / L^6 = 64 * ε := by rw [hε]; ring
    rw [← sub_div]; apply div_le_div_of_nonneg_right _ h0.le; linarith
  -- ε ≤ ... and ε^2 ≤ K^2 / L^12 ≤ K^2/L^7
  have hεL : ε * L^6 = K := by rw [hε]; field_simp
  -- multiply everything by L^7
  have key : (f L ^ 2 + 2 * (2 / L) * ε + ε^2) - (f (L-1) / L - 64 * ε / L) < 0 := by
    have e : (f L ^ 2 + 2 * (2 / L) * ε + ε^2) - (f (L-1) / L - 64 * ε / L)
        = (f L ^ 2 - f (L-1) / L) + (68 * K + K^2 / L^5) / L^7 := by
      rw [hε]; field_simp; ring
    rw [e]
    have hK5 : K^2 / L^5 ≤ K^2 := div_le_self (by positivity) (one_le_pow₀ (by linarith))
    have : (68 * K + K^2 / L^5) / L^7 ≤ (68 * K + K^2) / L^7 := by gcongr
    have h2 : (68 * K + K^2) / L^7 < 1 / (2 * L^6) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have : (68 * K + K^2) * 2 < L := by nlinarith
      have hL6 : 0 < L^6 := by positivity
      calc (68 * K + K ^ 2) * (2 * L ^ 6) = ((68 * K + K^2) * 2) * L^6 := by ring
        _ < L * L^6 := by gcongr
        _ = 1 * L^7 := by ring
    have e2 : -1/(2*L^6) = - (1/(2*L^6)) := by ring
    linarith
  linarith

end RPAux
end

-- ===== RP/B =====
section
namespace RPAux
open Real Filter

lemma hasDeriv_g (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun t => t * f (log t)) (1 / log t - 120 / (log t)^6) t := by
  have t0 : t ≠ 0 := by positivity
  have hl : 0 < log t := log_pos ht
  have h1 : HasDerivAt log t⁻¹ t := hasDerivAt_log t0
  have h2 : HasDerivAt (fun t => (log t)⁻¹) (-(t⁻¹) / (log t)^2) t := h1.inv hl.ne'
  have hf : ∀ s, 0 < s → f s = s⁻¹ + s⁻¹^2 + 2 * s⁻¹^3 + 6 * s⁻¹^4 + 24 * s⁻¹^5 := by
    intro s hs; unfold f; field_simp
  have h3 := (((h2.add (h2.pow 2)).add ((h2.pow 3).const_mul 2)).add ((h2.pow 4).const_mul 6)).add
    ((h2.pow 5).const_mul 24)
  have h4 := (hasDerivAt_id t).mul h3
  refine (h4.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [lt_mem_nhds ht] with y hy
    rw [hf _ (log_pos hy)]; simp
  simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, id]; norm_num
  field_simp
  ring

lemma cont_pow (n : ℕ) (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn (fun t => 1 / (log t)^n) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.pow
    exact continuousOn_log.mono (fun t ht => by simp; linarith [ht.1])
  · intro t ht; exact pow_ne_zero _ (log_pos (by linarith [ht.1])).ne'

lemma li_eq (x : ℝ) (hx : 2 ≤ x) :
    (∫ t in (2:ℝ)..x, 1 / log t) = x * f (log x) - 2 * f (log 2) + 120 * ∫ t in (2:ℝ)..x, 1 / (log t)^6 := by
  have h1 := (cont_pow 1 2 x (by norm_num) hx).intervalIntegrable (μ := MeasureTheory.volume)
  have h6 := (cont_pow 6 2 x (by norm_num) hx).intervalIntegrable (μ := MeasureTheory.volume)
  have hd : ∀ t ∈ Set.uIcc 2 x, HasDerivAt (fun t => t * f (log t)) (1 / log t - 120 / (log t)^6) t := by
    intro t ht; rw [Set.uIcc_of_le hx] at ht; exact hasDeriv_g t (by linarith [ht.1])
  have hi : IntervalIntegrable (fun t => 1 / log t - 120 / (log t)^6) MeasureTheory.volume 2 x := by
    have := h1.sub (h6.const_mul 120); simp only [pow_one] at this
    refine this.congr ?_; intro t _; simp [div_eq_mul_inv]
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have e : (fun t => 1 / log t - 120 / (log t)^6) = fun t => 1 / log t - 120 * (1 / (log t)^6) := by
    ext t; ring
  rw [e, intervalIntegral.integral_sub (by simpa using h1) (h6.const_mul 120),
    intervalIntegral.integral_const_mul] at this
  linarith

lemma ev_small (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ∀ᶠ x in atTop, c + d * √x ≤ x / (log x)^6 := by
  have hb := (isLittleO_pow_log_id_atTop (n := 6)).bound (c := 1 / (64 * (c + d + 1))) (by positivity)
  have h2 := tendsto_sqrt_atTop.eventually hb
  filter_upwards [h2, eventually_ge_atTop 4] with x hx hx4
  have hy : 2 ≤ √x := by rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2^2 by norm_num, sqrt_sq (by norm_num)]]; exact sqrt_le_sqrt hx4
  have hly : 0 < log √x := log_pos (by linarith)
  have hlx : log x = 2 * log √x := by rw [log_sqrt (by linarith)]; ring
  simp only [norm_pow, Real.norm_eq_abs, id, abs_of_pos hly, abs_of_pos (by linarith : (0:ℝ) < √x)] at hx
  have hsq : x = √x * √x := (mul_self_sqrt (by linarith)).symm
  have hL6 : (log x)^6 ≤ √x / (c + d + 1) := by
    rw [hlx, mul_pow]
    calc (2:ℝ)^6 * log √x ^ 6 ≤ 2^6 * (1 / (64 * (c + d + 1)) * √x) := by gcongr
      _ = _ := by field_simp; norm_num
  have hpos : 0 < (log x)^6 := by rw [hlx]; positivity
  calc c + d * √x ≤ (c + d + 1) * √x := by nlinarith
    _ = x / (√x / (c + d + 1)) := by
        have hs0 : 0 < √x := by linarith
        rw [div_div_eq_mul_div, eq_div_iff hs0.ne', mul_assoc, ← hsq]; ring
    _ ≤ x / (log x)^6 := by gcongr

lemma li_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x in atTop,
    |(∫ t in (2:ℝ)..x, 1 / log t) - x * f (log x)| ≤ K * x / (log x)^6 := by
  have hf2 : 0 ≤ f (log 2) := f_nonneg _ (log_pos (by norm_num))
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  refine ⟨1 + 120 * 64, by norm_num, ?_⟩
  filter_upwards [ev_small (2 * f (log 2)) (120 / (log 2)^6) (by positivity) (by positivity),
    eventually_ge_atTop 4] with x hx hx4
  have hsx : 2 ≤ √x := by rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2^2 by norm_num, sqrt_sq (by norm_num)]]; exact sqrt_le_sqrt hx4
  have hsxx : √x ≤ x := by
    nlinarith [mul_self_sqrt (by linarith : (0:ℝ) ≤ x)]
  have hlx : 0 < log x := log_pos (by linarith)
  rw [li_eq x (by linarith)]
  have hI0 : 0 ≤ ∫ t in (2:ℝ)..x, 1 / (log t)^6 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t ht => by
      have := log_pos (by linarith [ht.1] : (1:ℝ) < t); positivity)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((cont_pow 6 2 √x (by norm_num) hsx).intervalIntegrable (μ := MeasureTheory.volume)) ((cont_pow 6 √x x (by linarith) hsxx).intervalIntegrable (μ := MeasureTheory.volume))
  have hA : (∫ t in (2:ℝ)..√x, 1 / (log t)^6) ≤ ∫ t in (2:ℝ)..√x, 1 / (log 2)^6 := by
    apply intervalIntegral.integral_mono_on hsx ((cont_pow 6 2 √x (by norm_num) hsx).intervalIntegrable (μ := MeasureTheory.volume))
      intervalIntegrable_const
    intro t ht
    have := log_le_log (by norm_num) ht.1
    gcongr
  have hB : (∫ t in √x..x, 1 / (log t)^6) ≤ ∫ t in √x..x, 64 / (log x)^6 := by
    apply intervalIntegral.integral_mono_on hsxx ((cont_pow 6 √x x (by linarith) hsxx).intervalIntegrable (μ := MeasureTheory.volume))
      intervalIntegrable_const
    intro t ht
    have h1 : log x / 2 ≤ log t := by
      rw [← log_sqrt (by linarith)]; exact log_le_log (by linarith) ht.1
    have h2 : 0 < log x / 2 := by positivity
    rw [div_le_div_iff₀ (pow_pos (by linarith) 6) (by positivity)]
    have := pow_le_pow_left₀ h2.le h1 6
    nlinarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hA hB
  have hB' : (x - √x) * (64 / (log x)^6) ≤ 64 * x / (log x)^6 := by
    rw [show (x - √x) * (64 / (log x)^6) = 64 * (x - √x) / (log x)^6 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith [sqrt_nonneg x]
  have hA' : (√x - 2) * (1 / (log 2)^6) ≤ √x * (1 / (log 2)^6) := by gcongr; linarith
  rw [abs_le]; constructor
  · have : 0 ≤ x / (log x)^6 := by positivity
    have h120 : 0 ≤ 120 / (log 2)^6 * √x := by positivity
    have e : (1 + 120 * 64) * x / (log x)^6 = x / (log x)^6 + 7680 * (x / (log x)^6) := by ring
    rw [e]; nlinarith
  · have e : (1 + 120 * 64) * x / (log x)^6 = x / (log x)^6 + 120 * (64 * x / (log x)^6) := by ring
    rw [e]
    have : 120 / (log 2)^6 * √x = 120 * (√x * (1 / (log 2)^6)) := by ring
    nlinarith

end RPAux
end

-- ===== LE/I =====
section
namespace LEI
open Real

noncomputable def q0 (t : ℝ) : ℝ := (-1/8) + (7/8)*t + (-23/8)*t^2 + (33/8)*t^3
noncomputable def q1 (t : ℝ) : ℝ := (-31/64) + (51/16)*t + (-281/32)*t^2 + (79/16)*t^3 + (1241/64)*t^4
noncomputable def q2 (t : ℝ) : ℝ := (-11/16) + (233/64)*t + (-75/16)*t^2 + (-609/32)*t^3 + (40)*t^4 + (-2303/64)*t^5
noncomputable def q3 (t : ℝ) : ℝ := (-13/32) + (39/64)*t + (287/32)*t^2 + (-1351/32)*t^3 + (927/32)*t^4 + (831/64)*t^5 + (-1285/32)*t^6
noncomputable def q4 (t : ℝ) : ℝ := (-1/16) + (-81/64)*t + (623/64)*t^2 + (-1127/64)*t^3 + (-1037/32)*t^4 + (5629/64)*t^5 + (-5257/64)*t^6 + (2563/64)*t^7
noncomputable def q5 (t : ℝ) : ℝ := (1/64) + (-31/64)*t + (9/16)*t^2 + (429/32)*t^3 + (-3693/64)*t^4 + (4141/64)*t^5 + (155/32)*t^6 + (-379/8)*t^7 + (977/32)*t^8
noncomputable def q6 (t : ℝ) : ℝ := (1/16)*t + (-85/64)*t^2 + (55/8)*t^3 + (-255/32)*t^4 + (-1915/64)*t^5 + (5695/64)*t^6 + (-2687/32)*t^7 + (517/16)*t^8 + (-323/64)*t^9
noncomputable def q7 (t : ℝ) : ℝ := (3/32)*t^2 + (-109/64)*t^3 + (343/32)*t^4 + (-1955/64)*t^5 + (301/8)*t^6 + (-371/64)*t^7 + (-889/32)*t^8 + (1411/64)*t^9 + (-149/32)*t^10
noncomputable def q8 (t : ℝ) : ℝ := (1/16)*t^3 + (-67/64)*t^4 + (445/64)*t^5 + (-1527/64)*t^6 + (2929/64)*t^7 + (-3145/64)*t^8 + (1751/64)*t^9 + (-381/64)*t^10 + (-9/64)*t^11
noncomputable def q9 (t : ℝ) : ℝ := (1/64)*t^4 + (-1/4)*t^5 + (27/16)*t^6 + (-25/4)*t^7 + (443/32)*t^8 + (-75/4)*t^9 + (243/16)*t^10 + (-27/4)*t^11 + (81/64)*t^12

noncomputable def Q0 (d t : ℝ) : ℝ := q0 t + d * (q1 t + d * (q2 t + d * (q3 t + d * (q4 t + d * (q5 t + d * (q6 t + d * (q7 t + d * (q8 t + d * (q9 t)))))))))

lemma N0_eq (d t : ℝ) :
    let s := d * t
    let α := (d - s) / 2 - (d ^ 2 - 6 * d * s + 9 * s ^ 2) / 8
    let e0 := d + s * (d - s)
    (1 + α) ^ 2 * ((1 + e0) ^ 4 + s * (1 + e0) ^ 3 + 2 * s ^ 2 * (1 + e0) ^ 2 + 6 * s ^ 3 * (1 + e0)
      + 24 * s ^ 4) - (1 + e0) ^ 5 = d ^ 3 * Q0 d t := by
  intro s α e0
  simp only [s, α, e0, Q0, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]
  ring

lemma Q0_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ d t : ℝ, d ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → |Q0 d t| ≤ C := by
  have hc : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Q0 p.1 p.2) (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) := by
    apply Continuous.continuousOn; unfold Q0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9; fun_prop
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun d t hd ht => ?_⟩
  have := hC (d, t) ⟨hd, ht⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)


lemma pow_diff (A B : ℝ) (m : ℕ) (hA : |A| ≤ 2) (hB : |B| ≤ 2) :
    |A ^ m - B ^ m| ≤ |A - B| * m * 2 ^ (m - 1) := by
  refine (abs_pow_sub_pow_le A B m).trans ?_
  gcongr
  exact max_le hA hB

theorem core : ∃ C : ℝ, 0 ≤ C ∧ ∀ d s a L1 e : ℝ, 0 < d → 0 ≤ s → s ≤ d → d ≤ 1 / 10 →
    a = (d - s) / 2 - (d ^ 2 - 6 * d * s + 9 * s ^ 2) / 8 →
    |L1 - (a - a ^ 2 / 2)| ≤ 2 * d ^ 3 → e = d + 2 * s * L1 →
    |(1 + a) ^ 2 * (1 / (1 + e) + s / (1 + e) ^ 2 + 2 * s ^ 2 / (1 + e) ^ 3 + 6 * s ^ 3 / (1 + e) ^ 4
      + 24 * s ^ 4 / (1 + e) ^ 5) - 1| ≤ C * d ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := Q0_bound
  refine ⟨32 * (C + 1000), by positivity, ?_⟩
  intro d s a L1 e hd hs hsd hd1 ha hL he
  set e0 := d + s * (d - s) with he0
  have hd3 : 0 ≤ d ^ 3 := by positivity
  -- bounds on a
  have ha1 : |a - (d - s) / 2| ≤ 2 * d ^ 2 := by
    rw [ha, abs_le]; constructor <;> nlinarith [mul_nonneg hs hd.le, mul_nonneg hs hs]
  have hab : |a| ≤ d := by
    have : |a| ≤ |a - (d - s) / 2| + |(d - s) / 2| := by
      have := abs_add_le (a - (d - s) / 2) ((d - s) / 2); simpa using this
    rw [abs_of_nonneg (by linarith : 0 ≤ (d - s) / 2)] at this
    nlinarith
  have hL0 : |L1 - (d - s) / 2| ≤ 3 * d ^ 2 := by
    have e1 : L1 - (d - s) / 2 = (L1 - (a - a ^ 2 / 2)) + (a - (d - s) / 2) - a ^ 2 / 2 := by ring
    rw [e1]
    have h2 : a ^ 2 ≤ d ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    have h3 : |a ^ 2 / 2| ≤ d ^ 2 / 2 := by rw [abs_of_nonneg (by positivity)]; linarith
    have h4 : 2 * d ^ 3 ≤ d ^ 2 / 2 := by nlinarith
    calc _ ≤ |(L1 - (a - a ^ 2 / 2)) + (a - (d - s) / 2)| + |a ^ 2 / 2| := abs_sub _ _
      _ ≤ |L1 - (a - a ^ 2 / 2)| + |a - (d - s) / 2| + |a ^ 2 / 2| := by gcongr; exact abs_add_le _ _
      _ ≤ 3 * d ^ 2 := by linarith
  have hee : |e - e0| ≤ 6 * d ^ 3 := by
    have : e - e0 = 2 * s * (L1 - (d - s) / 2) := by rw [he, he0]; ring
    rw [this, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * s)]
    calc 2 * s * |L1 - (d - s) / 2| ≤ 2 * d * (3 * d ^ 2) := by gcongr
      _ = 6 * d ^ 3 := by ring
  have he0b : 0 ≤ e0 ∧ e0 ≤ 2 * d := by
    constructor <;> nlinarith [mul_nonneg hs (by linarith : (0:ℝ) ≤ d - s)]
  have hd3' : 6 * d ^ 3 ≤ 6 / 1000 := by
    have : d ^ 3 ≤ (1 / 10) ^ 3 := pow_le_pow_left₀ hd.le hd1 3
    linarith
  have heb : |e - e0| ≤ 6 / 1000 := hee.trans hd3'
  rw [abs_le] at heb
  have hA : (1 / 2 : ℝ) ≤ 1 + e := by linarith
  have hA2 : |1 + e| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hB2 : |1 + e0| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  set A := 1 + e with hAdef
  set B := 1 + e0 with hBdef
  have hAB : |A - B| = |e - e0| := by rw [hAdef, hBdef]; ring_nf
  have hApos : 0 < A := by linarith
  -- rewrite the target
  have key : (1 + a) ^ 2 * (1 / A + s / A ^ 2 + 2 * s ^ 2 / A ^ 3 + 6 * s ^ 3 / A ^ 4 + 24 * s ^ 4 / A ^ 5) - 1
      = ((1 + a) ^ 2 * (A ^ 4 + s * A ^ 3 + 2 * s ^ 2 * A ^ 2 + 6 * s ^ 3 * A + 24 * s ^ 4) - A ^ 5) / A ^ 5 := by
    field_simp
  rw [key, abs_div, abs_of_pos (by positivity : 0 < A ^ 5), div_le_iff₀ (by positivity)]
  -- N0 bound
  have hN0 := N0_eq d (s / d)
  simp only at hN0
  rw [show d * (s / d) = s by field_simp] at hN0
  have ht : s / d ∈ Set.Icc (0:ℝ) 1 := ⟨by positivity, by rw [div_le_one hd]; exact hsd⟩
  have hQ := hC d (s / d) ⟨hd.le, by linarith⟩ ht
  have hN0b : |(1 + a) ^ 2 * (B ^ 4 + s * B ^ 3 + 2 * s ^ 2 * B ^ 2 + 6 * s ^ 3 * B + 24 * s ^ 4) - B ^ 5|
      ≤ C * d ^ 3 := by
    rw [hBdef, he0, ha, hN0, abs_mul, abs_of_nonneg hd3, mul_comm]; gcongr
  -- difference bound
  have p2 := pow_diff A B 2 hA2 hB2
  have p3 := pow_diff A B 3 hA2 hB2
  have p4 := pow_diff A B 4 hA2 hB2
  have p5 := pow_diff A B 5 hA2 hB2
  norm_num at p2 p3 p4 p5
  rw [hAB] at p2 p3 p4 p5
  have hs1 : s ≤ 1 / 10 := by linarith
  have ha2 : (1 + a) ^ 2 ≤ 2 := by
    have : |a| ≤ 1 / 10 := by linarith
    rw [abs_le] at this
    nlinarith only [mul_nonneg (by linarith [this.2] : (0:ℝ) ≤ 1/10 - a) (by linarith [this.1] : (0:ℝ) ≤ a + 1/10)]
  have hS : |(A ^ 4 + s * A ^ 3 + 2 * s ^ 2 * A ^ 2 + 6 * s ^ 3 * A + 24 * s ^ 4)
      - (B ^ 4 + s * B ^ 3 + 2 * s ^ 2 * B ^ 2 + 6 * s ^ 3 * B + 24 * s ^ 4)| ≤ 36 * |e - e0| := by
    have e1 : (A ^ 4 + s * A ^ 3 + 2 * s ^ 2 * A ^ 2 + 6 * s ^ 3 * A + 24 * s ^ 4)
      - (B ^ 4 + s * B ^ 3 + 2 * s ^ 2 * B ^ 2 + 6 * s ^ 3 * B + 24 * s ^ 4)
      = (A ^ 4 - B ^ 4) + s * (A ^ 3 - B ^ 3) + 2 * s ^ 2 * (A ^ 2 - B ^ 2) + 6 * s ^ 3 * (A - B) := by ring
    rw [e1]
    have q1 : |s * (A ^ 3 - B ^ 3)| ≤ 2 * |e - e0| := by
      rw [abs_mul, abs_of_nonneg hs]
      nlinarith only [p3, hs, hs1, abs_nonneg (A ^ 3 - B ^ 3), abs_nonneg (e - e0)]
    have q2 : |2 * s ^ 2 * (A ^ 2 - B ^ 2)| ≤ 1 * |e - e0| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * s ^ 2)]
      have h2 : 2 * s ^ 2 ≤ 1 / 4 := by nlinarith only [hs, hs1]
      nlinarith only [p2, h2, abs_nonneg (A ^ 2 - B ^ 2), abs_nonneg (e - e0)]
    have q3 : |6 * s ^ 3 * (A - B)| ≤ 1 * |e - e0| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 6 * s ^ 3)]
      have : s ^ 3 ≤ (1/10) ^ 3 := pow_le_pow_left₀ hs hs1 3
      have : 6 * s ^ 3 ≤ 1 := by linarith
      rw [hAB]; nlinarith only [this, abs_nonneg (e - e0)]
    calc _ ≤ |A ^ 4 - B ^ 4| + |s * (A ^ 3 - B ^ 3)| + |2 * s ^ 2 * (A ^ 2 - B ^ 2)|
          + |6 * s ^ 3 * (A - B)| := by
          refine (abs_add_le _ _).trans ?_; gcongr
          refine (abs_add_le _ _).trans ?_; gcongr
          exact abs_add_le _ _
      _ ≤ 36 * |e - e0| := by
        linarith
  have hdiff : |((1 + a) ^ 2 * (A ^ 4 + s * A ^ 3 + 2 * s ^ 2 * A ^ 2 + 6 * s ^ 3 * A + 24 * s ^ 4) - A ^ 5)
      - ((1 + a) ^ 2 * (B ^ 4 + s * B ^ 3 + 2 * s ^ 2 * B ^ 2 + 6 * s ^ 3 * B + 24 * s ^ 4) - B ^ 5)|
      ≤ 160 * |e - e0| := by
    have e1 : ((1 + a) ^ 2 * (A ^ 4 + s * A ^ 3 + 2 * s ^ 2 * A ^ 2 + 6 * s ^ 3 * A + 24 * s ^ 4) - A ^ 5)
      - ((1 + a) ^ 2 * (B ^ 4 + s * B ^ 3 + 2 * s ^ 2 * B ^ 2 + 6 * s ^ 3 * B + 24 * s ^ 4) - B ^ 5)
      = (1 + a) ^ 2 * ((A ^ 4 + s * A ^ 3 + 2 * s ^ 2 * A ^ 2 + 6 * s ^ 3 * A + 24 * s ^ 4)
      - (B ^ 4 + s * B ^ 3 + 2 * s ^ 2 * B ^ 2 + 6 * s ^ 3 * B + 24 * s ^ 4)) - (A ^ 5 - B ^ 5) := by ring
    rw [e1]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [hS, ha2, p5, abs_nonneg (e - e0), sq_nonneg (1 + a), abs_nonneg ((A ^ 4 + s * A ^ 3 + 2 * s ^ 2 * A ^ 2 + 6 * s ^ 3 * A + 24 * s ^ 4)
      - (B ^ 4 + s * B ^ 3 + 2 * s ^ 2 * B ^ 2 + 6 * s ^ 3 * B + 24 * s ^ 4))]
  have hA5 : (1:ℝ) / 32 ≤ A ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num) hA 5; norm_num at this ⊢; linarith
  have tot : |(1 + a) ^ 2 * (A ^ 4 + s * A ^ 3 + 2 * s ^ 2 * A ^ 2 + 6 * s ^ 3 * A + 24 * s ^ 4) - A ^ 5|
      ≤ (C + 1000) * d ^ 3 := by
    have := abs_add_le (((1 + a) ^ 2 * (A ^ 4 + s * A ^ 3 + 2 * s ^ 2 * A ^ 2 + 6 * s ^ 3 * A + 24 * s ^ 4) - A ^ 5)
      - ((1 + a) ^ 2 * (B ^ 4 + s * B ^ 3 + 2 * s ^ 2 * B ^ 2 + 6 * s ^ 3 * B + 24 * s ^ 4) - B ^ 5))
      ((1 + a) ^ 2 * (B ^ 4 + s * B ^ 3 + 2 * s ^ 2 * B ^ 2 + 6 * s ^ 3 * B + 24 * s ^ 4) - B ^ 5)
    rw [sub_add_cancel] at this
    nlinarith only [this, hdiff, hN0b, hee, hd3]
  calc _ ≤ (C + 1000) * d ^ 3 := tot
    _ ≤ 32 * (C + 1000) * d ^ 3 * A ^ 5 := by
      have : 0 ≤ (C + 1000) * d ^ 3 := by positivity
      nlinarith only [this, hA5]

end LEI
end

-- ===== LE/G =====
section
namespace LEG
open Real Filter

noncomputable def alpha (l : ℝ) : ℝ := (log l - 1) / (2 * l) - (log l ^ 2 - 6 * log l + 9) / (8 * l ^ 2)

lemma log_small (l : ℝ) (hl : 400 ≤ l) : log l / l ≤ 1 / 10 := by
  have hl0 : 0 < l := by linarith
  have hs : 0 < √l := Real.sqrt_pos.2 hl0
  have h1 : log √l ≤ √l - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : log l = 2 * log √l := by rw [Real.log_sqrt hl0.le]; ring
  have h3 : 20 ≤ √l := by
    rw [show (20:ℝ) = √400 by rw [show (400:ℝ) = 20 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hl
  have h4 : √l * √l = l := Real.mul_self_sqrt hl0.le
  rw [div_le_iff₀ hl0]
  nlinarith

lemma log_ge_one (l : ℝ) (hl : 400 ≤ l) : 1 ≤ log l := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9; linarith

theorem G0_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, 400 ≤ l →
    |l * (1 + alpha l) ^ 2 * RPAux.f (l + log l + 2 * log (1 + alpha l)) - 1| ≤ C * (log l / l) ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := LEI.core
  refine ⟨C, hC0, fun l hl => ?_⟩
  have hl0 : 0 < l := by linarith
  have hu := log_ge_one l hl
  have hd1 := log_small l hl
  set d := log l / l with hd
  set s := 1 / l with hs
  have hdpos : 0 < d := by positivity
  have hs0 : 0 ≤ s := by positivity
  have hsd : s ≤ d := by rw [hs, hd]; gcongr
  have ha : alpha l = (d - s) / 2 - (d ^ 2 - 6 * d * s + 9 * s ^ 2) / 8 := by
    rw [alpha, hd, hs]; field_simp
  set a := alpha l with ha_def
  have hab : |a| ≤ d := by
    rw [ha, abs_le]; constructor <;> nlinarith [mul_nonneg hs0 hdpos.le, mul_nonneg hs0 hs0]
  have ha2 : |a| ≤ 1 / 10 := hab.trans hd1
  have hlog : |log (1 + a) - (a - a ^ 2 / 2)| ≤ 2 * d ^ 3 := by
    have h := Real.abs_log_sub_add_sum_range_le (x := -a) (by rw [abs_neg]; linarith) 2
    rw [abs_neg] at h
    have e1 : |log (1 + a) - (a - a ^ 2 / 2)| = |(∑ i ∈ Finset.range 2, (-a) ^ (i + 1) / (i + 1)) + log (1 - -a)| := by
      congr 1; simp [Finset.sum_range_succ]; ring
    rw [e1]
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : |a| ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hab 3
    have : d ^ 3 * |a| ≤ d ^ 3 * (1 / 10) := mul_le_mul_of_nonneg_left ha2 (by positivity)
    have : 0 ≤ d ^ 3 := by positivity
    norm_num; nlinarith
  have hcore := hC d s a (log (1 + a)) (d + 2 * s * log (1 + a)) hdpos hs0 hsd hd1 ha hlog rfl
  have hA : 0 < 1 + (d + 2 * s * log (1 + a)) := by
    have : |log (1 + a)| ≤ 1 := by
      have h1 : log (1 + a) ≤ a := by linarith [Real.log_le_sub_one_of_pos (by linarith [abs_le.1 ha2] : (0:ℝ) < 1 + a)]
      have h2 : -1 ≤ log (1 + a) := by
        have : (1:ℝ) / 2 ≤ 1 + a := by linarith [abs_le.1 ha2]
        have := Real.log_le_log (by norm_num) this
        have h3 : log (1/2 : ℝ) = - log 2 := by rw [one_div, Real.log_inv]
        linarith [Real.log_two_lt_d9]
      rw [abs_le]; constructor <;> linarith [abs_le.1 ha2]
    have : |2 * s * log (1 + a)| ≤ 2 * s := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * s)]; nlinarith [abs_nonneg (log (1 + a))]
    have : 2 * s ≤ 1 / 5 := by linarith
    linarith [abs_le.1 ‹|2 * s * log (1 + a)| ≤ 2 * s›]
  have hΛ : l + log l + 2 * log (1 + a) = l * (1 + (d + 2 * s * log (1 + a))) := by
    rw [hd, hs]; field_simp; ring
  rw [hΛ]
  convert hcore using 2
  set E := 1 + (d + 2 * s * log (1 + a))
  unfold RPAux.f
  rw [hs]
  field_simp

end LEG
end

-- ===== LE/M =====
section
namespace LEM
open Finset Real Filter Topology MeasureTheory

noncomputable def li (y : ℝ) : ℝ := ∫ t in (2:ℝ)..y, 1 / log t

lemma cont_inv_log (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn (fun t => 1 / log t) (Set.uIcc a b) := by
  have := RPAux.cont_pow 1 a b ha hab; simpa using this

lemma li_sub (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) : li b - li a = ∫ t in a..b, 1 / log t := by
  unfold li
  have i1 : IntervalIntegrable (fun t => 1 / log t) volume 2 a :=
    (cont_inv_log 2 a (by norm_num) ha).intervalIntegrable
  have i2 : IntervalIntegrable (fun t => 1 / log t) volume a b :=
    (cont_inv_log a b (by linarith) hab).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]; ring

lemma li_mono (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) : (b - a) / log b ≤ li b - li a := by
  rw [li_sub a b ha hab]
  have hb : 0 < log b := log_pos (by linarith)
  have : ∫ _ in a..b, 1 / log b = (b - a) / log b := by simp; ring
  rw [← this]
  apply intervalIntegral.integral_mono_on hab (by simp)
    ((cont_inv_log a b (by linarith) hab).intervalIntegrable)
  intro t ht
  have ht0 : 0 < log t := log_pos (by linarith [ht.1])
  exact one_div_le_one_div_of_le ht0 (log_le_log (by linarith [ht.1]) ht.2)

lemma J_eq (x : ℝ) (hx : 2 ≤ x) : LES.J x = li (x ^ 2) - li 4 := by
  have h4 : li (x ^ 2) - li 4 = ∫ t in (4:ℝ)..x ^ 2, 1 / log t := li_sub 4 (x ^ 2) (by norm_num) (by nlinarith)
  rw [h4, LES.J]
  have hsub := intervalIntegral.integral_comp_mul_deriv'' (a := 2) (b := x) (f := fun t => t ^ 2)
    (f' := fun t => 2 * t) (g := fun t => 1 / log t)
    (by fun_prop)
    (fun t _ => (hasDerivAt_pow 2 t).hasDerivWithinAt.congr_deriv (by ring))
    (by fun_prop)
    (by
      have hI : (fun t : ℝ => t ^ 2) '' Set.uIcc 2 x ⊆ Set.uIcc 4 (x ^ 2) := by
        rintro _ ⟨t, ht, rfl⟩
        rw [Set.uIcc_of_le hx] at ht
        rw [Set.uIcc_of_le (by nlinarith)]
        exact ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩
      exact (cont_inv_log 4 (x ^ 2) (by norm_num) (by nlinarith)).mono hI)
  have e4 : (2:ℝ) ^ 2 = 4 := by norm_num
  rw [e4] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hx] at ht
  have ht0 : 0 < t := by linarith [ht.1]
  simp only [Function.comp, Real.log_pow]
  have : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
  field_simp
  norm_num

lemma range_eq_Icc (N : ℕ) : Finset.range (N + 1) = Finset.Icc 0 N := by
  ext k; simp

lemma S0_eq (N : ℕ) : LGA.S0 N = ∑ p ∈ Icc 0 N with p.Prime, (p:ℝ) := by
  unfold LGA.S0 LGA.P; rw [range_eq_Icc]

lemma theta_floor (x : ℝ) : Chebyshev.theta (⌊x⌋₊ : ℝ) = Chebyshev.theta x := by
  unfold Chebyshev.theta; rw [Nat.floor_natCast]

/-- prime sum vs li(x²) -/
theorem S_li : ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ x : ℝ, 4 ≤ x →
    |LGA.S0 ⌊x⌋₊ - li (x ^ 2)| ≤ C * x ^ 2 / log x ^ 6 + K := by
  obtain ⟨C0, hC0, hθ⟩ := LET.theta_bound 6 (by norm_num)
  obtain ⟨C, hC, hS⟩ := LES.S0_bound 6 (by norm_num) C0 hC0 hθ
  refine ⟨C, |li 4| + 4 / log 2, hC, by positivity, fun x hx => ?_⟩
  have h := hS x hx
  rw [J_eq x (by linarith)] at h
  have : LGA.S0 ⌊x⌋₊ - li (x ^ 2) = ((∑ p ∈ Icc 0 ⌊x⌋₊ with p.Prime, (p:ℝ)) - (li (x ^ 2) - li 4) - 4 / log 2)
    + (4 / log 2 - li 4) := by rw [S0_eq]; ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  have h2 : |4 / log 2 - li 4| ≤ |li 4| + 4 / log 2 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (by positivity)]; linarith
  linarith

end LEM
end

-- ===== LE/F =====
section
namespace LEF
open Finset Real Filter Topology

lemma logw (x w : ℝ) (hx : 1 ≤ x) (hl : 400 ≤ log x) (hw : √x / 4 ≤ w) : log x / 4 ≤ log w := by
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have h1 : log (√x / 4) = log x / 2 - log 4 := by
    rw [Real.log_div hs.ne' (by norm_num), Real.log_sqrt (by linarith)]
  have h4 : log 4 < 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; have := Real.log_two_lt_d9; push_cast; linarith
  have := Real.log_le_log (by positivity) hw
  linarith

lemma inv_pow_le (l : ℝ) (hl : 400 ≤ l) (k : ℕ) (hk : 3 ≤ k) : 1 / l ^ k ≤ (log l / l) ^ 3 := by
  have hl0 : 0 < l := by linarith
  have hu := LEG.log_ge_one l hl
  rw [div_pow]
  have h1 : 1 / l ^ k ≤ 1 / l ^ 3 := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by linarith) hk
  refine h1.trans ?_
  gcongr
  exact one_le_pow₀ hu

/-- bound `c / log w ^ 6 ≤ 4096 c d^3` for `w ≥ √x/4` -/
lemma log6 (x w : ℝ) (hx : 1 ≤ x) (hl : 400 ≤ log x) (hw : √x / 4 ≤ w) :
    1 / log w ^ 6 ≤ 4096 / log x ^ 6 := by
  have h := logw x w hx hl hw
  have hl0 : 0 < log x := by linarith
  have : 1 / log w ^ 6 ≤ 1 / (log x / 4) ^ 6 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) h 6)
  refine this.trans ?_
  have e : 1 / (log x / 4) ^ 6 = 4096 * (1 / log x ^ 6) := by field_simp; norm_num
  rw [e]; apply le_of_eq; ring

lemma small_ev : ∀ᶠ w : ℝ in atTop, (√w + 1) * log w ≤ w / log w ^ 6 := by
  have h1 := (isLittleO_log_rpow_rpow_atTop 7 (by norm_num : (0:ℝ) < 1 / 2)).bound
    (c := 1 / 2) (by norm_num)
  filter_upwards [h1, eventually_ge_atTop (Real.exp 1)] with w hw hw1
  have hw0 : 0 < w := lt_of_lt_of_le (Real.exp_pos 1) hw1
  have hlw : 1 ≤ log w := by rwa [Real.le_log_iff_exp_le hw0]
  have hs1 : 1 ≤ √w := by
    rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp 1])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), ← Real.sqrt_eq_rpow] at hw
  have e7 : log w ^ (7:ℝ) = log w ^ 7 := by norm_cast
  rw [e7] at hw
  have hl6 : 0 < log w ^ 6 := by positivity
  rw [le_div_iff₀ hl6]
  have hsw : √w * √w = w := Real.mul_self_sqrt hw0.le
  calc (√w + 1) * log w * log w ^ 6 ≤ 2 * √w * log w ^ 7 := by
        have : 0 ≤ log w ^ 7 := by positivity
        nlinarith
    _ ≤ 2 * √w * (1 / 2 * √w) := by gcongr
    _ = w := by linear_combination hsw

lemma alpha_abs (l : ℝ) (hl : 400 ≤ l) : |LEG.alpha l| ≤ log l / l := by
  have hl0 : 0 < l := by linarith
  have hu := LEG.log_ge_one l hl
  have hd1 := LEG.log_small l hl
  set d := log l / l with hd
  set s := 1 / l with hs
  have hdpos : 0 < d := by positivity
  have hs0 : 0 ≤ s := by positivity
  have hsd : s ≤ d := by rw [hs, hd]; gcongr
  have ha : LEG.alpha l = (d - s) / 2 - (d ^ 2 - 6 * d * s + 9 * s ^ 2) / 8 := by
    rw [LEG.alpha, hd, hs]; field_simp
  rw [ha, abs_le]; constructor <;> nlinarith [mul_nonneg hs0 hdpos.le, mul_nonneg hs0 hs0]


set_option maxHeartbeats 4000000 in
open LandauFunction in
theorem pointwise (CG K1 CS KS Cθ X1 X2 : ℝ) (hCG : 0 ≤ CG) (hK1 : 0 ≤ K1) (hCS : 0 ≤ CS) (hCθ : 0 ≤ Cθ)
    (hG : ∀ l : ℝ, 400 ≤ l →
      |l * (1 + LEG.alpha l) ^ 2 * RPAux.f (l + log l + 2 * log (1 + LEG.alpha l)) - 1| ≤ CG * (log l / l) ^ 3)
    (hli : ∀ x : ℝ, X1 ≤ x → |LEM.li x - x * RPAux.f (log x)| ≤ K1 * x / log x ^ 6)
    (hS : ∀ x : ℝ, 4 ≤ x → |LGA.S0 ⌊x⌋₊ - LEM.li (x ^ 2)| ≤ CS * x ^ 2 / log x ^ 6 + KS)
    (hθ : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ Cθ * x / log x ^ 6)
    (hsm : ∀ w : ℝ, X2 ≤ w → (√w + 1) * log w ≤ w / log w ^ 6)
    (n : ℕ) (h1 : 400 ≤ log (n:ℝ))
    (h2 : 4 * (CG + 5 * K1 + (5 * 4096 * CS + 1) + 1) * (log (log (n:ℝ)) / log n) ^ 3 ≤ 1 / 2)
    (h3 : KS ≤ n * (log (log (n:ℝ)) / log n) ^ 3) (h4 : X1 ≤ n) (h5 : max X2 5 ≤ √(n:ℝ) / 4) :
    |log (landau n) - √(n * log n) * (1 + LEG.alpha (log n))|
      ≤ 2 * (4 * (CG + 5 * K1 + (5 * 4096 * CS + 1) + 1) + 8192 * Cθ + 8192)
        * (√(n * log n) * (log (log (n:ℝ)) / log n) ^ 3) := by
  set x : ℝ := (n:ℝ) with hxdef
  set l := log x with hldef
  set d := log l / l with hddef
  set a := LEG.alpha l with hadef
  set C1 := CG + 5 * K1 with hC1
  set C3 := 5 * 4096 * CS + 1 with hC3
  set K := 4 * (C1 + C3 + 1) with hKdef
  clear_value K C3 C1 a d l x
  have hl0 : 0 < l := by linarith
  have hx1 : 1 < x := by
    by_contra hc; push_neg at hc
    have := Real.log_nonpos (by rw [hxdef]; positivity : (0:ℝ) ≤ x) hc; linarith
  have hx0 : 0 < x := by linarith
  have hu := LEG.log_ge_one l h1
  have hd1 := LEG.log_small l h1
  have hd0 : 0 < d := by rw [hddef]; exact div_pos (by linarith) hl0
  have hd3 : 0 ≤ d ^ 3 := pow_nonneg hd0.le 3
  have hab := alpha_abs l h1
  rw [← hddef] at hab
  have ha1 : 9 / 10 ≤ 1 + a := by linarith [abs_le.1 hab]
  have ha2 : 1 + a ≤ 11 / 10 := by linarith [abs_le.1 hab]
  have hK0 : 0 ≤ K := by rw [hKdef, hC1, hC3]; positivity
  have hKd : K * d ^ 3 ≤ 1 / 2 := h2
  set F := √(x * l) * (1 + a) with hFdef
  clear_value F
  have hsxl : √x ≤ √(x * l) := Real.sqrt_le_sqrt (by nlinarith)
  have hsx0 : 0 < √x := Real.sqrt_pos.2 hx0
  have hF0 : 0 < F := by rw [hFdef]; exact mul_pos (Real.sqrt_pos.2 (mul_pos hx0 hl0)) (by linarith)
  have hF2 : F ^ 2 = x * l * (1 + a) ^ 2 := by
    rw [hFdef, mul_pow, Real.sq_sqrt (mul_pos hx0 hl0).le]
  have hFlo : 9 / 10 * √x ≤ F := by
    rw [hFdef]; have := mul_le_mul hsxl ha1 (by norm_num) (Real.sqrt_nonneg _); linarith
  have hFhi : F ≤ 11 / 10 * √(x * l) := by
    rw [hFdef]; have := mul_le_mul_of_nonneg_left ha2 (Real.sqrt_nonneg (x * l)); linarith
  have hxl0 : 0 < x * l := mul_pos hx0 hl0
  have hxl : 400 ≤ x * l := by nlinarith only [hx1, h1]
  have hsq1 : (81 / 100 : ℝ) ≤ (1 + a) ^ 2 := by nlinarith only [ha1]
  have hsq2 : (1 + a) ^ 2 ≤ 5 / 4 := by nlinarith only [ha1, ha2]
  have hF2lo : 81 / 100 * (x * l) ≤ F ^ 2 := by
    rw [hF2]; have := mul_le_mul_of_nonneg_left hsq1 hxl0.le; linarith
  have hF2hi : F ^ 2 ≤ 5 / 4 * (x * l) := by
    rw [hF2]; have := mul_le_mul_of_nonneg_left hsq2 hxl0.le; linarith
  have hw5 : ∀ w : ℝ, 0 ≤ w → w ≤ 2 * F → w ^ 2 ≤ 5 * (x * l) := by
    intro w hw0 hw2
    have := pow_le_pow_left₀ hw0 hw2 2
    nlinarith only [this, hF2hi]
  -- logs
  have hlogF2 : log (F ^ 2) = l + log l + 2 * log (1 + a) := by
    rw [hF2, Real.log_mul (mul_pos hx0 hl0).ne' (pow_pos (by linarith) 2).ne', Real.log_mul hx0.ne' hl0.ne',
      Real.log_pow]; push_cast; linarith
  have hlog1a : -1 / 2 ≤ log (1 + a) := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0:ℝ) < 1 + a)
    have : (1 + a)⁻¹ ≤ 10 / 9 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hlog1a' : log (1 + a) ≤ 1 / 10 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + a); linarith
  have hll : log l ≤ l / 10 := by rw [div_le_iff₀ hl0] at hd1; linarith
  have hlog5 : log 5 < 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5 / 4)
    rw [show (5:ℝ) = 5 / 4 * 4 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  have hbig : ∀ y : ℝ, 0 < y → y ≤ 5 * (x * l) → log y ≤ 2 * l := by
    intro y hy hyl
    have := Real.log_le_log hy hyl
    rw [Real.log_mul (by norm_num) (mul_pos hx0 hl0).ne', Real.log_mul hx0.ne' hl0.ne'] at this
    linarith
  have hlogF2lo : l ≤ log (F ^ 2) := by rw [hlogF2]; linarith
  have hlogF2hi : log (F ^ 2) ≤ 2 * l := hbig _ (pow_pos hF0 2) (by linarith)
  have hinv5 := inv_pow_le l h1 5 (by norm_num)
  have hinv6 := inv_pow_le l h1 6 (by norm_num)
  rw [← hddef] at hinv5 hinv6
  -- (A) li(F²) ≈ x
  have hA : |LEM.li (F ^ 2) - x| ≤ C1 * x * d ^ 3 := by
    have hg := hG l h1
    rw [← hadef, ← hddef] at hg
    have e1 : F ^ 2 * RPAux.f (log (F ^ 2)) - x = x * (l * (1 + a) ^ 2 * RPAux.f (l + log l + 2 * log (1 + a)) - 1) := by
      rw [hlogF2, hF2]; ring
    have hgx : |F ^ 2 * RPAux.f (log (F ^ 2)) - x| ≤ CG * x * d ^ 3 := by
      rw [e1, abs_mul, abs_of_pos hx0]
      have := mul_le_mul_of_nonneg_left hg hx0.le; linarith
    have hX1 : X1 ≤ F ^ 2 := by nlinarith only [h4, hF2lo, h1, hx0]
    have hl1 := hli (F ^ 2) hX1
    have hl2 : K1 * F ^ 2 / log (F ^ 2) ^ 6 ≤ 5 * K1 * x * d ^ 3 := by
      have : 1 / log (F ^ 2) ^ 6 ≤ 1 / l ^ 6 :=
        one_div_le_one_div_of_le (pow_pos hl0 6) (pow_le_pow_left₀ hl0.le hlogF2lo 6)
      have e : K1 * F ^ 2 / log (F ^ 2) ^ 6 = K1 * F ^ 2 * (1 / log (F ^ 2) ^ 6) := by ring
      rw [e]
      calc K1 * F ^ 2 * (1 / log (F ^ 2) ^ 6) ≤ K1 * (5 / 4 * (x * l)) * (1 / l ^ 6) := by gcongr
        _ = 5 / 4 * K1 * x * (1 / l ^ 5) := by field_simp
        _ ≤ 5 / 4 * K1 * x * d ^ 3 := by gcongr
        _ ≤ 5 * K1 * x * d ^ 3 := by linarith [mul_nonneg (mul_nonneg hK1 hx0.le) hd3]
    have := abs_sub_le (LEM.li (F ^ 2)) (F ^ 2 * RPAux.f (log (F ^ 2))) x
    rw [hC1]; linarith
  clear hG hli hlogF2 hlog1a hlog1a' hll hlog5 hsq1 hsq2 hab hd1 hlogF2lo
  -- w±
  set wp := F * (1 + K * d ^ 3) with hwp
  set wm := F * (1 - K * d ^ 3) with hwm
  clear_value wp wm
  have hFk0 := mul_nonneg hF0.le (mul_nonneg hK0 hd3)
  have hFk1 := mul_le_mul_of_nonneg_left hKd hF0.le
  have hwp_lo : F ≤ wp := by rw [hwp]; linarith
  have hwp_hi : wp ≤ 2 * F := by rw [hwp]; linarith
  have hwm_lo : F / 2 ≤ wm := by rw [hwm]; linarith
  have hwm_hi : wm ≤ F := by rw [hwm]; linarith
  have h5a : 5 ≤ √x / 4 := le_trans (le_max_right _ _) h5
  have h5b : X2 ≤ √x / 4 := le_trans (le_max_left _ _) h5
  have hwp4 : √x / 4 ≤ wp := by linarith
  have hwm4 : √x / 4 ≤ wm := by linarith
  -- S bounds at w
  have hSw : ∀ w : ℝ, √x / 4 ≤ w → w ≤ 2 * F → |LGA.S0 ⌊w⌋₊ - LEM.li (w ^ 2)| ≤ C3 * x * d ^ 3 := by
    intro w hw1 hw2
    have h := hS w (by linarith)
    have hl6 := log6 x w hx1.le (by rw [← hldef]; exact h1) hw1
    rw [← hldef] at hl6
    have hw2' : w ^ 2 ≤ 5 * (x * l) := hw5 w (by linarith) hw2
    have : CS * w ^ 2 / log w ^ 6 ≤ 5 * 4096 * CS * x * d ^ 3 := by
      have e : CS * w ^ 2 / log w ^ 6 = CS * w ^ 2 * (1 / log w ^ 6) := by ring
      rw [e]
      calc CS * w ^ 2 * (1 / log w ^ 6) ≤ CS * (5 * (x * l)) * (4096 / l ^ 6) := by gcongr
        _ = 5 * 4096 * CS * x * (1 / l ^ 5) := by field_simp
        _ ≤ 5 * 4096 * CS * x * d ^ 3 := by gcongr
    rw [hC3]; linarith
  have hSp := hSw wp hwp4 hwp_hi
  have hSm := hSw wm hwm4 (by linarith)
  -- monotonicity of li
  have hmp : K / 2 * x * d ^ 3 ≤ LEM.li (wp ^ 2) - LEM.li (F ^ 2) := by
    have hFF : 2 ≤ F ^ 2 := by linarith
    have hle : F ^ 2 ≤ wp ^ 2 := pow_le_pow_left₀ hF0.le hwp_lo 2
    have h := LEM.li_mono (F ^ 2) (wp ^ 2) hFF hle
    have hlw : log (wp ^ 2) ≤ 2 * l := hbig _ (pow_pos (by linarith) 2) (hw5 wp (by linarith) hwp_hi)
    have hlw0 : 0 < log (wp ^ 2) := Real.log_pos (by nlinarith only [hwp4, h5a])
    have hdiff : 2 * K * d ^ 3 * F ^ 2 ≤ wp ^ 2 - F ^ 2 := by
      rw [hwp]; nlinarith only [mul_nonneg (sq_nonneg F) (sq_nonneg (K * d ^ 3))]
    have h0 : 0 ≤ 2 * K * d ^ 3 * F ^ 2 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) hd3) (sq_nonneg F)
    have : 2 * K * d ^ 3 * F ^ 2 / (2 * l) ≤ (wp ^ 2 - F ^ 2) / log (wp ^ 2) := by
      apply div_le_div₀ (h0.trans hdiff) hdiff hlw0 hlw
    have e : 2 * K * d ^ 3 * F ^ 2 / (2 * l) = K * d ^ 3 * (F ^ 2 / l) := by field_simp
    have hFl : 81 / 100 * x ≤ F ^ 2 / l := by rw [le_div_iff₀ hl0]; linarith
    have : K * d ^ 3 * (81 / 100 * x) ≤ K * d ^ 3 * (F ^ 2 / l) := by gcongr
    linarith [mul_nonneg (mul_nonneg hK0 hd3) hx0.le]
  have hmm : K / 4 * x * d ^ 3 ≤ LEM.li (F ^ 2) - LEM.li (wm ^ 2) := by
    have hww : 2 ≤ wm ^ 2 := by nlinarith only [hwm4, h5a]
    have hle : wm ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ (by linarith) hwm_hi 2
    have h := LEM.li_mono (wm ^ 2) (F ^ 2) hww hle
    have hlw0 : 0 < log (F ^ 2) := Real.log_pos (by linarith only [hF2lo, hxl])
    have hdiff : K * d ^ 3 * F ^ 2 ≤ F ^ 2 - wm ^ 2 := by
      rw [hwm]
      have := mul_le_mul_of_nonneg_left hKd (mul_nonneg (mul_nonneg hK0 hd3) (sq_nonneg F))
      nlinarith only [this]
    have h0 : 0 ≤ K * d ^ 3 * F ^ 2 := mul_nonneg (mul_nonneg hK0 hd3) (sq_nonneg F)
    have : K * d ^ 3 * F ^ 2 / (2 * l) ≤ (F ^ 2 - wm ^ 2) / log (F ^ 2) := by
      apply div_le_div₀ (h0.trans hdiff) hdiff hlw0 hlogF2hi
    have e : K * d ^ 3 * F ^ 2 / (2 * l) = K * d ^ 3 * (F ^ 2 / l) / 2 := by field_simp
    have hFl : 81 / 100 * x ≤ F ^ 2 / l := by rw [le_div_iff₀ hl0]; linarith
    have : K * d ^ 3 * (81 / 100 * x) ≤ K * d ^ 3 * (F ^ 2 / l) := by gcongr
    linarith [mul_nonneg (mul_nonneg hK0 hd3) hx0.le]
  have hSp_ge : x ≤ LGA.S0 ⌊wp⌋₊ := by
    have := abs_le.1 hSp; have := abs_le.1 hA
    have hxd : 0 ≤ x * d ^ 3 := mul_nonneg hx0.le hd3
    have hC1n : 0 ≤ C1 := by rw [hC1]; positivity
    have hC3n : 0 ≤ C3 := by rw [hC3]; positivity
    have := mul_nonneg hC1n hxd
    have := mul_nonneg hC3n hxd
    rw [hKdef] at hmp hmm
    linarith
  have hSm_le : LGA.S0 ⌊wm⌋₊ ≤ x := by
    have := abs_le.1 hSm; have := abs_le.1 hA
    have hxd : 0 ≤ x * d ^ 3 := mul_nonneg hx0.le hd3
    have hC1n : 0 ≤ C1 := by rw [hC1]; positivity
    have hC3n : 0 ≤ C3 := by rw [hC3]; positivity
    have := mul_nonneg hC1n hxd
    have := mul_nonneg hC3n hxd
    rw [hKdef] at hmp hmm
    linarith
  clear hSw hSp hSm hmp hmm hA hS hlogF2hi hw5 hbig hinv5
  -- theta bounds
  have hθw : ∀ w : ℝ, √x / 4 ≤ w → |Chebyshev.theta w - w| ≤ 4096 * Cθ * w * d ^ 3 := by
    intro w hw
    have h := hθ w (by linarith)
    have hl6 := log6 x w hx1.le (by rw [← hldef]; exact h1) hw
    rw [← hldef] at hl6
    have hw0 : 0 ≤ w := by linarith
    have : Cθ * w / log w ^ 6 ≤ 4096 * Cθ * w * d ^ 3 := by
      have e : Cθ * w / log w ^ 6 = Cθ * w * (1 / log w ^ 6) := by ring
      rw [e]
      calc Cθ * w * (1 / log w ^ 6) ≤ Cθ * w * (4096 / l ^ 6) := by gcongr
        _ = 4096 * Cθ * w * (1 / l ^ 6) := by ring
        _ ≤ 4096 * Cθ * w * d ^ 3 := by gcongr
    linarith
  -- lower bound
  have hlower : F - (K + 4096 * Cθ) * F * d ^ 3 ≤ log (landau n) := by
    set N := ⌊wm⌋₊
    have hsum : ∑ p ∈ LGA.P N, p ≤ n := by
      have : ((∑ p ∈ LGA.P N, p : ℕ) : ℝ) = LGA.S0 N := by unfold LGA.S0; push_cast; rfl
      have h' : LGA.S0 N ≤ (n:ℝ) := by rw [← hxdef]; exact hSm_le
      rw [← this] at h'
      exact_mod_cast h'
    have hlo := LGB.lower n N hsum
    rw [LGA.th_eq, LEM.theta_floor] at hlo
    have := abs_le.1 (hθw wm hwm4)
    have h4096 : 4096 * Cθ * wm * d ^ 3 ≤ 4096 * Cθ * F * d ^ 3 := by gcongr
    linarith
  -- upper bound
  have hupper : log (landau n) ≤ F + (K + 8192 * Cθ + 8192) * F * d ^ 3 := by
    set M := ⌊wp⌋₊ with hM
    have hM5 : (5:ℝ) ≤ M := by
      have : (5:ℕ) ≤ M := Nat.le_floor (by push_cast; linarith)
      exact_mod_cast this
    have hM4 : 4 ≤ M := by exact_mod_cast (by linarith : (4:ℝ) ≤ M)
    have hup := LEU.landau_upper n M hM4
    rw [LGA.th_eq, LEM.theta_floor] at hup
    have hMw : (M:ℝ) ≤ wp := Nat.floor_le (by linarith)
    have hlM : 0 ≤ log (M:ℝ) := Real.log_nonneg (by linarith)
    have hlam : -(log M / M * LGA.S0 M) + x * log M / M ≤ 0 := by
      have : x * log M / M = log M / M * x := by ring
      rw [this]
      have : 0 ≤ log M / M := div_nonneg hlM (by linarith)
      have := mul_le_mul_of_nonneg_left hSp_ge this
      linarith
    have hsq : ((Nat.sqrt M : ℕ) : ℝ) + 1 ≤ √wp + 1 := by
      have := Real.nat_sqrt_le_real_sqrt (a := M)
      have := Real.sqrt_le_sqrt hMw
      linarith
    have hlogM : log (M:ℝ) ≤ log wp := Real.log_le_log (by linarith) hMw
    have hsm' := hsm wp (by linarith)
    have hrem : ((Nat.sqrt M : ℕ) + 1 : ℝ) * log M ≤ wp / log wp ^ 6 := by
      calc ((Nat.sqrt M : ℕ) + 1 : ℝ) * log M ≤ (√wp + 1) * log wp := by
            apply mul_le_mul hsq hlogM hlM (by linarith [Real.sqrt_nonneg wp])
        _ ≤ _ := hsm'
    have hl6 := log6 x wp hx1.le (by rw [← hldef]; exact h1) hwp4
    rw [← hldef] at hl6
    have hrem2 : wp / log wp ^ 6 ≤ 8192 * F * d ^ 3 := by
      have e : wp / log wp ^ 6 = wp * (1 / log wp ^ 6) := by ring
      rw [e]
      calc wp * (1 / log wp ^ 6) ≤ (2 * F) * (4096 / l ^ 6) := by
            apply mul_le_mul hwp_hi hl6 (one_div_nonneg.2 (pow_nonneg (Real.log_nonneg (by linarith)) 6)) (by linarith)
        _ = 8192 * F * (1 / l ^ 6) := by ring
        _ ≤ 8192 * F * d ^ 3 := by gcongr
    have hθp := abs_le.1 (hθw wp hwp4)
    have h4096 : 4096 * Cθ * wp * d ^ 3 ≤ 4096 * Cθ * (2 * F) * d ^ 3 := by gcongr
    have e : (Nat.sqrt M + 1 : ℝ) * log M = ((Nat.sqrt M : ℕ) + 1 : ℝ) * log M := rfl
    have hxn : (n:ℝ) = x := hxdef.symm
    rw [hxn] at hup
    linarith
  -- combine
  have hfin : |log (landau n) - F| ≤ (K + 8192 * Cθ + 8192) * F * d ^ 3 := by
    rw [abs_le]; constructor
    · have : (K + 4096 * Cθ) * F * d ^ 3 ≤ (K + 8192 * Cθ + 8192) * F * d ^ 3 := by
        have : 0 ≤ Cθ * F * d ^ 3 := mul_nonneg (mul_nonneg hCθ hF0.le) hd3
        have : 0 ≤ F * d ^ 3 := mul_nonneg hF0.le hd3
        linarith
      linarith
    · linarith
  refine hfin.trans ?_
  have hc : 0 ≤ K + 8192 * Cθ + 8192 := by linarith
  calc (K + 8192 * Cθ + 8192) * F * d ^ 3 ≤ (K + 8192 * Cθ + 8192) * (11 / 10 * √(x * l)) * d ^ 3 := by gcongr
    _ ≤ 2 * (K + 8192 * Cθ + 8192) * (√(x * l) * d ^ 3) := by
      have : 0 ≤ (K + 8192 * Cθ + 8192) * (√(x * l) * d ^ 3) := mul_nonneg hc (mul_nonneg (Real.sqrt_nonneg _) hd3)
      linarith

end LEF
end

-- ===== LE/Main =====
open Finset Real Filter Topology LandauFunction

theorem solution :
    (fun n : ℕ => Real.log (landau n) - Real.sqrt (n * Real.log n) *
        (1 + (Real.log (Real.log n) - 1) / (2 * Real.log n)
          - (Real.log (Real.log n) ^ 2 - 6 * Real.log (Real.log n) + 9) / (8 * Real.log n ^ 2)))
      =O[Filter.atTop]
      (fun n : ℕ => Real.sqrt (n * Real.log n) * (Real.log (Real.log n) / Real.log n) ^ 3) := by
  obtain ⟨CG, hCG, hG⟩ := LEG.G0_bound
  obtain ⟨K1, hK1, hli⟩ := RPAux.li_bound
  obtain ⟨X1, hX1⟩ := eventually_atTop.1 hli
  obtain ⟨CS, KS, hCS, hKS, hS⟩ := LEM.S_li
  obtain ⟨Cθ, hCθ, hθ⟩ := LET.theta_bound 6 (by norm_num)
  obtain ⟨X2, hX2⟩ := eventually_atTop.1 LEF.small_ev
  set K' := 4 * (CG + 5 * K1 + (5 * 4096 * CS + 1) + 1) with hK'
  have hlogn : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- d → 0
  have hd : Tendsto (fun l : ℝ => K' * (log l / l) ^ 3) atTop (𝓝 0) := by
    have h0 : Tendsto (fun l : ℝ => log l / l) atTop (𝓝 0) := by
      have := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
      simpa using this
    have := (h0.pow 3).const_mul K'
    simpa using this
  have E2 : ∀ᶠ n : ℕ in atTop, K' * (log (log (n:ℝ)) / log n) ^ 3 ≤ 1 / 2 :=
    hlogn.eventually (hd.eventually (ge_mem_nhds (by norm_num)))
  have E1 : ∀ᶠ n : ℕ in atTop, (400:ℝ) ≤ log (n:ℝ) := hlogn.eventually (eventually_ge_atTop 400)
  have E3 : ∀ᶠ n : ℕ in atTop, KS * log (n:ℝ) ^ 3 ≤ n := by
    have hb := (isLittleO_pow_log_id_atTop (n := 3)).bound (c := 1 / (KS + 1)) (by positivity)
    refine (tendsto_natCast_atTop_atTop.eventually (hb.and (eventually_ge_atTop 1))).mono ?_
    intro n ⟨hn, hn1⟩
    simp only [Real.norm_eq_abs, id] at hn
    rw [Nat.abs_cast] at hn
    have : KS * log (n:ℝ) ^ 3 ≤ KS * (1 / (KS + 1) * n) := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hn) hKS
    have e : KS * (1 / (KS + 1) * (n:ℝ)) = KS / (KS + 1) * n := by ring
    have : KS / (KS + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  have E4 : ∀ᶠ n : ℕ in atTop, X1 ≤ (n:ℝ) := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop X1)
  have E5 : ∀ᶠ n : ℕ in atTop, max X2 5 ≤ √(n:ℝ) / 4 := by
    have : Tendsto (fun n : ℕ => √(n:ℝ) / 4) atTop atTop :=
      (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
    exact this.eventually (eventually_ge_atTop _)
  refine Asymptotics.IsBigO.of_bound (2 * (K' + 8192 * Cθ + 8192)) ?_
  filter_upwards [E1, E2, E3, E4, E5] with n h1 h2 h3 h4 h5
  have hl0 : 0 < log (n:ℝ) := by linarith
  have hu := LEG.log_ge_one _ h1
  have h3' : KS ≤ n * (log (log (n:ℝ)) / log n) ^ 3 := by
    have hd1 : 1 / log (n:ℝ) ≤ log (log (n:ℝ)) / log n := by gcongr
    have : (1 / log (n:ℝ)) ^ 3 ≤ (log (log (n:ℝ)) / log n) ^ 3 := pow_le_pow_left₀ (by positivity) hd1 3
    have e : KS = KS * log (n:ℝ) ^ 3 * (1 / log (n:ℝ)) ^ 3 := by field_simp
    rw [e]
    calc KS * log (n:ℝ) ^ 3 * (1 / log (n:ℝ)) ^ 3 ≤ n * (1 / log (n:ℝ)) ^ 3 := by gcongr
      _ ≤ _ := by gcongr
  have hp := LEF.pointwise CG K1 CS KS Cθ X1 X2 hCG hK1 hCS hCθ hG
    (fun x hx => by have := hX1 x hx; unfold LEM.li; exact this) hS hθ hX2 n h1 h2 h3' h4 h5
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hnn : 0 ≤ √((n:ℝ) * log n) * (log (log (n:ℝ)) / log n) ^ 3 := by
    have : 0 ≤ log (log (n:ℝ)) := by linarith
    positivity
  rw [abs_of_nonneg hnn]
  have e : (1 + (log (log (n:ℝ)) - 1) / (2 * log n) - (log (log (n:ℝ)) ^ 2 - 6 * log (log n) + 9) / (8 * log n ^ 2))
      = 1 + LEG.alpha (log n) := by unfold LEG.alpha; ring
  rw [e]
  exact hp
