-- Prove2me | solution 1 for LandauFunction.landau_log_eq_sqrt_logIntegralInv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T06:45:20.828975+00:00
-- url     : https://prove2.me/submissions/32fd3b74-027c-4d83-8fbe-a08839b5889f

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_psi_prime_number_theorem
import Definitions.Def_LandauFunction_landau
import Definitions.Def_LandauFunction_logIntegral

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

-- ===== LI/E =====
section

namespace LIE
open Real Filter Topology

noncomputable def E (c x : ℝ) : ℝ :=
  Real.exp (-c * Real.log x ^ ((3 : ℝ) / 5) * Real.log (Real.log x) ^ (-(1 : ℝ) / 5))

noncomputable def ψ (L : ℝ) : ℝ := L ^ ((3 : ℝ) / 5) * Real.log L ^ (-(1 : ℝ) / 5)

lemma E_eq (c x : ℝ) : E c x = Real.exp (-(c * ψ (Real.log x))) := by
  unfold E ψ; ring_nf

lemma E_pos (c x : ℝ) : 0 < E c x := Real.exp_pos _

lemma psi_eq (L : ℝ) (hL : 1 < L) :
    ψ L = Real.exp (3 / 5 * Real.log L - 1 / 5 * Real.log (Real.log L)) := by
  unfold ψ
  rw [rpow_def_of_pos (by linarith), rpow_def_of_pos (log_pos hL), ← Real.exp_add]; ring_nf

lemma psi_nonneg (L : ℝ) (hL : 1 < L) : 0 ≤ ψ L := by
  rw [psi_eq L hL]; exact (Real.exp_pos _).le

lemma psi_mono (L L' : ℝ) (hL : Real.exp 1 ≤ L) (h : L ≤ L') : ψ L ≤ ψ L' := by
  have h1 : 1 < L := lt_of_lt_of_le (by have := Real.add_one_le_exp 1; linarith) hL
  have hl1 : 1 ≤ Real.log L := by rwa [Real.le_log_iff_exp_le (by linarith)]
  have hl1' : Real.log L ≤ Real.log L' := Real.log_le_log (by linarith) h
  rw [psi_eq L h1, psi_eq L' (by linarith)]
  apply Real.exp_le_exp.2
  have hp1 : 0 < Real.log L := by linarith
  have hp2 : 0 < Real.log L' := by linarith
  have hq := Real.log_le_sub_one_of_pos (x := Real.log L' / Real.log L) (div_pos hp2 hp1)
  rw [Real.log_div hp2.ne' hp1.ne'] at hq
  have : Real.log L' / Real.log L - 1 ≤ Real.log L' - Real.log L := by
    rw [div_sub_one hp1.ne', div_le_iff₀ hp1]
    nlinarith
  linarith

lemma psi_le (L : ℝ) (hL : Real.exp 1 ≤ L) : ψ L ≤ L ^ ((3 : ℝ) / 5) := by
  have h1 : 1 < L := lt_of_lt_of_le (by have := Real.add_one_le_exp 1; linarith) hL
  have hl1 : 1 ≤ Real.log L := by rwa [Real.le_log_iff_exp_le (by linarith)]
  unfold ψ
  have : Real.log L ^ (-(1 : ℝ) / 5) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hl1 (by norm_num)
  have h0 : 0 ≤ L ^ ((3 : ℝ) / 5) := by positivity
  nlinarith

lemma psi_diff (c : ℝ) (hc : 0 < c) : ∃ L0, ∀ L L', L0 ≤ L → L ≤ L' → c * (ψ L' - ψ L) ≤ L' - L := by
  have ht : Tendsto (fun L : ℝ => L ^ ((2 : ℝ) / 5)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  obtain ⟨L1, hL1⟩ := eventually_atTop.1 (ht.eventually (eventually_ge_atTop c))
  refine ⟨max L1 (Real.exp 1), fun L L' hL h => ?_⟩
  have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have h1 : 1 < L := lt_of_lt_of_le (by have := Real.add_one_le_exp 1; linarith) hLe
  have hl1 : 1 ≤ Real.log L := by rwa [Real.le_log_iff_exp_le (by linarith)]
  have hl1' : Real.log L ≤ Real.log L' := Real.log_le_log (by linarith) h
  have hcL : c ≤ L ^ ((2 : ℝ) / 5) := hL1 L (le_trans (le_max_left _ _) hL)
  -- ψ L' ≤ L'^{3/5} λ^{-1/5}
  have hA : ψ L' ≤ L' ^ ((3 : ℝ) / 5) * Real.log L ^ (-(1 : ℝ) / 5) := by
    unfold ψ
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hl1' (by norm_num)
  have hB : Real.log L ^ (-(1 : ℝ) / 5) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hl1 (by norm_num)
  have hB0 : 0 ≤ Real.log L ^ (-(1 : ℝ) / 5) := by positivity
  set a := L ^ ((1 : ℝ) / 5) with ha
  set b := L' ^ ((1 : ℝ) / 5) with hb
  have hpow : ∀ x : ℝ, 0 ≤ x → ∀ k : ℕ, (x ^ ((1 : ℝ) / 5)) ^ k = x ^ ((k : ℝ) / 5) := by
    intro x hx k
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; ring_nf
  have e3a : L ^ ((3 : ℝ) / 5) = a ^ 3 := by rw [ha, hpow L (by linarith) 3]; norm_num
  have e3b : L' ^ ((3 : ℝ) / 5) = b ^ 3 := by rw [hb, hpow L' (by linarith) 3]; norm_num
  have e2a : L ^ ((2 : ℝ) / 5) = a ^ 2 := by rw [ha, hpow L (by linarith) 2]; norm_num
  have e5a : L = a ^ 5 := by rw [ha, hpow L (by linarith) 5]; norm_num
  have e5b : L' = b ^ 5 := by rw [hb, hpow L' (by linarith) 5]; norm_num
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by linarith) _
  have hab : a ≤ b := Real.rpow_le_rpow (by linarith) h (by norm_num)
  have hpsiL : ψ L = a ^ 3 * Real.log L ^ (-(1 : ℝ) / 5) := by unfold ψ; rw [e3a]
  rw [e3b] at hA
  rw [e2a] at hcL
  -- c (ψ L' - ψ L) ≤ c (b^3 - a^3) λ^{-1/5} ≤ c (b^3 - a^3) ≤ a^2 (b^3-a^3) ≤ b^5 - a^5
  have hd : 0 ≤ b ^ 3 - a ^ 3 := by nlinarith [pow_le_pow_left₀ ha0 hab 3]
  have s1 : c * (ψ L' - ψ L) ≤ c * ((b ^ 3 - a ^ 3) * Real.log L ^ (-(1 : ℝ) / 5)) := by
    rw [hpsiL]; apply mul_le_mul_of_nonneg_left _ hc.le; nlinarith
  have s2 : (b ^ 3 - a ^ 3) * Real.log L ^ (-(1 : ℝ) / 5) ≤ b ^ 3 - a ^ 3 := by nlinarith
  have s3 : c * (b ^ 3 - a ^ 3) ≤ a ^ 2 * (b ^ 3 - a ^ 3) := by nlinarith
  have s4 : a ^ 2 * (b ^ 3 - a ^ 3) ≤ b ^ 5 - a ^ 5 := by
    have hba : 0 ≤ b - a := by linarith
    have : b ^ 5 - a ^ 5 - a ^ 2 * (b ^ 3 - a ^ 3) = (b - a) * (b ^ 4 + b ^ 3 * a + (b ^ 2 * a ^ 2 - a ^ 2 * b ^ 2)
      + (b * a ^ 3 - a ^ 3 * b) + (a ^ 4 - a ^ 4) + 0) + (b - a) * (0) := by ring
    have hb0 : 0 ≤ b := ha0.trans hab
    have h4 : 0 ≤ b ^ 4 + b ^ 3 * a := by positivity
    nlinarith [mul_nonneg hba h4]
  rw [e5a, e5b] at *
  nlinarith [mul_le_mul_of_nonneg_left s2 hc.le]

lemma xE_eq (c x : ℝ) (hx : 0 < x) : x * E c x = Real.exp (Real.log x - c * ψ (Real.log x)) := by
  rw [E_eq, sub_eq_add_neg, Real.exp_add, Real.exp_log hx]

/-- `E` is antitone eventually. -/
lemma E_anti (c : ℝ) (hc : 0 < c) : ∀ x y : ℝ, Real.exp (Real.exp 1) ≤ x → x ≤ y → E c y ≤ E c x := by
  intro x y hx hxy
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : Real.exp 1 ≤ Real.log x := by rwa [Real.le_log_iff_exp_le hx0]
  rw [E_eq, E_eq]
  apply Real.exp_le_exp.2
  have := psi_mono _ _ hL (Real.log_le_log hx0 hxy)
  nlinarith

/-- `x E(x)` is monotone eventually. -/
lemma xE_mono (c : ℝ) (hc : 0 < c) : ∃ T, 1 ≤ T ∧ ∀ x y : ℝ, T ≤ x → x ≤ y → x * E c x ≤ y * E c y := by
  obtain ⟨L0, hL0⟩ := psi_diff c hc
  refine ⟨max (Real.exp L0) 1, le_max_right _ _, fun x y hx hxy => ?_⟩
  have hx0 : 0 < x := by linarith [le_max_right (Real.exp L0) 1]
  have hL : L0 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact le_trans (le_max_left _ _) hx
  have h := hL0 _ _ hL (Real.log_le_log hx0 hxy)
  rw [xE_eq c x hx0, xE_eq c y (by linarith)]
  apply Real.exp_le_exp.2
  linarith

/-- `2 √x ≤ x E(x)` eventually. -/
lemma E_big (c : ℝ) : ∃ T, 1 ≤ T ∧ ∀ x : ℝ, T ≤ x → 2 * √x ≤ x * E c x := by
  have ht : Tendsto (fun L : ℝ => L ^ ((2 : ℝ) / 5)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  obtain ⟨L1, hL1⟩ := eventually_atTop.1 (ht.eventually (eventually_ge_atTop (4 * |c|)))
  refine ⟨max (Real.exp (max (max L1 (Real.exp 1)) 4)) 1, le_max_right _ _, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith [le_max_right (Real.exp (max (max L1 (Real.exp 1)) 4)) 1]
  have hL : max (max L1 (Real.exp 1)) 4 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact le_trans (le_max_left _ _) hx
  set L := Real.log x with hLdef
  have hLe : Real.exp 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL4 : 4 ≤ L := le_trans (le_max_right _ _) hL
  have hc4 : 4 * |c| ≤ L ^ ((2 : ℝ) / 5) := hL1 L (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL)
  have hψ := psi_le L hLe
  have hψ0 := psi_nonneg L (by linarith)
  have hLL : L ^ ((3 : ℝ) / 5) * L ^ ((2 : ℝ) / 5) = L := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h3 : 0 ≤ L ^ ((3 : ℝ) / 5) := by positivity
  have hcψ : c * ψ L ≤ L / 4 := by
    have : c * ψ L ≤ |c| * L ^ ((3 : ℝ) / 5) := by
      calc c * ψ L ≤ |c| * ψ L := mul_le_mul_of_nonneg_right (le_abs_self c) hψ0
        _ ≤ |c| * L ^ ((3 : ℝ) / 5) := mul_le_mul_of_nonneg_left hψ (abs_nonneg c)
    nlinarith [mul_le_mul_of_nonneg_left hc4 h3]
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hs : 2 * √x = Real.exp (Real.log 2 + L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, Real.exp_add, Real.exp_log (by norm_num), hLdef]
    ring_nf
  rw [hs, xE_eq c x hx0, ← hLdef]
  apply Real.exp_le_exp.2
  linarith

/-- `E(x) log x ≤ ε` eventually. -/
lemma E_log_small (c : ℝ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ T, 1 ≤ T ∧ ∀ x : ℝ, T ≤ x → E c x * Real.log x ≤ ε := by
  have hq : Tendsto (fun t : ℝ => c * (2 * t / 5) ^ 2 / 2 - t) atTop atTop := by
    have : (fun t : ℝ => c * (2 * t / 5) ^ 2 / 2 - t) = fun t => t * (2 * c / 25 * t - 1) := by
      ext t; ring
    rw [this]
    apply Tendsto.atTop_mul_atTop₀ tendsto_id
    exact tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop (by positivity) tendsto_id)
  obtain ⟨t1, ht1⟩ := eventually_atTop.1 (hq.eventually (eventually_ge_atTop (-Real.log ε)))
  set t0 := max t1 1
  refine ⟨Real.exp (Real.exp t0), Real.one_le_exp (Real.exp_pos _).le, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : Real.exp t0 ≤ Real.log x := by rwa [Real.le_log_iff_exp_le hx0]
  set L := Real.log x with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl : t0 ≤ Real.log L := by rwa [Real.le_log_iff_exp_le hL0]
  have hl0 : 0 ≤ Real.log L := le_trans (by norm_num) (le_trans (le_max_right _ _) hl)
  have h1 : 1 < L := by
    have := Real.add_one_le_exp t0; have : 1 ≤ t0 := le_max_right _ _; linarith
  have hψ : Real.exp (2 * Real.log L / 5) ≤ ψ L := by
    rw [psi_eq L h1]; apply Real.exp_le_exp.2
    have : Real.log (Real.log L) ≤ Real.log L := by
      rcases hl0.lt_or_eq with h | h
      · have := Real.log_le_sub_one_of_pos h; linarith
      · rw [← h]; simp
    linarith
  have hexp : (2 * Real.log L / 5) ^ 2 / 2 ≤ Real.exp (2 * Real.log L / 5) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 2 * Real.log L / 5) (by positivity)
    nlinarith [hl0]
  have hq1 := ht1 (Real.log L) (le_trans (le_max_left _ _) hl)
  have hcψ : c * (2 * Real.log L / 5) ^ 2 / 2 ≤ c * ψ L := by
    have := mul_le_mul_of_nonneg_left (hexp.trans hψ) hc.le; linarith
  have hEL : E c x * L = Real.exp (-(c * ψ L) + Real.log L) := by
    rw [E_eq, Real.exp_add, Real.exp_log hL0]
  rw [hEL, ← Real.exp_log hε]
  apply Real.exp_le_exp.2
  linarith

end LIE

end

-- ===== LI/Th =====
section

namespace LIT
open Finset Real Filter Topology MeasureTheory LandauFunction Chebyshev

lemma cont_inv_log (a b : ℝ) (ha : 1 < a) :
    ContinuousOn (fun t => 1 / Real.log t) (Set.Icc a b) := by
  intro t ht
  have h1 : 1 < t := by linarith [ht.1]
  have hl : Real.log t ≠ 0 := (Real.log_pos h1).ne'
  have : ContinuousAt (fun t => 1 / Real.log t) t :=
    continuousAt_const.div (Real.continuousAt_log (by positivity)) hl
  exact this.continuousWithinAt

lemma cont_inv_log' (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ContinuousOn (fun t => 1 / Real.log t) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]; exact cont_inv_log a b ha

lemma li_hasDeriv (t : ℝ) (ht : 2 ≤ t) : HasDerivAt logIntegral (1 / Real.log t) t := by
  have hcont : ContinuousOn (fun t => 1 / Real.log t) (Set.Ioi 1) := by
    intro s hs
    have h1 : 1 < s := hs
    exact (continuousAt_const.div (Real.continuousAt_log (by positivity))
      (Real.log_pos h1).ne').continuousWithinAt
  have hca : ContinuousAt (fun t => 1 / Real.log t) t :=
    hcont.continuousAt (Ioi_mem_nhds (by linarith))
  exact intervalIntegral.integral_hasDerivAt_right
    ((cont_inv_log' 2 t (by norm_num) ht).intervalIntegrable)
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi t (by show (1:ℝ) < t; linarith)) hca

lemma li_cont : ContinuousOn logIntegral (Set.Ici 2) :=
  fun t ht => (li_hasDeriv t ht).continuousAt.continuousWithinAt

lemma li_two : logIntegral 2 = 0 := by unfold logIntegral; simp

lemma li_sub (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    logIntegral b - logIntegral a = ∫ t in a..b, 1 / Real.log t := by
  unfold logIntegral
  have i1 : IntervalIntegrable (fun t => 1 / Real.log t) volume 2 a :=
    (cont_inv_log' 2 a (by norm_num) ha).intervalIntegrable
  have i2 : IntervalIntegrable (fun t => 1 / Real.log t) volume a b :=
    (cont_inv_log' a b (by linarith) hab).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]; ring

lemma li_mono (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ logIntegral b - logIntegral a := by
  rw [li_sub a b ha hab]
  have hb : 0 < Real.log b := Real.log_pos (by linarith)
  have : ∫ _ in a..b, 1 / Real.log b = (b - a) / Real.log b := by simp; ring
  rw [← this]
  apply intervalIntegral.integral_mono_on hab (by simp)
    ((cont_inv_log' a b (by linarith) hab).intervalIntegrable)
  intro t ht
  have ht0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
  exact one_div_le_one_div_of_le ht0 (Real.log_le_log (by linarith [ht.1]) ht.2)

lemma li_le (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    logIntegral b - logIntegral a ≤ (b - a) / Real.log a := by
  rw [li_sub a b ha hab]
  have hb : 0 < Real.log a := Real.log_pos (by linarith)
  have : ∫ _ in a..b, 1 / Real.log a = (b - a) / Real.log a := by simp; ring
  rw [← this]
  apply intervalIntegral.integral_mono_on hab
    ((cont_inv_log' a b (by linarith) hab).intervalIntegrable) (by simp)
  intro t ht
  have ht0 : 0 < Real.log a := hb
  exact one_div_le_one_div_of_le ht0 (Real.log_le_log (by linarith [ht.1]) ht.1)

lemma li_parts (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, logIntegral t / t = logIntegral x * Real.log x - x + 2 := by
  have hd : ∀ t ∈ Set.uIcc 2 x, HasDerivAt (fun t => logIntegral t * Real.log t - t) (logIntegral t / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have := ((li_hasDeriv t ht.1).mul (Real.hasDerivAt_log ht0)).sub (hasDerivAt_id t)
    have h2 : logIntegral t / t = 1 / Real.log t * Real.log t + logIntegral t * t⁻¹ - 1 := by
      rw [one_div, inv_mul_cancel₀ hl]; ring
    rw [h2]; exact this
  have hint : IntervalIntegrable (fun t => logIntegral t / t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((li_hasDeriv t ht.1).continuousAt.div continuousAt_id ht0).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, li_two]
  ring

lemma pi_int (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (Nat.primeCounting ⌊t⌋₊ : ℝ) / t) volume a b := by
  have hm : Monotone (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ)) := by
    intro s t hst
    exact Nat.cast_le.2 (Nat.monotone_primeCounting (Nat.floor_mono hst))
  have h1 := (hm.intervalIntegrable (μ := volume) (a := a) (b := b)).mul_continuousOn
    (g := fun t => t⁻¹) (by
      rw [Set.uIcc_of_le hab]; intro t ht
      exact (continuousAt_inv₀ (by linarith [ht.1] : t ≠ 0)).continuousWithinAt)
  simpa [div_eq_mul_inv] using h1

lemma li_div_int (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => logIntegral t / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  exact ((li_hasDeriv t (by linarith [ht.1])).continuousAt.div continuousAt_id ht0).continuousWithinAt

/-- θ bound from the π hypothesis. -/
theorem theta_bound (c : ℝ) (hc : 0 < c) (C T1 : ℝ) (hC : 0 ≤ C)
    (hπ : ∀ x : ℝ, T1 ≤ x → |(Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x| ≤ C * (x * LIE.E c x)) :
    ∃ K T : ℝ, 0 ≤ K ∧ 3 ≤ T ∧ ∀ x : ℝ, T ≤ x →
      |θ x - x| ≤ K * (x * LIE.E c x * Real.log x) := by
  obtain ⟨Tm, hTm1, hmono⟩ := LIE.xE_mono c hc
  obtain ⟨Tb, hTb1, hbig⟩ := LIE.E_big c
  set T0 := max (max T1 Tm) 3 with hT0
  have hT03 : 3 ≤ T0 := le_max_right _ _
  set R : ℝ → ℝ := fun t => (Nat.primeCounting ⌊t⌋₊ : ℝ) - logIntegral t with hR
  set I0 := ∫ t in (2:ℝ)..T0, R t / t with hI0
  set K0 := |I0| + 2 with hK0
  refine ⟨2 * C + 1, max T0 (max Tb (K0 ^ 2)), by positivity,
    le_trans hT03 (le_max_left _ _), fun x hx => ?_⟩
  have hxT0 : T0 ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans hT03 hxT0
  have hx0 : 0 < x := by linarith
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have hRint : ∀ a b : ℝ, 2 ≤ a → a ≤ b → IntervalIntegrable (fun t => R t / t) volume a b := by
    intro a b ha hab
    have := (pi_int a b (by linarith) hab).sub (li_div_int a b ha hab)
    simpa [hR, sub_div] using this
  -- identity
  have hθ := theta_eq_primeCounting_mul_log_sub_integral (by linarith : (2:ℝ) ≤ x)
  have hsplit : ∫ t in (2:ℝ)..x, R t / t =
      (∫ t in (2:ℝ)..x, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t) - ∫ t in (2:ℝ)..x, logIntegral t / t := by
    rw [← intervalIntegral.integral_sub (pi_int 2 x (by norm_num) (by linarith))
      (li_div_int 2 x (le_refl _) (by linarith))]
    congr 1; ext t; simp [hR, sub_div]
  rw [li_parts x (by linarith)] at hsplit
  have hid : θ x - x = R x * Real.log x - (∫ t in (2:ℝ)..x, R t / t) - 2 := by
    rw [hsplit, hθ]; simp only [hR]; ring
  have hadj : ∫ t in (2:ℝ)..x, R t / t = I0 + ∫ t in T0..x, R t / t :=
    (intervalIntegral.integral_add_adjacent_intervals (hRint 2 T0 (by norm_num) (by linarith))
      (hRint T0 x (by linarith) hxT0)).symm
  set Q := x * LIE.E c x with hQ
  have hQ0 : 0 ≤ Q := mul_nonneg hx0.le (LIE.E_pos c x).le
  -- tail bound
  have htail : |∫ t in T0..x, R t / t| ≤ C * Q * Real.log x := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (f := fun t => R t / t)
      (g := fun t => C * Q * t⁻¹) (μ := volume) hxT0 (Filter.Eventually.of_forall fun t ht => by
        have ht0 : 0 < t := by linarith [ht.1]
        rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 ht0.le)
        have h1 := hπ t (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht.1.le)
        have h2 := hmono t x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht.1.le) ht.2
        calc |R t| ≤ C * (t * LIE.E c t) := h1
          _ ≤ C * Q := mul_le_mul_of_nonneg_left h2 hC)
      (by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hxT0]; intro t ht
        exact (continuousAt_const.mul (continuousAt_inv₀ (by linarith [ht.1] : t ≠ 0))).continuousWithinAt)
    rw [Real.norm_eq_abs] at hb
    refine hb.trans (le_of_eq_of_le (b := C * Q * Real.log (x / T0)) ?_ ?_)
    · rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by linarith) hx0]
    · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hQ0)
      rw [Real.log_div hx0.ne' (by linarith)]
      have : 0 ≤ Real.log T0 := Real.log_nonneg (by linarith)
      linarith
  have hRx : |R x| ≤ C * Q :=
    hπ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxT0)
  have hK0Q : K0 ≤ Q := by
    have hb := hbig x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx)
    have hs : K0 ≤ √x := by
      have : K0 ^ 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
      calc K0 = √(K0 ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ √x := Real.sqrt_le_sqrt this
    have : 0 ≤ √x := Real.sqrt_nonneg x
    linarith
  rw [hid, hadj]
  have e : R x * Real.log x - (I0 + ∫ t in T0..x, R t / t) - 2
      = R x * Real.log x - (∫ t in T0..x, R t / t) - (I0 + 2) := by ring
  rw [e]
  have h1 : |R x * Real.log x| ≤ C * Q * Real.log x := by
    rw [abs_mul, abs_of_pos (by linarith : 0 < Real.log x)]
    exact mul_le_mul_of_nonneg_right hRx (by linarith)
  have h2 : |I0 + 2| ≤ Q * Real.log x := by
    have : |I0 + 2| ≤ K0 := by rw [hK0]; exact (abs_add_le _ _).trans (by norm_num)
    nlinarith
  have := abs_sub (R x * Real.log x - ∫ t in T0..x, R t / t) (I0 + 2)
  have := abs_sub (R x * Real.log x) (∫ t in T0..x, R t / t)
  have e2 : (2 * C + 1) * (Q * Real.log x) = C * Q * Real.log x + C * Q * Real.log x + Q * Real.log x := by ring
  rw [show x * LIE.E c x * Real.log x = Q * Real.log x by rw [hQ], e2]
  linarith

end LIT

end

-- ===== LI/S =====
section

namespace LIS
open Finset Real Filter Topology MeasureTheory LandauFunction Chebyshev

lemma J_eq (x : ℝ) (hx : 2 ≤ x) : LES.J x = logIntegral (x ^ 2) - logIntegral 4 := by
  have h4 : logIntegral (x ^ 2) - logIntegral 4 = ∫ t in (4:ℝ)..x ^ 2, 1 / Real.log t :=
    LIT.li_sub 4 (x ^ 2) (by norm_num) (by nlinarith)
  rw [h4, LES.J]
  have hsub := intervalIntegral.integral_comp_mul_deriv'' (a := 2) (b := x) (f := fun t => t ^ 2)
    (f' := fun t => 2 * t) (g := fun t => 1 / Real.log t)
    (by fun_prop)
    (fun t _ => (hasDerivAt_pow 2 t).hasDerivWithinAt.congr_deriv (by ring))
    (by fun_prop)
    (by
      have hI : (fun t : ℝ => t ^ 2) '' Set.uIcc 2 x ⊆ Set.uIcc 4 (x ^ 2) := by
        rintro _ ⟨t, ht, rfl⟩
        rw [Set.uIcc_of_le hx] at ht
        rw [Set.uIcc_of_le (by nlinarith)]
        exact ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩
      exact (LIT.cont_inv_log' 4 (x ^ 2) (by norm_num) (by nlinarith)).mono hI)
  have e4 : (2:ℝ) ^ 2 = 4 := by norm_num
  rw [e4] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hx] at ht
  have ht0 : 0 < t := by linarith [ht.1]
  simp only [Function.comp, Real.log_pow]
  have : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
  field_simp
  norm_num

lemma S0_eq (N : ℕ) : LGA.S0 N = ∑ p ∈ Icc 0 N with p.Prime, (p:ℝ) := by
  unfold LGA.S0 LGA.P
  have : Finset.range (N + 1) = Finset.Icc 0 N := by ext k; simp
  rw [this]

theorem S_bound (c : ℝ) (hc : 0 < c) (K T : ℝ) (hK : 0 ≤ K) (hT : 3 ≤ T)
    (hθ : ∀ x : ℝ, T ≤ x → |θ x - x| ≤ K * (x * LIE.E c x * Real.log x)) :
    ∃ K' T' : ℝ, 0 ≤ K' ∧ 4 ≤ T' ∧ ∀ x : ℝ, T' ≤ x →
      |LGA.S0 ⌊x⌋₊ - logIntegral (x ^ 2)| ≤ K' * (x ^ 2 * LIE.E c x) := by
  obtain ⟨Tm, hTm1, hmono⟩ := LIE.xE_mono c hc
  obtain ⟨Tb, hTb1, hbig⟩ := LIE.E_big c
  set T0 := max (max T Tm) 4 with hT0
  have hT04 : 4 ≤ T0 := le_max_right _ _
  set g : ℝ → ℝ := fun t => (1 / Real.log t - 1 / Real.log t ^ 2) * (θ t - t) with hg
  have hgint : ∀ a b : ℝ, 2 ≤ a → a ≤ b → IntervalIntegrable g volume a b := by
    intro a b ha hab
    have h1 := LES.theta_int b (by linarith)
    have h2 : IntervalIntegrable (fun t => (1 / Real.log t - 1 / Real.log t ^ 2) * t) volume 2 b := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)]
      exact (LES.cont_g' 2 b (by norm_num)).mul continuousOn_id
    have h3 := h1.sub h2
    have h4 : IntervalIntegrable g volume 2 b := by
      have e : g = fun t => (1 / Real.log t - 1 / Real.log t ^ 2) * θ t - (1 / Real.log t - 1 / Real.log t ^ 2) * t := by
        ext t; simp only [hg]; ring
      rw [e]; exact h3
    refine h4.mono_set ?_
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by linarith : (2:ℝ) ≤ b)]
    exact Set.Icc_subset_Icc ha (le_refl _)
  set I1 := ∫ t in (2:ℝ)..T0, g t with hI1
  set K1 := |I1| + |4 / Real.log 2 - logIntegral 4| with hK1
  refine ⟨2 * K + 1, max T0 (max Tb (K1 ^ 2)), by positivity,
    le_trans hT04 (le_max_left _ _), fun x hx => ?_⟩
  have hxT0 : T0 ≤ x := le_trans (le_max_left _ _) hx
  have hx4 : 4 ≤ x := le_trans hT04 hxT0
  have hx0 : 0 < x := by linarith
  have hlx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have hab := LES.S0_abel x (by linarith)
  have hid := LES.int_identity x (by linarith)
  rw [J_eq x (by linarith)] at hid
  have hsplit : ∫ t in (2:ℝ)..x, g t = (∫ t in (2:ℝ)..x, (1 / Real.log t - 1 / Real.log t ^ 2) * θ t)
      - ∫ t in (2:ℝ)..x, (1 / Real.log t - 1 / Real.log t ^ 2) * t := by
    rw [← intervalIntegral.integral_sub (LES.theta_int x (by linarith))]
    · congr 1; ext t; simp only [hg]; ring
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)]
      exact (LES.cont_g' 2 x (by norm_num)).mul continuousOn_id
  have hadj : ∫ t in (2:ℝ)..x, g t = I1 + ∫ t in T0..x, g t :=
    (intervalIntegral.integral_add_adjacent_intervals (hgint 2 T0 (by norm_num) (by linarith))
      (hgint T0 x (by linarith) hxT0)).symm
  have hlx0 : 0 < Real.log x := by linarith
  have hiden : LGA.S0 ⌊x⌋₊ - logIntegral (x ^ 2) =
      x / Real.log x * (θ x - x) - (∫ t in T0..x, g t) - (I1 - (4 / Real.log 2 - logIntegral 4)) := by
    rw [S0_eq, hab]
    have : x / Real.log x * (θ x - x) = x / Real.log x * θ x - x ^ 2 / Real.log x := by
      field_simp
    rw [this]
    have h2 := hsplit
    rw [hadj, hid] at h2
    linarith
  set Q := x * LIE.E c x with hQ
  have hQ0 : 0 ≤ Q := mul_nonneg hx0.le (LIE.E_pos c x).le
  have htail : |∫ t in T0..x, g t| ≤ K * Q * x := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (f := g)
      (g := fun _ => K * Q) (μ := volume) hxT0 (Filter.Eventually.of_forall fun t ht => by
        have ht0 : 0 < t := by linarith [ht.1]
        have hT0t : T0 ≤ t := ht.1.le
        have hlt : 1 ≤ Real.log t := by
          rw [Real.le_log_iff_exp_le ht0]; have := Real.exp_one_lt_d9; linarith
        have hlt0 : 0 < Real.log t := by linarith
        have hg1 : |1 / Real.log t - 1 / Real.log t ^ 2| ≤ 1 / Real.log t := by
          have h1 : 0 ≤ 1 / Real.log t - 1 / Real.log t ^ 2 := by
            rw [sub_nonneg]; apply one_div_le_one_div_of_le hlt0; nlinarith
          rw [abs_of_nonneg h1]
          have : 0 ≤ 1 / Real.log t ^ 2 := by positivity
          linarith
        have h1 := hθ t (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT0t)
        have h2 := hmono t x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT0t) ht.2
        simp only [hg]
        rw [Real.norm_eq_abs, abs_mul]
        calc |1 / Real.log t - 1 / Real.log t ^ 2| * |θ t - t|
            ≤ 1 / Real.log t * (K * (t * LIE.E c t * Real.log t)) :=
              mul_le_mul hg1 h1 (abs_nonneg _) (by positivity)
          _ = K * (t * LIE.E c t) := by field_simp
          _ ≤ K * Q := mul_le_mul_of_nonneg_left h2 hK)
      (by simp)
    rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    have : 0 ≤ K * Q := mul_nonneg hK hQ0
    have : 0 ≤ T0 := by linarith
    nlinarith
  have hfirst : |x / Real.log x * (θ x - x)| ≤ K * Q * x := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < x / Real.log x)]
    have h1 := hθ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxT0)
    calc x / Real.log x * |θ x - x| ≤ x / Real.log x * (K * (Q * Real.log x)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); rw [hQ]; exact h1
      _ = K * Q * x := by field_simp
  have hK1Q : K1 ≤ Q := by
    have hb := hbig x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx)
    have hs : K1 ≤ √x := by
      have : K1 ^ 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
      calc K1 = √(K1 ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ √x := Real.sqrt_le_sqrt this
    have : 0 ≤ √x := Real.sqrt_nonneg x
    linarith
  have hconst : |I1 - (4 / Real.log 2 - logIntegral 4)| ≤ Q * x := by
    have : |I1 - (4 / Real.log 2 - logIntegral 4)| ≤ K1 := abs_sub _ _
    nlinarith
  rw [hiden]
  have e2 : (2 * K + 1) * (x ^ 2 * LIE.E c x) = K * Q * x + K * Q * x + Q * x := by rw [hQ]; ring
  rw [e2]
  have := abs_sub (x / Real.log x * (θ x - x) - ∫ t in T0..x, g t) (I1 - (4 / Real.log 2 - logIntegral 4))
  have := abs_sub (x / Real.log x * (θ x - x)) (∫ t in T0..x, g t)
  linarith

end LIS

end

-- ===== LI/Inv =====
section

namespace LII
open Finset Real Filter Topology MeasureTheory LandauFunction

lemma inv_spec (y x1 : ℝ) (hy : 0 ≤ y) (hx1 : 2 ≤ x1) (hyx : y ≤ logIntegral x1) :
    2 ≤ logIntegralInv y ∧ logIntegralInv y ≤ x1 ∧ logIntegral (logIntegralInv y) = y := by
  set S := {x : ℝ | 2 ≤ x ∧ y ≤ logIntegral x} with hS
  have hne : S.Nonempty := ⟨x1, hx1, hyx⟩
  have hbdd : BddBelow S := ⟨2, fun x hx => hx.1⟩
  have hcl : IsClosed S := by
    have := LIT.li_cont.preimage_isClosed_of_isClosed (t := Set.Ici y) isClosed_Ici isClosed_Ici
    exact this
  have hmem : sInf S ∈ S := hcl.csInf_mem hne hbdd
  have hdef : logIntegralInv y = sInf S := rfl
  rw [hdef]
  refine ⟨hmem.1, csInf_le hbdd ⟨hx1, hyx⟩, le_antisymm ?_ hmem.2⟩
  obtain ⟨z, hz, hzy⟩ := intermediate_value_Icc hmem.1 (LIT.li_cont.mono Set.Icc_subset_Ici_self)
    (show y ∈ Set.Icc (logIntegral 2) (logIntegral (sInf S)) from ⟨by rw [LIT.li_two]; exact hy, hmem.2⟩)
  have hzS : z ∈ S := ⟨hz.1, hzy.ge⟩
  have : sInf S ≤ z := csInf_le hbdd hzS
  have hz' : z = sInf S := le_antisymm hz.2 this
  rw [← hz', hzy]

lemma li_upper (z : ℝ) (hz : 2 ≤ z) : logIntegral z ≤ (z - 2) / Real.log 2 := by
  have := LIT.li_le 2 z (le_refl _) hz
  rw [LIT.li_two] at this; linarith

lemma li_at (x : ℝ) (hx : 8 ≤ x) : x ≤ logIntegral (2 * x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hl : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  set ℓ := Real.log x with hℓ
  have h2 : (2:ℝ) ≤ 2 * x * ℓ := by nlinarith
  have hm := LIT.li_mono 2 (2 * x * ℓ) (le_refl _) h2
  rw [LIT.li_two, sub_zero] at hm
  have hlog : Real.log (2 * x * ℓ) = Real.log 2 + ℓ + Real.log ℓ := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
  have hlℓ : Real.log ℓ ≤ ℓ - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hl2 : Real.log 2 < 7 / 10 := by have := Real.log_two_lt_d9; linarith
  have hpos : 0 < Real.log (2 * x * ℓ) := Real.log_pos (by nlinarith)
  have hle : Real.log (2 * x * ℓ) ≤ 2 * ℓ - 3 / 10 := by rw [hlog]; linarith
  refine le_trans ?_ hm
  rw [le_div_iff₀ hpos]
  nlinarith

end LII

end

-- ===== LI/P =====
section

namespace LIP
open Finset Real Filter Topology LandauFunction

lemma log_ge_two (x : ℝ) (hx : 8 ≤ x) : 2 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos 1]

set_option maxHeartbeats 4000000 in
theorem pointwise (c KS Kθ W : ℝ) (hKS : 0 ≤ KS) (hKθ : 0 ≤ Kθ) (hW : 4 ≤ W)
    (hθ : ∀ x : ℝ, W ≤ x → |Chebyshev.theta x - x| ≤ Kθ * (x * LIE.E c x * Real.log x))
    (hS : ∀ x : ℝ, W ≤ x → |LGA.S0 ⌊x⌋₊ - logIntegral (x ^ 2)| ≤ KS * (x ^ 2 * LIE.E c x))
    (hmono : ∀ x y : ℝ, W ≤ x → x ≤ y → x * LIE.E c x ≤ y * LIE.E c y)
    (hanti : ∀ x y : ℝ, W ≤ x → x ≤ y → LIE.E c y ≤ LIE.E c x)
    (hbig : ∀ x : ℝ, W ≤ x → 2 * √x ≤ x * LIE.E c x)
    (hsmall : ∀ x : ℝ, W ≤ x → LIE.E c x * Real.log x ≤ 1 / (2 * (8 * KS + 1)))
    (n : ℕ) (hn : 8 * W ^ 2 ≤ (n:ℝ)) (hn8 : 8 ≤ (n:ℝ)) :
    |Real.log (landau n) - √(logIntegralInv n)| ≤
      4 * ((8 * KS + 1) + 4 * Kθ + 4) *
        (√(n * Real.log n) * LIE.E c (√(n * Real.log n)) * Real.log n) := by
  set x : ℝ := (n:ℝ) with hxdef
  set D := 8 * KS + 1 with hD
  have hD0 : 0 < D := by positivity
  have hx0 : 0 < x := by linarith
  set ℓ := Real.log x with hℓ
  have hl2 : 2 ≤ ℓ := log_ge_two x hn8
  -- inverse
  obtain ⟨hy2, hyle, hliy⟩ := LII.inv_spec x (2 * x * ℓ) hx0.le (by nlinarith only [hn8, hl2]) (LII.li_at x hn8)
  set y0 := logIntegralInv x with hy0
  have hylo : x / 2 ≤ y0 := by
    have := LII.li_upper y0 hy2
    rw [hliy, le_div_iff₀ (Real.log_pos (by norm_num))] at this
    have h2 := Real.log_two_gt_d9
    nlinarith only [this, h2, hx0]
  set w0 := √y0 with hw0
  have hw0sq : w0 ^ 2 = y0 := Real.sq_sqrt (by linarith)
  have hw0pos : 0 < w0 := Real.sqrt_pos.2 (by linarith)
  have hw0W : 2 * W ≤ w0 := by
    have h1 : (2 * W) ^ 2 ≤ w0 ^ 2 := by rw [hw0sq]; nlinarith only [hn, hylo]
    exact (pow_le_pow_iff_left₀ (by linarith) hw0pos.le (by norm_num)).1 h1
  set v := √(x * ℓ) with hv
  have hxl0 : 0 < x * ℓ := by positivity
  have hvsq : v ^ 2 = x * ℓ := Real.sq_sqrt hxl0.le
  have hv0 : 0 < v := Real.sqrt_pos.2 hxl0
  have hw0v : w0 ≤ 2 * v := by
    have h1 : w0 ^ 2 ≤ (2 * v) ^ 2 := by rw [hw0sq, mul_pow, hvsq]; nlinarith only [hyle, hxl0]
    exact (pow_le_pow_iff_left₀ hw0pos.le (by linarith) (by norm_num)).1 h1
  have hvW : W ≤ v := by
    have h1 : W ^ 2 ≤ v ^ 2 := by rw [hvsq]; nlinarith only [hn, hl2, hx0, hW]
    exact (pow_le_pow_iff_left₀ (by linarith) hv0.le (by norm_num)).1 h1
  -- E at w0
  set e0 := LIE.E c w0 with he0
  have he0pos : 0 < e0 := LIE.E_pos c w0
  set lw := Real.log w0 with hlw
  have hlw1 : 1 ≤ lw := by
    rw [hlw, Real.le_log_iff_exp_le hw0pos]; have := Real.exp_one_lt_d9; linarith
  set Q := w0 * e0 * lw with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hsm : e0 * lw ≤ 1 / (2 * D) := hsmall w0 (by linarith)
  set Δ := D * Q with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hΔw : Δ ≤ w0 / 2 := by
    have : Δ = w0 * (D * (e0 * lw)) := by rw [hΔ, hQ]; ring
    rw [this]
    have h1 : D * (e0 * lw) ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hsm hD0.le
      rwa [show D * (1 / (2 * D)) = 1 / 2 by field_simp] at this
    nlinarith only [h1, hw0pos]
  set wm := w0 - Δ with hwm
  set wp := w0 + Δ with hwp
  have hwmW : W ≤ wm := by linarith
  have hwm0 : 0 < wm := by linarith
  have hwmw0 : wm ≤ w0 := by linarith
  have hwpW : W ≤ wp := by linarith
  have hwp2 : wp ≤ 2 * w0 := by linarith
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlwp : Real.log wp ≤ 2 * lw := by
    have := Real.log_le_log (by linarith) hwp2
    rw [Real.log_mul (by norm_num) hw0pos.ne'] at this
    linarith
  have hlwm : Real.log wm ≤ lw := Real.log_le_log hwm0 hwmw0
  have hlwm0 : 0 ≤ Real.log wm := Real.log_nonneg (by linarith)
  have hEp : LIE.E c wp ≤ e0 := hanti w0 wp (by linarith) (by linarith)
  have hmEm : wm * LIE.E c wm ≤ w0 * e0 := hmono wm w0 hwmW hwmw0
  have hEm0 : 0 < LIE.E c wm := LIE.E_pos c wm
  have hEp0 : 0 < LIE.E c wp := LIE.E_pos c wp
  -- key: w0 * e0 * Δ-relation
  have hkey : Δ * w0 / (2 * lw) = D / 2 * (w0 ^ 2 * e0) := by
    rw [hΔ, hQ]; field_simp
  -- (i) sum at wm ≤ x
  have hSm_le : LGA.S0 ⌊wm⌋₊ ≤ x := by
    have h1 := abs_le.1 (hS wm hwmW)
    have hli := LIT.li_mono (wm ^ 2) (w0 ^ 2) (by nlinarith only [hwmW, hW]) (pow_le_pow_left₀ hwm0.le hwmw0 2)
    rw [hw0sq, hliy] at hli
    have hlog : Real.log y0 = 2 * lw := by rw [← hw0sq, Real.log_pow]; push_cast; ring
    rw [hlog] at hli
    have hdiff : Δ * w0 ≤ y0 - wm ^ 2 := by rw [← hw0sq, hwm]; nlinarith only [hΔw, hΔ0, hw0pos]
    have h2 : Δ * w0 / (2 * lw) ≤ (y0 - wm ^ 2) / (2 * lw) :=
      div_le_div_of_nonneg_right hdiff (by positivity)
    have h3 : wm ^ 2 * LIE.E c wm ≤ w0 ^ 2 * e0 := by
      have : wm ^ 2 * LIE.E c wm = wm * (wm * LIE.E c wm) := by ring
      rw [this, show w0 ^ 2 * e0 = w0 * (w0 * e0) by ring]
      exact mul_le_mul hwmw0 hmEm (by positivity) hw0pos.le
    have h4 : 0 ≤ w0 ^ 2 * e0 := by positivity
    rw [hkey] at h2
    have : KS * (wm ^ 2 * LIE.E c wm) ≤ KS * (w0 ^ 2 * e0) := mul_le_mul_of_nonneg_left h3 hKS
    rw [hD] at h2
    linarith [h1.2]
  -- (ii) sum at wp ≥ x
  have hSp_ge : x ≤ LGA.S0 ⌊wp⌋₊ := by
    have h1 := abs_le.1 (hS wp hwpW)
    have hw0wp : w0 ≤ wp := by linarith
    have hli := LIT.li_mono (w0 ^ 2) (wp ^ 2) (by nlinarith only [hw0W, hW]) (pow_le_pow_left₀ hw0pos.le hw0wp 2)
    rw [hw0sq, hliy] at hli
    have hlog : Real.log (wp ^ 2) ≤ 4 * lw := by rw [Real.log_pow]; push_cast; linarith
    have hlogp : 0 < Real.log (wp ^ 2) := Real.log_pos (by nlinarith only [hwpW, hW])
    have hdiff : 2 * Δ * w0 ≤ wp ^ 2 - y0 := by rw [← hw0sq, hwp]; nlinarith only [sq_nonneg Δ]
    have h2 : 2 * Δ * w0 / (4 * lw) ≤ (wp ^ 2 - y0) / Real.log (wp ^ 2) :=
      div_le_div₀ (by nlinarith only [hdiff, hΔ0, hw0pos]) hdiff hlogp hlog
    have e2 : 2 * Δ * w0 / (4 * lw) = Δ * w0 / (2 * lw) := by field_simp; ring
    rw [e2, hkey] at h2
    have h3 : wp ^ 2 * LIE.E c wp ≤ 4 * (w0 ^ 2 * e0) := by
      have : wp ^ 2 ≤ (2 * w0) ^ 2 := pow_le_pow_left₀ (by linarith) hwp2 2
      have := mul_le_mul this hEp hEp0.le (by positivity)
      linarith
    have : KS * (wp ^ 2 * LIE.E c wp) ≤ KS * (4 * (w0 ^ 2 * e0)) := mul_le_mul_of_nonneg_left h3 hKS
    have h4 : 0 ≤ w0 ^ 2 * e0 := by positivity
    rw [hD] at h2
    linarith [h1.1]
  -- lower bound
  have hlower : w0 - (D + Kθ) * Q ≤ Real.log (landau n) := by
    set N := ⌊wm⌋₊
    have hsum : ∑ p ∈ LGA.P N, p ≤ n := by
      have : ((∑ p ∈ LGA.P N, p : ℕ) : ℝ) = LGA.S0 N := by unfold LGA.S0; push_cast; rfl
      have h' : LGA.S0 N ≤ (n:ℝ) := hSm_le
      rw [← this] at h'
      exact_mod_cast h'
    have hlo := LGB.lower n N hsum
    rw [LGA.th_eq, ← Chebyshev.theta_eq_theta_coe_floor] at hlo
    have h1 := abs_le.1 (hθ wm hwmW)
    have h2 : Kθ * (wm * LIE.E c wm * Real.log wm) ≤ Kθ * Q := by
      apply mul_le_mul_of_nonneg_left _ hKθ
      rw [hQ]; exact mul_le_mul hmEm hlwm hlwm0 (by positivity)
    have : (D + Kθ) * Q = Δ + Kθ * Q := by rw [hΔ]; ring
    rw [this]
    linarith
  -- upper bound
  have hupper : Real.log (landau n) ≤ w0 + (D + 4 * Kθ + 4) * Q := by
    set M := ⌊wp⌋₊ with hM
    have hMw : (M:ℝ) ≤ wp := Nat.floor_le (by linarith)
    have hM4' : (4:ℝ) ≤ M := by
      have : (4:ℕ) ≤ M := Nat.le_floor (by push_cast; linarith)
      exact_mod_cast this
    have hM4 : 4 ≤ M := by exact_mod_cast hM4'
    have hup := LEU.landau_upper n M hM4
    rw [LGA.th_eq, ← Chebyshev.theta_eq_theta_coe_floor] at hup
    have hlM : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by linarith)
    have hlam : -(Real.log M / M * LGA.S0 M) + n * Real.log M / M ≤ 0 := by
      have : (n:ℝ) * Real.log M / M = Real.log M / M * x := by rw [hxdef]; ring
      rw [this]
      have : 0 ≤ Real.log M / M := div_nonneg hlM (by linarith)
      have := mul_le_mul_of_nonneg_left hSp_ge this
      linarith
    have hsq : ((Nat.sqrt M : ℕ) : ℝ) + 1 ≤ √wp + 1 := by
      have := Real.nat_sqrt_le_real_sqrt (a := M)
      have := Real.sqrt_le_sqrt hMw
      linarith
    have hlogM : Real.log (M:ℝ) ≤ Real.log wp := Real.log_le_log (by linarith) hMw
    have hb := hbig wp hwpW
    have hs1 : 1 ≤ √wp := by
      rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    have hwpE : wp * LIE.E c wp ≤ 2 * (w0 * e0) := by
      have := mul_le_mul hwp2 hEp hEp0.le (by linarith)
      linarith
    have hlwp0 : 0 ≤ Real.log wp := Real.log_nonneg (by linarith)
    have hP : wp * LIE.E c wp * Real.log wp ≤ 4 * Q := by
      have := mul_le_mul hwpE hlwp hlwp0 (by positivity)
      rw [hQ]; linarith
    have hrem : ((Nat.sqrt M : ℕ) + 1 : ℝ) * Real.log M ≤ 4 * Q := by
      calc ((Nat.sqrt M : ℕ) + 1 : ℝ) * Real.log M ≤ (√wp + 1) * Real.log wp := by
            apply mul_le_mul hsq hlogM hlM (by linarith [Real.sqrt_nonneg wp])
        _ ≤ (wp * LIE.E c wp) * Real.log wp := by
            apply mul_le_mul_of_nonneg_right _ hlwp0; linarith
        _ ≤ 4 * Q := hP
    have hθp := abs_le.1 (hθ wp hwpW)
    have hθp2 : Kθ * (wp * LIE.E c wp * Real.log wp) ≤ Kθ * (4 * Q) := mul_le_mul_of_nonneg_left hP hKθ
    have e : (Nat.sqrt M + 1 : ℝ) * Real.log M = ((Nat.sqrt M : ℕ) + 1 : ℝ) * Real.log M := rfl
    have : (D + 4 * Kθ + 4) * Q = Δ + Kθ * (4 * Q) + 4 * Q := by rw [hΔ]; ring
    rw [this]
    linarith
  -- compare Q with target
  have hQv : Q ≤ 4 * (v * LIE.E c v * ℓ) := by
    have h1 : w0 * e0 ≤ 2 * v * LIE.E c (2 * v) := hmono w0 (2 * v) (by linarith) hw0v
    have h2 : LIE.E c (2 * v) ≤ LIE.E c v := hanti v (2 * v) hvW (by linarith)
    have h3 : lw ≤ 2 * ℓ := by
      have := Real.log_le_log hw0pos hw0v
      rw [Real.log_mul (by norm_num) hv0.ne', hv, Real.log_sqrt hxl0.le,
        Real.log_mul hx0.ne' (by linarith)] at this
      have : Real.log ℓ ≤ ℓ - 1 := Real.log_le_sub_one_of_pos (by linarith)
      linarith
    have hEv : 0 ≤ LIE.E c v := (LIE.E_pos c v).le
    have h5 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 2 * v)
    have h4 : w0 * e0 ≤ 2 * (v * LIE.E c v) := by linarith
    rw [hQ]
    have := mul_le_mul h4 h3 (by linarith) (by positivity)
    linarith
  have hfin : |Real.log (landau n) - w0| ≤ (D + 4 * Kθ + 4) * Q := by
    rw [abs_le]; constructor
    · have : (D + Kθ) * Q ≤ (D + 4 * Kθ + 4) * Q := by nlinarith only [hQ0, hKθ]
      linarith
    · linarith
  refine hfin.trans ?_
  have hc0 : 0 ≤ D + 4 * Kθ + 4 := by positivity
  have := mul_le_mul_of_nonneg_left hQv hc0
  rw [hD] at this ⊢
  linarith

end LIP

end

-- ===== LI/Main =====
section

open Finset Real Filter Topology LandauFunction

theorem solution (c : ℝ) (hc : 0 < c)
    (hπ : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x) =O[Filter.atTop]
      (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((3 : ℝ) / 5) *
        Real.log (Real.log x) ^ (-(1 : ℝ) / 5)))) :
    (fun n : ℕ => Real.log (landau n) - Real.sqrt (logIntegralInv n)) =O[Filter.atTop]
      (fun n : ℕ =>
        (Real.sqrt (n * Real.log n) *
          Real.exp (-c * Real.log (Real.sqrt (n * Real.log n)) ^ ((3 : ℝ) / 5) *
            Real.log (Real.log (Real.sqrt (n * Real.log n))) ^ (-(1 : ℝ) / 5))) *
        Real.log n) := by
  obtain ⟨C, hC0, hCw⟩ := hπ.exists_nonneg
  obtain ⟨T1, hT1⟩ := eventually_atTop.1 hCw.bound
  have hπ' : ∀ x : ℝ, max T1 0 ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x| ≤ C * (x * LIE.E c x) := by
    intro x hx
    have h := hT1 x (le_trans (le_max_left _ _) hx)
    have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    have e : x * Real.exp (-c * Real.log x ^ ((3 : ℝ) / 5) * Real.log (Real.log x) ^ (-(1 : ℝ) / 5))
        = x * LIE.E c x := rfl
    rw [e, abs_of_nonneg (mul_nonneg hx0 (LIE.E_pos c x).le)] at h
    exact h
  obtain ⟨Kθ, Tθ, hKθ, hTθ, hθ⟩ := LIT.theta_bound c hc C (max T1 0) hC0 hπ'
  obtain ⟨KS, TS, hKS, hTS, hS⟩ := LIS.S_bound c hc Kθ Tθ hKθ hTθ hθ
  obtain ⟨Tm, hTm1, hmono⟩ := LIE.xE_mono c hc
  obtain ⟨Tb, hTb1, hbig⟩ := LIE.E_big c
  obtain ⟨Te, hTe1, hsmall⟩ := LIE.E_log_small c hc (1 / (2 * (8 * KS + 1))) (by positivity)
  set W := max (max (max Tθ TS) (max Tm Tb)) (max Te (max (Real.exp (Real.exp 1)) 4)) with hW
  have hW4 : 4 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have g1 : Tθ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have g2 : TS ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have g3 : Tm ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have g4 : Tb ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have g5 : Te ≤ W := le_trans (le_max_left _ _) (le_max_right _ _)
  have g6 : Real.exp (Real.exp 1) ≤ W :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  refine Asymptotics.IsBigO.of_bound (4 * ((8 * KS + 1) + 4 * Kθ + 4)) ?_
  have hev : ∀ᶠ n : ℕ in atTop, max (8 * W ^ 2) 8 ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hev] with n hn
  have hp := LIP.pointwise c KS Kθ W hKS hKθ hW4
    (fun x hx => hθ x (le_trans g1 hx)) (fun x hx => hS x (le_trans g2 hx))
    (fun x y hx hxy => hmono x y (le_trans g3 hx) hxy)
    (fun x y hx hxy => LIE.E_anti c hc x y (le_trans g6 hx) hxy)
    (fun x hx => hbig x (le_trans g4 hx)) (fun x hx => hsmall x (le_trans g5 hx))
    n (le_trans (le_max_left _ _) hn) (le_trans (le_max_right _ _) hn)
  have hn1 : (1:ℝ) ≤ n := le_trans (by norm_num) (le_trans (le_max_right _ _) hn)
  have hl0 : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have e : (Real.sqrt (n * Real.log n) *
          Real.exp (-c * Real.log (Real.sqrt (n * Real.log n)) ^ ((3 : ℝ) / 5) *
            Real.log (Real.log (Real.sqrt (n * Real.log n))) ^ (-(1 : ℝ) / 5))) * Real.log n
      = √(n * Real.log n) * LIE.E c (√(n * Real.log n)) * Real.log n := rfl
  rw [e, abs_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (LIE.E_pos c _).le) hl0)]
  exact hp

end
