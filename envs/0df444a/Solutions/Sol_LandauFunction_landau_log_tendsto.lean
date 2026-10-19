-- Prove2me | solution 1 for LandauFunction.landau_log_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T01:11:49.731103+00:00
-- url     : https://prove2.me/submissions/3e7aa05b-3cd3-4dcf-a502-d082c438b3f5

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_psi_prime_number_theorem
import Definitions.Def_LandauFunction_landau

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

section
open Finset Real Filter Topology
open LandauFunction

namespace LGC
open LGA LGB

noncomputable def X (n : ℕ) : ℝ := Real.sqrt (n * Real.log n)

lemma X_tendsto : Tendsto X atTop atTop := by
  unfold X
  exact Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ log_tendsto)

lemma X_sq {n : ℕ} (hn : 1 ≤ n) : X n ^ 2 = n * Real.log n := by
  unfold X
  rw [Real.sq_sqrt]
  exact mul_nonneg (by positivity) (Real.log_natCast_nonneg n)

lemma logX {n : ℕ} (hn : 3 ≤ n) : Real.log (X n) = (Real.log n + Real.log (Real.log n)) / 2 := by
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  unfold X
  rw [Real.log_sqrt (by positivity), Real.log_mul (by positivity) hl.ne']

/-- For `N = ⌊c X⌋`: `N / X → c` and `log N / log n → 1/2`. -/
lemma floor_lim (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (⌊c * X n⌋₊ : ℝ) / X n) atTop (𝓝 c) ∧
    Tendsto (fun n : ℕ => Real.log (⌊c * X n⌋₊ : ℕ) / Real.log n) atTop (𝓝 (1 / 2)) ∧
    Tendsto (fun n : ℕ => ⌊c * X n⌋₊) atTop atTop := by
  have hcX : Tendsto (fun n => c * X n) atTop atTop := X_tendsto.const_mul_atTop hc
  have h1 : Tendsto (fun n : ℕ => (⌊c * X n⌋₊ : ℝ) / X n) atTop (𝓝 c) := by
    have := (tendsto_nat_floor_div_atTop.comp hcX).const_mul c
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [X_tendsto.eventually_gt_atTop 0] with n hn
    simp only [Function.comp]
    field_simp
  refine ⟨h1, ?_, tendsto_nat_floor_atTop.comp hcX⟩
  have hlog := ((Real.continuousAt_log hc.ne').tendsto.comp h1).div_atTop log_tendsto
  have hll := loglog_tendsto
  have h2 := (hlog.add (tendsto_const_nhds (x := (1 / 2 : ℝ)))).add (hll.const_mul (1 / 2))
  simp only [zero_add, mul_zero, add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 3, (tendsto_nat_floor_atTop.comp hcX).eventually_ge_atTop 1,
    X_tendsto.eventually_gt_atTop 0] with n hn h1n hX
  have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  simp only [Function.comp] at h1n ⊢
  have hN : (0 : ℝ) < (⌊c * X n⌋₊ : ℝ) := by exact_mod_cast h1n
  rw [Real.log_div hN.ne' hX.ne', logX hn]
  field_simp
  ring

theorem main : Tendsto (fun n : ℕ => Real.log (landau n) / Real.sqrt (n * Real.log n)) atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => Real.log (landau n) / X n) atTop (𝓝 1)
  rw [tendsto_order]
  constructor
  · -- lower bound
    intro a ha
    set a' := max a 0 with ha'def
    have ha'1 : a' < 1 := max_lt ha one_pos
    have ha'0 : 0 ≤ a' := le_max_right a 0
    have haa' : a ≤ a' := le_max_left a 0
    set δ := (1 - a') / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hδ0 : 0 < 1 - δ := by rw [hδ]; linarith
    obtain ⟨hN1, hN2, hN3⟩ := floor_lim (1 - δ) hδ0
    set N : ℕ → ℕ := fun n => ⌊(1 - δ) * X n⌋₊ with hNdef
    -- S0 N / n → (1-δ)^2
    have hS : Tendsto (fun n : ℕ => (S0 (N n) * Real.log (N n) / (N n : ℝ) ^ 2) *
        ((N n : ℝ) / X n) ^ 2 * (Real.log n / Real.log (N n))) atTop
        (𝓝 (1 / 2 * (1 - δ) ^ 2 * (1 / 2)⁻¹)) := by
      refine Tendsto.mul (Tendsto.mul (S0_tendsto.comp hN3) (hN1.pow 2)) ?_
      have := hN2.inv₀ (by norm_num)
      refine this.congr' ?_
      filter_upwards with n; simp only [inv_div]; rfl
    have hlim : (1 / 2 * (1 - δ) ^ 2 * (1 / 2)⁻¹ : ℝ) < 1 := by
      have : (1 - δ) ^ 2 < 1 := by nlinarith
      norm_num; linarith
    have hth : Tendsto (fun n : ℕ => th (N n) / N n * ((N n : ℝ) / X n)) atTop (𝓝 (1 * (1 - δ))) :=
      (th_tendsto.comp hN3).mul hN1
    have ha' : a < 1 * (1 - δ) := by rw [hδ]; linarith
    filter_upwards [hS.eventually (gt_mem_nhds hlim), hth.eventually (lt_mem_nhds ha'),
      hN3.eventually_ge_atTop 3, eventually_ge_atTop 3, X_tendsto.eventually_gt_atTop 0] with
      n h1 h2 h3 h4 h5
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hNpos : (0 : ℝ) < N n := by exact_mod_cast (by omega : 0 < N n)
    have hlN : 0 < Real.log (N n) := Real.log_pos (by exact_mod_cast (by omega : 1 < N n))
    have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    -- S0 (N n) ≤ n
    have hS0 : S0 (N n) < n := by
      have e : S0 (N n) * Real.log (N n) / (N n : ℝ) ^ 2 * ((N n : ℝ) / X n) ^ 2 *
          (Real.log n / Real.log (N n)) = S0 (N n) / n := by
        rw [div_pow, X_sq (by omega)]
        field_simp
      rw [e, div_lt_one hn0] at h1
      exact h1
    have hS0n : ∑ p ∈ P (N n), p ≤ n := by
      have : ((∑ p ∈ P (N n), p : ℕ) : ℝ) < n := by
        rw [Nat.cast_sum]; exact hS0
      exact_mod_cast this.le
    have hlow := lower n (N n) hS0n
    have e2 : th (N n) / N n * ((N n : ℝ) / X n) = th (N n) / X n := by field_simp
    rw [e2] at h2
    calc a < th (N n) / X n := h2
      _ ≤ Real.log (landau n) / X n := div_le_div_of_nonneg_right hlow h5.le
  · -- upper bound
    intro b hb
    obtain ⟨hM1, hM2, hM3⟩ := floor_lim 1 one_pos
    set M : ℕ → ℕ := fun n => ⌊1 * X n⌋₊ with hMdef
    have hU : Tendsto (fun n : ℕ => (pc (M n) * Real.log (M n) / M n - S0 (M n) * Real.log (M n) / (M n : ℝ) ^ 2) *
        ((M n : ℝ) / X n) + (Real.log (M n) / Real.log n) * (X n / M n)) atTop
        (𝓝 ((1 - 1 / 2) * 1 + 1 / 2 * (1 : ℝ)⁻¹)) := by
      refine Tendsto.add (Tendsto.mul (Tendsto.sub (pc_tendsto.comp hM3) (S0_tendsto.comp hM3)) hM1)
        (Tendsto.mul hM2 ?_)
      have := hM1.inv₀ one_ne_zero
      refine this.congr' ?_
      filter_upwards with n; simp only [inv_div]; rfl
    have hb' : ((1 - 1 / 2) * 1 + 1 / 2 * (1 : ℝ)⁻¹ : ℝ) < b := by norm_num; linarith
    filter_upwards [hU.eventually (gt_mem_nhds hb'), hM3.eventually_ge_atTop 3, eventually_ge_atTop 3,
      X_tendsto.eventually_gt_atTop 0] with n h1 h3 h4 h5
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hMpos : (0 : ℝ) < M n := by exact_mod_cast (by omega : 0 < M n)
    have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    -- landau n is the lcm of a partition
    obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Nat.Partition n))
      Finset.univ_nonempty (fun p => p.parts.lcm)
    have hg : landau n = p.parts.lcm := by rw [landau_eq_sup, hp]
    have hup := upper p.parts (fun i hi => p.parts_pos hi) (M n) h3
    rw [p.parts_sum, ← hg] at hup
    have e : (pc (M n) * Real.log (M n) / M n - S0 (M n) * Real.log (M n) / (M n : ℝ) ^ 2) *
        ((M n : ℝ) / X n) + (Real.log (M n) / Real.log n) * (X n / M n) =
        (pc (M n) * Real.log (M n) - Real.log (M n) / M n * S0 (M n) + n * Real.log (M n) / M n) / X n := by
      have hX2 := X_sq (n := n) (by omega)
      field_simp
      rw [hX2]
      ring
    rw [e] at h1
    calc Real.log (landau n) / X n ≤
        (pc (M n) * Real.log (M n) - Real.log (M n) / M n * S0 (M n) + n * Real.log (M n) / M n) / X n :=
          div_le_div_of_nonneg_right hup h5.le
      _ < b := h1

end LGC

end

open LandauFunction

theorem solution :
    Filter.Tendsto (fun n : ℕ => Real.log (landau n) / Real.sqrt (n * Real.log n))
      Filter.atTop (nhds 1) :=
  LGC.main
