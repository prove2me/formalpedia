-- Prove2me | solution 1 for KallenbergLP.Constrained.freq_eq_abel_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:36:13.031132+00:00
-- url     : https://prove2.me/submissions/c10f7b1e-df2b-471b-b161-88ec0a9a814d

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies

open Filter Topology

namespace KallenbergLP.Constrained

theorem abel_identity (a : ℕ → ℝ) (C : ℝ) (ha : ∀ k, |a k| ≤ C) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    (∑' k, α ^ k * a k) * (1 - α)⁻¹ = ∑' n, α ^ n * ∑ k ∈ Finset.range (n + 1), a k := by
  have hn : ‖α‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hf : Summable (fun k => ‖α ^ k * a k‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one h0 h1).mul_left C)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 k), mul_comm]
    exact mul_le_mul_of_nonneg_right (ha k) (pow_nonneg h0 k)
  have hg : Summable (fun m => ‖α ^ m‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0, abs_pow] using summable_geometric_of_lt_one h0 h1
  rw [← tsum_geometric_of_lt_one h0 h1, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg]
  congr 1; ext n
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc α ^ k * a k * α ^ (n - k) = α ^ (k + (n - k)) * a k := by rw [pow_add]; ring
    _ = α ^ n * a k := by rw [Nat.add_sub_cancel' hkn]

theorem sum_succ_geom {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * α ^ n) ((1 - α) ^ 2)⁻¹ := by
  have hn : ‖α‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have s1 : Summable (fun n : ℕ => (n : ℝ) * α ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h := (s1.hasSum).add (hasSum_geometric_of_lt_one h0 h1)
  rw [tsum_coe_mul_geometric_of_norm_lt_one hn] at h
  have hne : (1 - α) ≠ 0 := by linarith
  convert h using 1
  · ext n; ring
  · field_simp; ring

theorem abel_of_cesaro (a : ℕ → ℝ) (C : ℝ) (ha : ∀ k, |a k| ≤ C) (L : ℝ)
    (h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), a k) atTop (𝓝 L)) :
    Tendsto (fun α : ℝ => (1 - α) * ∑' k : ℕ, α ^ k * a k) (𝓝[<] 1) (𝓝 L) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (ha 0)
  set C' := C + |L| with hC'
  have hC'0 : 0 ≤ C' := by positivity
  -- bound on the Cesaro means
  have hu : ∀ n : ℕ, |((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), a k - L| ≤ C' := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hs : |∑ k ∈ Finset.range (n + 1), a k| ≤ ((n : ℝ) + 1) * C := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum (fun k _ => ha k)).trans ?_
      simp
    have : |((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), a k| ≤ C := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
      rw [inv_mul_le_iff₀ hpos]; exact hs
    calc _ ≤ |((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), a k| + |L| := abs_sub _ _
      _ ≤ C' := by rw [hC']; linarith
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  set K : ℝ := ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * C' + 1 with hK
  have hK0 : 0 < K := by
    have : 0 ≤ ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * C' :=
      Finset.sum_nonneg (fun n _ => by positivity)
    linarith
  refine ⟨min 1 (ε / (2 * K)), by positivity, ?_⟩
  intro α hα hdist
  have hα1 : α < 1 := hα
  rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)] at hdist
  have hdist1 : 1 - α < 1 := lt_of_lt_of_le hdist (min_le_left _ _)
  have hdist2 : 1 - α < ε / (2 * K) := lt_of_lt_of_le hdist (min_le_right _ _)
  have h0 : 0 ≤ α := by linarith
  have hpos : 0 < 1 - α := by linarith
  have hn : ‖α‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact hα1
  set c : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), a k - L with hc
  have hS : ∀ n, α ^ n * ∑ k ∈ Finset.range (n + 1), a k
      = ((n : ℝ) + 1) * α ^ n * c n + L * (((n : ℝ) + 1) * α ^ n) := by
    intro n
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [hc]; field_simp; ring
  have hG := sum_succ_geom h0 hα1
  have hw : Summable (fun n : ℕ => ((n : ℝ) + 1) * α ^ n * c n) := by
    refine Summable.of_norm_bounded (hG.summable.mul_left C') (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    have := hu n
    nlinarith [show 0 ≤ ((n : ℝ) + 1) * α ^ n by positivity]
  have hid := abel_identity a C ha h0 hα1
  have hsum : ∑' n, α ^ n * ∑ k ∈ Finset.range (n + 1), a k
      = ∑' n : ℕ, ((n : ℝ) + 1) * α ^ n * c n + L * ((1 - α) ^ 2)⁻¹ := by
    rw [tsum_congr hS, Summable.tsum_add hw (hG.summable.mul_left L), tsum_mul_left, hG.tsum_eq]
  set T := ∑' k, α ^ k * a k
  set W := ∑' n : ℕ, ((n : ℝ) + 1) * α ^ n * c n
  have hne : (1 - α) ≠ 0 := hpos.ne'
  have hT : (1 - α) * T - L = (1 - α) ^ 2 * W := by
    have h2 : T = (1 - α) * (W + L * ((1 - α) ^ 2)⁻¹) := by
      rw [← hsum, ← hid]; field_simp
    rw [h2]; field_simp; ring
  -- bound W
  have hwabs : Summable (fun n : ℕ => |((n : ℝ) + 1) * α ^ n * c n|) := hw.abs
  have hfin : HasSum (fun n : ℕ => if n < N then ((n : ℝ) + 1) * C' else 0)
      (∑ n ∈ Finset.range N, ((n : ℝ) + 1) * C') := by
    have : HasSum (fun n : ℕ => if n < N then ((n : ℝ) + 1) * C' else 0)
        (∑ b ∈ Finset.range N, (fun n : ℕ => if n < N then ((n : ℝ) + 1) * C' else 0) b) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by simp only [Finset.mem_range] at hb; simp [hb])
    convert this using 1
    refine Finset.sum_congr rfl (fun n hn => ?_)
    simp [Finset.mem_range.mp hn]
  have hbound : ∀ n : ℕ, |((n : ℝ) + 1) * α ^ n * c n|
      ≤ (ε / 2) * (((n : ℝ) + 1) * α ^ n) + (if n < N then ((n : ℝ) + 1) * C' else 0) := by
    intro n
    have hp : 0 ≤ ((n : ℝ) + 1) * α ^ n := by positivity
    rw [abs_mul, abs_of_nonneg hp]
    by_cases hnN : n < N
    · rw [if_pos hnN]
      have hαn : α ^ n ≤ 1 := pow_le_one₀ h0 hα1.le
      have := hu n
      have h3 : ((n : ℝ) + 1) * α ^ n * |c n| ≤ ((n : ℝ) + 1) * C' := by
        calc ((n : ℝ) + 1) * α ^ n * |c n| ≤ ((n : ℝ) + 1) * 1 * C' := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hαn (by positivity)) this
                (abs_nonneg _) (by positivity)
          _ = _ := by ring
      nlinarith [mul_nonneg (show (0:ℝ) ≤ ε / 2 by positivity) hp]
    · rw [if_neg hnN]
      have hcn : |c n| < ε / 2 := by
        have := hN n (by omega)
        rwa [Real.dist_eq] at this
      nlinarith [mul_le_mul_of_nonneg_left hcn.le hp]
  have hWle : |W| ≤ (ε / 2) * ((1 - α) ^ 2)⁻¹ + ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * C' := by
    calc |W| ≤ ∑' n : ℕ, |((n : ℝ) + 1) * α ^ n * c n| := by
          have := norm_tsum_le_tsum_norm (f := fun n : ℕ => ((n : ℝ) + 1) * α ^ n * c n)
            (by simpa [Real.norm_eq_abs] using hwabs)
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∑' n : ℕ, ((ε / 2) * (((n : ℝ) + 1) * α ^ n) + (if n < N then ((n : ℝ) + 1) * C' else 0)) :=
          Summable.tsum_le_tsum hbound hwabs ((hG.summable.mul_left _).add hfin.summable)
      _ = _ := by
          rw [Summable.tsum_add (hG.summable.mul_left _) hfin.summable, tsum_mul_left,
            hG.tsum_eq, hfin.tsum_eq]
  rw [Real.dist_eq, hT, abs_mul, abs_of_nonneg (by positivity)]
  have hq : 0 < (1 - α) ^ 2 := by positivity
  calc (1 - α) ^ 2 * |W| ≤ (1 - α) ^ 2 * ((ε / 2) * ((1 - α) ^ 2)⁻¹
          + ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * C') := mul_le_mul_of_nonneg_left hWle hq.le
    _ = ε / 2 + (1 - α) ^ 2 * (K - 1) := by
          have hKe : ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * C' = K - 1 := by rw [hK]; ring
          rw [hKe]; field_simp
    _ < ε := by
      have h4 : (1 - α) ^ 2 ≤ 1 - α := by nlinarith
      have h5 : (1 - α) * K < ε / 2 := by
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * K)] at hdist2
        linarith
      nlinarith



open MarkovDecisionProcesses

theorem fa_q_le_one {S A : Type*} [Fintype S] [Fintype A] {M : StationaryMDP S A}
    (R : AvgHRPolicy M) (t : ℕ) (h : List (S × A)) (s : S) (a : A) (ha : a ∈ M.admissible s) :
    R.q t h s a ≤ 1 := by
  rw [← R.sum_one t h s]
  exact Finset.single_le_sum (f := fun b => R.q t h s b) (fun b _ => R.nonneg t h s b) ha

theorem fa_occ_bounds {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] {M : StationaryMDP S A} (R : AvgHRPolicy M) (k : ℕ) :
    ∀ t h s p, 0 ≤ occ R k t h s p ∧ occ R k t h s p ≤ 1 := by
  induction k with
  | zero =>
    intro t h s p
    simp only [occ]
    split_ifs with hp
    · refine ⟨R.nonneg _ _ _ _, fa_q_le_one R _ _ _ _ ?_⟩
      rw [← hp]; exact p.2
    · exact ⟨le_rfl, zero_le_one⟩
  | succ k ih =>
    intro t h s p
    simp only [occ]
    constructor
    · refine Finset.sum_nonneg (fun b _ => mul_nonneg (R.nonneg _ _ _ _) ?_)
      exact Finset.sum_nonneg (fun s' _ => mul_nonneg (M.trans_nonneg _ _ _) (ih _ _ _ _).1)
    · calc _ ≤ ∑ b ∈ M.admissible s, R.q t h s b * 1 := by
            refine Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left ?_ (R.nonneg _ _ _ _))
            calc _ ≤ ∑ s', M.trans s b s' * 1 :=
                  Finset.sum_le_sum (fun s' _ =>
                    mul_le_mul_of_nonneg_left (ih _ _ _ _).2 (M.trans_nonneg _ _ _))
              _ = 1 := by simp [M.trans_sum]
        _ = 1 := by simp [R.sum_one]

theorem fa_a_bounds {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] {M : StationaryMDP S A} (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) (R : AvgHRPolicy M) (k : ℕ) (p : KallenbergLP.AverageLP.Pair M) :
    0 ≤ ∑ i, β i * prob R k i p ∧ ∑ i, β i * prob R k i p ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hβ0 i) (fa_occ_bounds R k _ _ _ _).1)
  · calc _ ≤ ∑ i, β i * 1 := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (fa_occ_bounds R k _ _ _ _).2 (hβ0 i))
      _ = 1 := by simp [hβ1]

theorem fa_freq_bounds {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] {M : StationaryMDP S A} (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) (R : AvgHRPolicy M) (T : ℕ) (p : KallenbergLP.AverageLP.Pair M) :
    freq β R T p ∈ Set.Icc (0 : ℝ) 1 := by
  unfold freq
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hTp.le)
      (Finset.sum_nonneg (fun k _ => (fa_a_bounds β hβ0 hβ1 R k p).1))
  · rw [inv_mul_le_iff₀ hTp]
    calc _ ≤ ∑ k ∈ Finset.range T, (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => (fa_a_bounds β hβ0 hβ1 R k p).2)
      _ = T * 1 := by simp

theorem fa_tendsto {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] {M : StationaryMDP S A} (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) (R : AvgHRPolicy M) (hR : IsC1 β R)
    (x : KallenbergLP.AverageLP.Pair M → ℝ) (hx : x ∈ limitPoints β R) :
    Tendsto (fun T => freq β R T) atTop (𝓝 x) := by
  obtain ⟨x', hx'⟩ := hR
  have hxx : x = x' := by rw [hx'] at hx; exact hx
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨φ1, hφ1, hφ1'⟩ := Filter.strictMono_subseq_of_tendsto_atTop hns
  have hK : IsCompact (Set.pi Set.univ (fun _ : KallenbergLP.AverageLP.Pair M => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨y, _, φ2, hφ2, hy⟩ := hK.tendsto_subseq (x := fun n => freq β R (ns (φ1 n)))
    (fun n => fun q _ => fa_freq_bounds β hβ0 hβ1 R _ q)
  have hyL : y ∈ limitPoints β R := ⟨(ns ∘ φ1) ∘ φ2, hφ1'.comp hφ2, hy⟩
  rw [hx'] at hyL
  have : y = x := by rw [hxx]; exact hyL
  rw [← this]
  exact ⟨φ1 ∘ φ2, hy⟩

theorem freq_abel_core {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) (R : AvgHRPolicy M) (hR : IsC1 β R)
    (x : KallenbergLP.AverageLP.Pair M → ℝ) (hx : x ∈ limitPoints β R) (p : KallenbergLP.AverageLP.Pair M) :
    Tendsto (fun α : ℝ => (1 - α) * ∑' k : ℕ, α ^ k * ∑ i, β i * prob R k i p)
      (𝓝[<] 1) (𝓝 (x p)) := by
  apply abel_of_cesaro (fun k => ∑ i, β i * prob R k i p) 1
  · intro k
    have := fa_a_bounds β hβ0 hβ1 R k p
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  · have h1 := ((continuous_apply p).tendsto x).comp (fa_tendsto β hβ0 hβ1 R hR x hx)
    have h2 := (tendsto_add_atTop_iff_nat 1).mpr h1
    convert h2 using 1
    ext n
    simp [freq]

end KallenbergLP.Constrained

open KallenbergLP.Constrained
open MarkovDecisionProcesses Filter Topology

theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) (R : AvgHRPolicy M) (hR : IsC1 β R)
    (x : KallenbergLP.AverageLP.Pair M → ℝ) (hx : x ∈ limitPoints β R) (p : KallenbergLP.AverageLP.Pair M) :
    Tendsto (fun α : ℝ => (1 - α) * ∑' k : ℕ, α ^ k * ∑ i, β i * prob R k i p)
      (𝓝[<] 1) (𝓝 (x p)) := by
  exact freq_abel_core M β hβ0 hβ1 R hR x hx p
