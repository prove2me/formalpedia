-- Prove2me | solution 1 for NymanBeurling.damped_moebius_finite_head_approximation
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T01:11:51.25643+00:00
-- url     : https://prove2.me/submissions/d30c3774-1093-45e1-a2f4-9ea96cc40565

import Mathlib
import Theorems.Thm_NymanBeurling_moebius_dirichlet_abel_limit

set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators

private lemma floor_sum (m : ℕ) :
    (∑ d ∈ Finset.range (m+1), (ArithmeticFunction.moebius d : ℝ) * (m/d : ℕ)) =
      if m = 0 then 0 else 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hd : (∑ d ∈ Finset.range (m+2),
        if d ∣ m+1 then (ArithmeticFunction.moebius d : ℝ) else 0) =
        if m+1 = 1 then 1 else 0 := by
      rw [← Finset.sum_filter, Nat.filter_dvd_eq_divisors (by omega)]
      have h := congrArg (fun f : ArithmeticFunction ℝ => f (m+1))
        (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
      simpa only [ArithmeticFunction.coe_mul_zeta_apply,
        ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using h
    have ht : (∑ d ∈ Finset.range (m+2),
        (ArithmeticFunction.moebius d : ℝ) * (m/d : ℕ)) =
        ∑ d ∈ Finset.range (m+1), (ArithmeticFunction.moebius d : ℝ) * (m/d : ℕ) := by
      rw [Finset.sum_range_succ]
      simp [Nat.div_eq_of_lt (Nat.lt_succ_self m)]
    simp only [Nat.succ_eq_add_one, Nat.succ_div, Nat.cast_add, mul_add,
      Finset.sum_add_distrib]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero]
    rw [ht, hd, ih]
    split_ifs <;> simp_all <;> omega

private lemma shifted_floor_sum (m : ℕ) (hm : 0 < m) :
    (∑ k ∈ Finset.range m,
      (ArithmeticFunction.moebius (k+2) : ℝ) * (m/(k+2) : ℕ)) = 1 - m := by
  have h := floor_sum m
  have h' : (∑ d ∈ Finset.range (m+2),
      (ArithmeticFunction.moebius d : ℝ) * (m/d : ℕ)) = 1 := by
    rw [Finset.sum_range_succ]
    simpa [Nat.div_eq_of_lt (Nat.lt_succ_self m), ne_of_gt hm] using h
  rw [show m+2 = 2+m by omega, Finset.sum_range_add] at h'
  norm_num [Finset.sum_range_succ] at h'
  simpa only [Nat.add_comm] using (eq_sub_iff_add_eq.mpr (by linarith :
    (∑ x ∈ Finset.range m, (ArithmeticFunction.moebius (2+x) : ℝ) *
      (m/(2+x) : ℕ)) + (m : ℝ) = 1))

private lemma real_term (ε : ℝ) (d : ℕ) :
    (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ))
      (1+(ε : ℂ)) d).re = (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^(1+ε) := by
  by_cases hd : d = 0
  · simp [hd]
  · rw [LSeries.term_of_ne_zero hd]
    have heq : Complex.ofReal ((d : ℝ)^(1+ε)) = (d : ℂ)^(1+(ε : ℂ)) := by
      simpa using Complex.ofReal_cpow (Nat.cast_nonneg d) (1+ε)
    rw [← heq, ← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.ofReal_re]

private lemma partial_series_tendsto (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
      (ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^(1+ε)) atTop
      (𝓝 ((LSeries (fun n => (ArithmeticFunction.moebius n : ℂ))
        (1+(ε : ℂ))).re - 1)) := by
  have hs := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr
    (show 1 < (1+(ε : ℂ)).re by simpa using hε)).LSeriesHasSum
  have hr := Complex.hasSum_re hs
  simp_rw [real_term] at hr
  have ht := hr.tendsto_sum_nat
  have ht' := ht.comp (tendsto_add_atTop_nat 2)
  have heq (N : ℕ) : (∑ d ∈ Finset.range (N+2),
      (ArithmeticFunction.moebius d : ℝ)/(d : ℝ)^(1+ε)) - 1 =
      ∑ k ∈ Finset.range N,
        (ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^(1+ε) := by
    rw [show N+2 = 2+N by omega, Finset.sum_range_add]
    norm_num [Finset.sum_range_succ, Nat.add_comm]
  simpa only [Function.comp_def, heq] using ht'.sub_const 1

private noncomputable def mobiusResidual (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range N,
    ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^ε) * (m % (k+2) : ℕ) /
      (k+2 : ℝ)

private noncomputable def mobiusLimit (ε : ℝ) (m : ℕ) : ℝ :=
  1 + (m : ℝ) * ((LSeries (fun n => (ArithmeticFunction.moebius n : ℂ))
    (1+(ε : ℂ))).re - 1) -
    ∑ k ∈ Finset.range m,
      ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^ε) * (m/(k+2) : ℕ)

private lemma residual_expansion (N m : ℕ) (ε : ℝ) (hN : m ≤ N) :
    mobiusResidual N ε m =
      1 + (m : ℝ) * (∑ k ∈ Finset.range N,
        (ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^(1+ε)) -
        ∑ k ∈ Finset.range m,
          ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^ε) * (m/(k+2) : ℕ) := by
  have hterm (k : ℕ) :
      ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^ε) * (m%(k+2) : ℕ) /
        (k+2 : ℝ) =
      (m : ℝ) * ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^(1+ε)) -
        ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^ε) * (m/(k+2) : ℕ) := by
    have hd : (k+2 : ℝ) ≠ 0 := by positivity
    have hp : (k+2 : ℝ)^ε ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) ε)
    have hm : ((m%(k+2) : ℕ) : ℝ) = (m : ℝ) - (k+2 : ℝ)*(m/(k+2) : ℕ) := by
      have h := Nat.mod_add_div m (k+2)
      have h' : ((m%(k+2) : ℕ) : ℝ) + (k+2 : ℝ)*(m/(k+2) : ℕ) = (m : ℝ) := by
        exact_mod_cast h
      linarith
    rw [hm, Real.rpow_add (by positivity), Real.rpow_one]
    field_simp
    <;> ring
  have hsum : (∑ k ∈ Finset.range N,
      ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^ε) * (m/(k+2) : ℕ)) =
      ∑ k ∈ Finset.range m,
        ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^ε) * (m/(k+2) : ℕ) := by
    symm
    apply Finset.sum_subset (Finset.range_mono hN)
    intro k hk hkm
    have hmk : m < k+2 := by simp only [Finset.mem_range] at hkm; omega
    simp [Nat.div_eq_of_lt hmk]
  simp_rw [mobiusResidual, hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum]
  ring

private lemma residual_tendsto (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => mobiusResidual N ε m) atTop (𝓝 (mobiusLimit ε m)) := by
  have ht := (((partial_series_tendsto ε hε).const_mul (m : ℝ)).const_add 1).sub_const
    (∑ k ∈ Finset.range m,
      ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^ε) * (m/(k+2) : ℕ))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop m] with N hN
  exact (residual_expansion N m ε hN).symm

private lemma limitResidual_tendsto (m : ℕ) (hm : 0 < m) :
    Tendsto (fun ε : ℝ => mobiusLimit ε m) (𝓝[>] 0) (𝓝 0) := by
  have hL := Complex.continuous_re.continuousAt.tendsto.comp
    NymanBeurling.moebius_dirichlet_abel_limit
  have hf (k : ℕ) : Tendsto (fun ε : ℝ =>
      ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^ε) * (m/(k+2) : ℕ))
      (𝓝[>] 0) (𝓝 ((ArithmeticFunction.moebius (k+2) : ℝ) * (m/(k+2) : ℕ))) := by
    have hc : ContinuousAt (fun ε : ℝ => (k+2 : ℝ)^ε) 0 :=
      (Real.continuous_const_rpow (show (k+2 : ℝ) ≠ 0 by positivity)).continuousAt
    have hc' : ContinuousAt (fun ε : ℝ =>
        ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^ε) * (m/(k+2) : ℕ)) 0 :=
      (continuousAt_const.div hc (by simp)).mul continuousAt_const
    simpa using hc'.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hs := tendsto_finset_sum (Finset.range m) (fun k _ => hf k)
  have ht := (((hL.sub_const 1).const_mul (m : ℝ)).const_add 1).sub hs
  simpa [mobiusLimit, shifted_floor_sum m hm] using ht

theorem solution (H : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∑ n ∈ Finset.range H,
          (1 + ∑ k : Fin N,
            ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
              (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
          ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by
  let C (ε : ℝ) := ∑ n ∈ Finset.range H,
    (mobiusLimit ε (n+1))^2 / ((n+1 : ℝ)*(n+2 : ℝ))
  have hc : Tendsto C (𝓝[>] 0) (𝓝 0) := by
    have ht := tendsto_finset_sum (Finset.range H) (fun n _ =>
      ((limitResidual_tendsto (n+1) (by omega)).pow 2).div_const ((n+1 : ℝ)*(n+2 : ℝ)))
    simpa [C] using ht
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C ε < δ := hc.eventually (gt_mem_nhds hδ)
  obtain ⟨ε₀, hε₀, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall
  have hC : C ε < δ := hsmall ⟨hε, hεsmall⟩
  have hcost : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range H,
      (mobiusResidual N ε (n+1))^2 / ((n+1 : ℝ)*(n+2 : ℝ))) atTop (𝓝 (C ε)) :=
    tendsto_finset_sum (Finset.range H) (fun n _ =>
      ((residual_tendsto (n+1) ε hε).pow 2).div_const ((n+1 : ℝ)*(n+2 : ℝ)))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hcost.eventually (gt_mem_nhds hC))
  refine ⟨N₀, fun N hN => ?_⟩
  convert hN₀ N hN using 1
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  congr 3
  exact Fin.sum_univ_eq_sum_range (fun k =>
    ((ArithmeticFunction.moebius (k+2) : ℝ)/(k+2 : ℝ)^ε) *
      ((n+1)%(k+2) : ℕ)/(k+2 : ℝ)) N

