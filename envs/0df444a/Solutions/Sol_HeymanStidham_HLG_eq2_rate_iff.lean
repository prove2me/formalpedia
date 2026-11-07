-- Prove2me | solution 1 for HeymanStidham.HLG.eq2_rate_iff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:34:11.877555+00:00
-- url     : https://prove2.me/submissions/31d4f5af-e3cd-459d-8d59-3097c580dfca

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace Aux_HLG_EQ2
open HeymanStidham.HLG

theorem tendsto_t (t : ℕ → ℝ) (ht : Monotone t) (lam : ℝ) (hlam : 0 < lam)
    (hrate : IsArrivalRate t lam) : Tendsto t atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone ht ?_
  intro b
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ᶠ T : ℝ in atTop, (arrivalCount t T : ℝ) / T = 0 := by
    filter_upwards [eventually_ge_atTop b] with T hT
    have hset : {n : ℕ | t n ≤ T} = Set.univ := by
      ext n; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (hcon n).le.trans hT
    simp [arrivalCount, hset, Set.Infinite.ncard Set.infinite_univ]
  have h0 : Tendsto (fun T : ℝ => (arrivalCount t T : ℝ) / T) atTop (𝓝 0) :=
    (tendsto_congr' hzero).mpr tendsto_const_nhds
  exact hlam.ne' (tendsto_nhds_unique hrate h0)

theorem finite_le (t : ℕ → ℝ) (htinf : Tendsto t atTop atTop) (T : ℝ) :
    {n : ℕ | t n ≤ T}.Finite := by
  obtain ⟨K, hK⟩ := (htinf.eventually_gt_atTop T).exists_forall_of_atTop
  refine (Set.finite_Iio K).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iio]
  by_contra h
  push_neg at h
  linarith [hK n h]

theorem mem_iff (t : ℕ → ℝ) (ht : Monotone t) (htinf : Tendsto t atTop atTop) (T : ℝ)
    (n : ℕ) : t n ≤ T ↔ n < arrivalCount t T := by
  have hfin := finite_le t htinf T
  unfold arrivalCount
  constructor
  · intro hn
    have hsub : ((Finset.range (n + 1) : Finset ℕ) : Set ℕ) ⊆ {k : ℕ | t k ≤ T} := by
      intro k hk
      simp only [Finset.coe_range, Set.mem_Iio] at hk
      exact (ht (by omega : k ≤ n)).trans hn
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Finset.card_range] at this
    omega
  · intro hn
    by_contra hnot
    have hsub : {k : ℕ | t k ≤ T} ⊆ ((Finset.range n : Finset ℕ) : Set ℕ) := by
      intro k hk
      simp only [Set.mem_setOf_eq] at hk
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hkn
      push_neg at hkn
      exact hnot ((ht hkn).trans hk)
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Finset.card_range] at this
    omega

end Aux_HLG_EQ2

open HeymanStidham.HLG Aux_HLG_EQ2 in
theorem solution (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (lam : ℝ) (hlam : 0 < lam) :
    IsArrivalRate t lam ↔ Tendsto (fun n : ℕ => t n / ((n : ℝ) + 1)) atTop (𝓝 lam⁻¹) := by
  constructor
  · intro hrate
    have htinf := tendsto_t t ht lam hlam hrate
    -- r n = (n+1)/t n → λ
    have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / t n) atTop (𝓝 lam) := by
      have hup : Tendsto (fun n => (arrivalCount t (t n) : ℝ) / t n) atTop (𝓝 lam) :=
        hrate.comp htinf
      have hlow : Tendsto (fun n => (arrivalCount t (t n - 1) : ℝ) / (t n - 1) *
          (1 - 1 / t n)) atTop (𝓝 (lam * (1 - 0))) := by
        refine (hrate.comp ?_).mul (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop htinf))
        exact tendsto_atTop_add_const_right _ (-1) htinf
      rw [sub_zero, mul_one] at hlow
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
      · filter_upwards [htinf.eventually_gt_atTop 1] with n hn
        have h1 : (arrivalCount t (t n - 1) : ℝ) ≤ n := by
          have : ¬ (n < arrivalCount t (t n - 1)) := by
            rw [← mem_iff t ht htinf]; linarith
          exact_mod_cast (not_lt.1 this)
        have e : (arrivalCount t (t n - 1) : ℝ) / (t n - 1) * (1 - 1 / t n) =
            (arrivalCount t (t n - 1) : ℝ) / t n := by
          field_simp
        rw [e]
        exact div_le_div_of_nonneg_right (by linarith) (by linarith)
      · filter_upwards [htinf.eventually_gt_atTop 0] with n hn
        refine div_le_div_of_nonneg_right ?_ hn.le
        have : n < arrivalCount t (t n) := (mem_iff t ht htinf (t n) n).1 le_rfl
        have : (n : ℝ) + 1 ≤ (arrivalCount t (t n) : ℝ) := by exact_mod_cast this
        exact this
    have := hr.inv₀ hlam.ne'
    refine this.congr' ?_
    filter_upwards with n
    simp [inv_div]
  · intro h
    have hlinv : 0 < lam⁻¹ := inv_pos.2 hlam
    -- t n → ∞
    have htinf : Tendsto t atTop atTop := by
      have hn1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      refine (Tendsto.pos_mul_atTop hlinv h hn1).congr' ?_
      filter_upwards with n
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      field_simp
    have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / t n) atTop (𝓝 lam) := by
      have := h.inv₀ hlinv.ne'
      rw [inv_inv] at this
      refine this.congr' ?_
      filter_upwards with n
      simp [inv_div]
    -- N(T) → ∞
    have hN : Tendsto (fun T : ℝ => arrivalCount t T) atTop atTop := by
      rw [tendsto_atTop]
      intro m
      filter_upwards [eventually_ge_atTop (t m)] with T hT
      have := (mem_iff t ht htinf T m).1 hT
      omega
    have hN1 : Tendsto (fun T : ℝ => arrivalCount t T - 1) atTop atTop :=
      (tendsto_sub_atTop_nat 1).comp hN
    have hfrac : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 1) :=
      tendsto_natCast_div_add_atTop 1
    have hlow : Tendsto (fun T : ℝ => ((arrivalCount t T : ℝ) + 1) / t (arrivalCount t T) *
        ((arrivalCount t T : ℝ) / ((arrivalCount t T : ℝ) + 1))) atTop (𝓝 (lam * 1)) :=
      (hr.comp hN).mul (hfrac.comp hN)
    rw [mul_one] at hlow
    have hup : Tendsto (fun T : ℝ => (((arrivalCount t T - 1 : ℕ) : ℝ) + 1) /
        t (arrivalCount t T - 1)) atTop (𝓝 lam) := hr.comp hN1
    have hpos := htinf.eventually_gt_atTop 0
    obtain ⟨K, hK⟩ := hpos.exists_forall_of_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hN.eventually_ge_atTop (K + 1), eventually_gt_atTop 0] with T hT hT0
      set M := arrivalCount t T with hM
      have hMT : T < t M := by
        have : ¬ (M < arrivalCount t T) := lt_irrefl _
        rw [← mem_iff t ht htinf] at this
        exact not_le.1 this
      have htM : 0 < t M := hK M (by omega)
      have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
      have e : ((M : ℝ) + 1) / t M * ((M : ℝ) / ((M : ℝ) + 1)) = (M : ℝ) / t M := by
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hT0 hMT.le
    · filter_upwards [hN.eventually_ge_atTop (K + 1), eventually_gt_atTop 0] with T hT hT0
      set M := arrivalCount t T with hM
      have hMle : t (M - 1) ≤ T := by
        rw [mem_iff t ht htinf]; omega
      have htM : 0 < t (M - 1) := hK (M - 1) (by omega)
      have hcast : (((M - 1 : ℕ) : ℝ) + 1) = (M : ℝ) := by
        have : 1 ≤ M := by omega
        rw [Nat.cast_sub this]; ring
      rw [hcast]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) htM hMle
