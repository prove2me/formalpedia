-- Prove2me | solution 1 for HeymanStidham.HLG.U_V_same_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:31:32.997193+00:00
-- url     : https://prove2.me/submissions/ea0dbe4f-c5b8-4d28-bce4-80c6d614529a

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace Aux_HLG_UV
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

theorem arrived_eq (t : ℕ → ℝ) (ht : Monotone t) (htinf : Tendsto t atTop atTop)
    (a : ℕ → ℝ) (T : ℝ) :
    arrivedTotal t a T = ∑ n ∈ Finset.range (arrivalCount t T), a n := by
  unfold arrivedTotal
  rw [tsum_eq_sum (s := Finset.range (arrivalCount t T))]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_range, ← mem_iff t ht htinf T n] at hn
    simp [Set.indicator_of_mem (show n ∈ {k : ℕ | t k ≤ T} from hn)]
  · intro n hn
    rw [Finset.mem_range, ← mem_iff t ht htinf T n] at hn
    exact Set.indicator_of_notMem (show n ∉ {k : ℕ | t k ≤ T} from hn) _

theorem eq4 (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (a : ℕ → ℝ) (lam : ℝ) (hlam : 0 < lam) (hrate : IsArrivalRate t lam)
    (G : ℝ) (hG : IsCustomerAverage a G) :
    Tendsto (fun T : ℝ => arrivedTotal t a T / T) atTop (𝓝 (lam * G)) := by
  have htinf := tendsto_t t ht lam hlam hrate
  -- N(T) → ∞
  have hNr : Tendsto (fun T : ℝ => (arrivalCount t T : ℝ)) atTop atTop := by
    have h := Tendsto.pos_mul_atTop hlam hrate tendsto_id
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [Pi.mul_apply, id]
    field_simp
  have hN : Tendsto (fun T : ℝ => arrivalCount t T) atTop atTop :=
    tendsto_natCast_atTop_iff.mp hNr
  have hGc := hG.comp hN
  have hprod := hrate.mul hGc
  refine hprod.congr' ?_
  filter_upwards [hNr.eventually_gt_atTop 0, eventually_gt_atTop 0] with T hNT hT
  simp only [Function.comp_apply]
  rw [arrived_eq t ht htinf a T]
  field_simp

theorem summ_ind (S : Set ℕ) (hS : S.Finite) (a : ℕ → ℝ) : Summable (S.indicator a) :=
  summable_of_finite_support (hS.subset (Set.support_indicator_subset))

end Aux_HLG_UV

open HeymanStidham.HLG Aux_HLG_UV in
theorem solution (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (hst : Tendsto (fun n : ℕ => s n / t n) atTop (𝓝 0))
    (lam : ℝ) (hlam : 0 < lam) (hrate : IsArrivalRate t lam)
    (G : ℝ) (hG : IsCustomerAverage a G) :
    Tendsto (fun T : ℝ => finishedTotal t s a T / T) atTop (𝓝 (lam * G)) := by
  have htinf := tendsto_t t ht lam hlam hrate
  have hU := eq4 t ht ht0 a lam hlam hrate G hG
  have htn0 : ∀ n, 0 ≤ t n := fun n => ht0.trans (ht (Nat.zero_le n))
  have hBsub : ∀ T, {n : ℕ | t n + s n ≤ T} ⊆ {n : ℕ | t n ≤ T} := by
    intro T n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    linarith [hs n]
  have hBfin : ∀ T, {n : ℕ | t n + s n ≤ T}.Finite := fun T =>
    (finite_le t htinf T).subset (hBsub T)
  -- V(T) ≤ U(T)
  have hVU : ∀ T, finishedTotal t s a T ≤ arrivedTotal t a T := by
    intro T
    unfold finishedTotal arrivedTotal
    exact Summable.tsum_le_tsum
      (fun n => Set.indicator_le_indicator_of_subset (hBsub T) ha n)
      (summ_ind _ (hBfin T) a) (summ_ind _ (finite_le t htinf T) a)
  rw [tendsto_order]
  refine ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
  · -- lower bound
    have hcont : Tendsto (fun e : ℝ => lam * G / (1 + e)) (𝓝[>] 0) (𝓝 (lam * G)) := by
      have : Tendsto (fun e : ℝ => lam * G / (1 + e)) (𝓝 0) (𝓝 (lam * G / (1 + 0))) :=
        tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_id) (by norm_num)
      simpa using this.mono_left nhdsWithin_le_nhds
    obtain ⟨ε, hεa, hε⟩ :=
      ((hcont.eventually (lt_mem_nhds ha')).and self_mem_nhdsWithin).exists
    have hε0 : 0 < ε := hε
    obtain ⟨n0, hn0⟩ := ((hst.eventually (gt_mem_nhds hε0)).and
      (htinf.eventually_gt_atTop 0)).exists_forall_of_atTop
    set C := ∑ n ∈ Finset.range n0, a n with hC
    -- U(T/(1+ε)) ≤ V(T) + C
    have hkey : ∀ T, 0 ≤ T → arrivedTotal t a (T / (1 + ε)) ≤ finishedTotal t s a T + C := by
      intro T hT
      have hR : ∑' n, ((Finset.range n0 : Finset ℕ) : Set ℕ).indicator a n = C := by
        rw [tsum_eq_sum (s := Finset.range n0)]
        · refine Finset.sum_congr rfl (fun n hn => ?_)
          exact Set.indicator_of_mem (by simpa using hn) _
        · intro n hn
          exact Set.indicator_of_notMem (by simpa using hn) _
      unfold arrivedTotal finishedTotal
      rw [← hR, ← Summable.tsum_add (summ_ind _ (hBfin T) a)
        (summ_ind _ (Finset.finite_toSet _) a)]
      refine Summable.tsum_le_tsum (fun n => ?_)
        (summ_ind _ (finite_le t htinf _) a)
        ((summ_ind _ (hBfin T) a).add (summ_ind _ (Finset.finite_toSet _) a))
      by_cases hA : n ∈ {k : ℕ | t k ≤ T / (1 + ε)}
      · rw [Set.indicator_of_mem hA]
        by_cases hn : n < n0
        · rw [Set.indicator_of_mem (show n ∈ ((Finset.range n0 : Finset ℕ) : Set ℕ) by
            simpa using hn)]
          have := Set.indicator_nonneg (fun k _ => ha k) n
            (s := {k : ℕ | t k + s k ≤ T})
          linarith
        · push_neg at hn
          obtain ⟨h1, h2⟩ := hn0 n hn
          have hsn : s n < ε * t n := by
            have := (div_lt_iff₀ h2).1 h1
            linarith
          have hmem : n ∈ {k : ℕ | t k + s k ≤ T} := by
            simp only [Set.mem_setOf_eq] at hA ⊢
            have : (1 + ε) * t n ≤ T := by
              rw [le_div_iff₀ (by linarith)] at hA; linarith
            nlinarith
          rw [Set.indicator_of_mem hmem]
          have := Set.indicator_nonneg (fun k _ => ha k) n
            (s := ((Finset.range n0 : Finset ℕ) : Set ℕ))
          linarith
      · rw [Set.indicator_of_notMem hA]
        have h1 := Set.indicator_nonneg (fun k _ => ha k) n (s := {k : ℕ | t k + s k ≤ T})
        have h2 := Set.indicator_nonneg (fun k _ => ha k) n
          (s := ((Finset.range n0 : Finset ℕ) : Set ℕ))
        linarith
    -- the lower comparison function
    have h1ε : (0 : ℝ) < 1 + ε := by linarith
    have hW : Tendsto (fun T : ℝ =>
        arrivedTotal t a (T / (1 + ε)) / (T / (1 + ε)) / (1 + ε) - C / T) atTop
        (𝓝 (lam * G / (1 + ε) - 0)) := by
      refine Tendsto.sub ?_ (tendsto_const_nhds.div_atTop tendsto_id)
      exact (hU.comp (tendsto_id.atTop_div_const h1ε)).div_const _
    rw [sub_zero] at hW
    filter_upwards [hW.eventually (lt_mem_nhds hεa), eventually_gt_atTop 0] with T hT hT0
    refine lt_of_lt_of_le hT ?_
    have e : arrivedTotal t a (T / (1 + ε)) / (T / (1 + ε)) / (1 + ε) - C / T =
        (arrivedTotal t a (T / (1 + ε)) - C) / T := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith [hkey T hT0.le]) hT0.le
  · -- upper bound
    filter_upwards [hU.eventually (gt_mem_nhds ha'), eventually_gt_atTop 0] with T hT hT0
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (hVU T) hT0.le) hT
