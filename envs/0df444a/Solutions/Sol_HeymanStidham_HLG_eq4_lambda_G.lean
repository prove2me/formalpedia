-- Prove2me | solution 1 for HeymanStidham.HLG.eq4_lambda_G
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:30:22.387529+00:00
-- url     : https://prove2.me/submissions/fc9f5bcf-3847-4747-86e1-235bd0d1b06a

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace Aux_HLG_EQ4
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

end Aux_HLG_EQ4

open HeymanStidham.HLG Aux_HLG_EQ4 in
theorem solution (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
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
