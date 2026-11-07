-- Prove2me | solution 1 for HeymanStidham.HLG.s_div_t_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:29:29.537212+00:00
-- url     : https://prove2.me/submissions/46082a27-d30a-4a03-93c1-91e27a89824e

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace Aux_HLG_SDT
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

theorem count_ge (t : ℕ → ℝ) (ht : Monotone t) (htinf : Tendsto t atTop atTop) (n : ℕ) :
    ((n : ℝ) + 1) ≤ (arrivalCount t (t n) : ℝ) := by
  have hsub : ((Finset.range (n + 1) : Finset ℕ) : Set ℕ) ⊆ {k : ℕ | t k ≤ t n} := by
    intro k hk
    simp only [Finset.coe_range, Set.mem_Iio] at hk
    exact ht (by omega)
  have := Set.ncard_le_ncard hsub (finite_le t htinf (t n))
  rw [Set.ncard_coe_finset, Finset.card_range] at this
  unfold arrivalCount
  exact_mod_cast this

end Aux_HLG_SDT

open HeymanStidham.HLG Aux_HLG_SDT in
theorem solution (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (s : ℕ → ℝ) (hII : CondII s)
    (lam : ℝ) (hlam : 0 < lam) (hrate : IsArrivalRate t lam) :
    Tendsto (fun n : ℕ => s n / t n) atTop (𝓝 0) := by
  have htinf := tendsto_t t ht lam hlam hrate
  -- (n+1)/tₙ ≤ N(tₙ)/tₙ → λ, so (n+1)/tₙ is eventually bounded by λ + 1
  have hcomp : Tendsto (fun n => (arrivalCount t (t n) : ℝ) / t n) atTop (𝓝 lam) :=
    hrate.comp htinf
  have hev : ∀ᶠ n in atTop, 0 < t n ∧ (arrivalCount t (t n) : ℝ) / t n < lam + 1 :=
    (htinf.eventually_gt_atTop 0).and (hcomp.eventually (gt_mem_nhds (by linarith)))
  have hII' : Tendsto (fun n : ℕ => |s n / ((n : ℝ) + 1)| * (lam + 1)) atTop (𝓝 0) := by
    have := (hII.abs).mul_const (lam + 1)
    simpa using this
  refine squeeze_zero_norm' ?_ hII'
  filter_upwards [hev] with n ⟨htn, hb⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc := count_ge t ht htinf n
  have hq : ((n : ℝ) + 1) / t n ≤ lam + 1 := by
    calc ((n : ℝ) + 1) / t n ≤ (arrivalCount t (t n) : ℝ) / t n :=
          div_le_div_of_nonneg_right hc htn.le
      _ ≤ lam + 1 := hb.le
  rw [Real.norm_eq_abs]
  have e : s n / t n = s n / ((n : ℝ) + 1) * (((n : ℝ) + 1) / t n) := by
    field_simp
  rw [e, abs_mul, abs_of_pos (div_pos hn1 htn)]
  exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)
