-- Prove2me | solution 1 for HeymanStidham.HLG.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:27:10.41959+00:00
-- url     : https://prove2.me/submissions/7dd6c598-bfc1-4810-805a-c42a20390f21

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting
import Theorems.Thm_HeymanStidham_HLG_eq3_sandwich
import Theorems.Thm_HeymanStidham_HLG_eq4_lambda_G
import Theorems.Thm_HeymanStidham_HLG_s_div_t_tendsto_zero
import Theorems.Thm_HeymanStidham_HLG_U_V_same_limit

open Filter Topology MeasureTheory

open HeymanStidham.HLG in
/-- Arrival epochs tend to infinity when the arrival rate is positive. -/
private lemma hlg1_tendsto_t (t : ℕ → ℝ) (ht : Monotone t) (lam : ℝ) (hlam : 0 < lam)
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

open HeymanStidham.HLG in
theorem solution (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (f : ℕ → ℝ → ℝ) (s : ℕ → ℝ) (hI : CondI t f s) (hII : CondII s)
    (lam : ℝ) (hlam : 0 < lam) (hrate : IsArrivalRate t lam)
    (hiii : ∀ n τ, 0 ≤ τ → 0 ≤ f n τ)
    (hiv : ∀ n, IntegrableOn (f n) (Set.Ici 0))
    (G : ℝ) (hG : IsCustomerAverage (custTotal f) G) :
    IsTimeAverage (rate f) (lam * G) := by
  have htinf := hlg1_tendsto_t t ht lam hlam hrate
  have hg0 : ∀ n, 0 ≤ custTotal f n := fun n =>
    setIntegral_nonneg measurableSet_Ici (fun τ hτ => hiii n τ hτ)
  have hst := s_div_t_tendsto_zero t ht ht0 s hII lam hlam hrate
  have hU := eq4_lambda_G t ht ht0 (custTotal f) lam hlam hrate G hG
  have hV := U_V_same_limit t ht ht0 (custTotal f) hg0 s hI.1 hst lam hlam hrate G hG
  refine ⟨fun T hT => (eq3_sandwich t ht ht0 htinf f s hI hiii hiv T hT).1, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hV hU ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    exact div_le_div_of_nonneg_right
      (eq3_sandwich t ht ht0 htinf f s hI hiii hiv T hT.le).2.1 hT.le
  · filter_upwards [eventually_gt_atTop 0] with T hT
    exact div_le_div_of_nonneg_right
      (eq3_sandwich t ht ht0 htinf f s hI hiii hiv T hT.le).2.2 hT.le
