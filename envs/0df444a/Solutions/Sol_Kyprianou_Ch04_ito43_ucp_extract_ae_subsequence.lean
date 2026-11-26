-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ucp_extract_ae_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:57:21.065659+00:00
-- url     : https://prove2.me/submissions/2919cc66-4ae8-43ff-83dc-bfa011428d82

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (A : ℕ → NNReal → Omega → ℝ) (T : NNReal)
    (hA : ∀ (e : ℝ), 0 < e →
      Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |A n t w|}).toReal) atTop (nhds 0))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    ∃ M : ℕ → ℕ, Tendsto M atTop atTop ∧
      ∀ᵐ w ∂P, ∀ e : ℝ, 0 < e →
        ∀ᶠ n in atTop, ∀ t ≤ T, |A (N (M n)) t w| < e := by
  classical
  let r : ℕ → ℝ := fun n => (1/2:ℝ)^n
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hlim : Tendsto r atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall (n : ℕ) : ∀ᶠ k in atTop,
      (P {w | ∃ t ≤ T, r n ≤ |A (N k) t w|}).toReal < r n :=
    ((hA (r n) (hr n)).comp hN).eventually (gt_mem_nhds (hr n))
  choose b hb using fun n => eventually_atTop.mp (hsmall n)
  let M : ℕ → ℕ := fun n => max n (b n)
  have hM : Tendsto M atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left _ _) tendsto_id
  let S : ℕ → Set Omega := fun n => {w | ∃ t ≤ T, r n ≤ |A (N (M n)) t w|}
  have hle (n : ℕ) : P (S n) ≤ (1/2:ℝ≥0∞)^n := by
    have h := (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top P (S n)) (hr n).le).mpr
      (hb n (M n) (le_max_right _ _)).le
    simpa only [r, ENNReal.ofReal_pow (by norm_num : 0 ≤ (1/2:ℝ)),
      ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2:ℝ)), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat] using h
  have hsum : (∑' n, P (S n)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_geometric]
    norm_num
  refine ⟨M,hM,?_⟩
  filter_upwards [ae_eventually_notMem hsum] with w hw
  intro e he
  filter_upwards [hw,hlim.eventually (gt_mem_nhds he)] with n hn hnsmall
  intro t ht
  exact (lt_of_not_ge (fun h => hn ⟨t,ht,h⟩)).trans hnsmall
