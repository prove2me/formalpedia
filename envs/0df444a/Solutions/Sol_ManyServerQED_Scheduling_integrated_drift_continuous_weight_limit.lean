-- Prove2me | solution 1 for ManyServerQED.Scheduling.integrated_drift_continuous_weight_limit
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T21:10:13.477928+00:00
-- url     : https://prove2.me/submissions/6853c3e6-b6cf-4a95-8414-43f8d2fdb29b

import Mathlib

open MeasureTheory Set Filter Topology Finset

private noncomputable def grid (T : ℝ) (m j : ℕ) : ℝ := T * j / (m+1:ℕ)
private noncomputable def gridSum (T : ℝ) (w b : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ range (m+1), w (grid T m j) * (b (grid T m (j+1)) - b (grid T m j))

private theorem grid_mono {T : ℝ} (hT : 0 ≤ T) (m : ℕ) : Monotone (grid T m) := by
  intro i j hij
  unfold grid
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hT) (by positivity)

private theorem grid_mem {T : ℝ} (hT : 0 ≤ T) {m j : ℕ} (hj : j ≤ m+1) :
    grid T m j ∈ Icc 0 T := by
  constructor
  · unfold grid
    positivity
  · have he : grid T m (m+1) = T := by
      unfold grid
      exact mul_div_cancel_right₀ _ (by positivity)
    exact ((grid_mono hT m) hj).trans_eq he

private theorem grid_riemann_error {T C ε : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (v w a : ℝ → ℝ) (ha : IntervalIntegrable a volume 0 T)
    (hInt : IntervalIntegrable (fun s => v s * a s) volume 0 T)
    (hB : ∀ s ∈ Icc 0 T, |a s| ≤ C) (m : ℕ)
    (hErr : ∀ j : ℕ, j < m+1 → ∀ s ∈ Icc (grid T m j) (grid T m (j+1)),
      |v s - w (grid T m j)| ≤ ε) :
    |(∫ s in (0:ℝ)..T, v s * a s) - gridSum T w (fun t => ∫ s in (0:ℝ)..t, a s) m| ≤ T*C*ε := by
  have htm : grid T m (m+1) = T := by
    unfold grid
    exact mul_div_cancel_right₀ _ (by positivity)
  have ht0 : grid T m 0 = 0 := by simp [grid]
  have hh {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 T) :
      ∀ j, j < m+1 → IntervalIntegrable f volume (grid T m j) (grid T m (j+1)) := by
    intro j hj
    apply hf.mono_set
    rw [uIcc_of_le ((grid_mono hT m) (Nat.le_succ j)),uIcc_of_le hT]
    exact Icc_subset_Icc (grid_mem hT hj.le).1 (grid_mem hT (Nat.succ_le_of_lt hj)).2
  have hp (j : ℕ) (hj : j ≤ m+1) :
      IntervalIntegrable a volume 0 (grid T m j) := by
    apply ha.mono_set
    rw [uIcc_of_le (grid_mem hT hj).1,uIcc_of_le hT]
    exact Icc_subset_Icc_right (grid_mem hT hj).2
  have hS := intervalIntegral.sum_integral_adjacent_intervals (a := grid T m) (hh hInt)
  rw [ht0,htm] at hS
  unfold gridSum
  rw [← hS, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hPoint (j : ℕ) (hj : j ∈ range (m+1)) :
      |(∫ s in grid T m j..grid T m (j+1), v s*a s) -
        w (grid T m j) * ((∫ s in (0:ℝ)..grid T m (j+1), a s) -
          ∫ s in (0:ℝ)..grid T m j, a s)| ≤
       (grid T m (j+1) - grid T m j) * (C*ε) := by
    have hj' := mem_range.1 hj
    let l := grid T m j
    let r := grid T m (j+1)
    have hlr : l ≤ r := (grid_mono hT m) (Nat.le_succ j)
    have haI : IntervalIntegrable a volume l r := hh ha j hj'
    have hI : IntervalIntegrable (fun s => v s*a s) volume l r := hh hInt j hj'
    have hD := intervalIntegral.integral_add_adjacent_intervals (hp j hj'.le) haI
    have hSub : ((∫ s in (0:ℝ)..r, a s) - ∫ s in (0:ℝ)..l, a s) =
      ∫ s in l..r, a s := by linarith
    change |(∫ s in l..r, v s*a s) - w l * ((∫ s in (0:ℝ)..r, a s) -
        ∫ s in (0:ℝ)..l, a s)| ≤ _
    rw [hSub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hI (haI.const_mul (w l))]
    have hi := (hI.sub (haI.const_mul (w l))).abs
    refine (intervalIntegral.abs_integral_le_integral_abs hlr).trans ?_
    have hBnd : ∀ s ∈ Icc l r, |v s*a s - w l*a s| ≤ C*ε := by
      intro s hs
      rw [← sub_mul, abs_mul, mul_comm C ε]
      exact mul_le_mul (hErr j hj' s hs)
        (hB s ⟨(grid_mem hT hj'.le).1.trans hs.1,hs.2.trans (grid_mem hT (Nat.succ_le_of_lt hj')).2⟩)
        (abs_nonneg _) (le_trans (abs_nonneg _) (hErr j hj' s hs))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm (C*ε)] using
      intervalIntegral.integral_mono_on hlr hi (intervalIntegrable_const (c := C*ε)) hBnd
  refine (Finset.sum_le_sum (fun j hj => hPoint j hj)).trans_eq ?_
  rw [← Finset.sum_mul]
  have htel (l : ℕ) : ∑ j ∈ range l, (grid T m (j+1) - grid T m j) = grid T m l - grid T m 0 := by
    induction l with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, ih]; ring
  have hs : ∑ j ∈ range (m+1), (grid T m (j+1) - grid T m j) = T := by
    rw [htel, htm, ht0, sub_zero]
  rw [hs]
  ring

set_option maxHeartbeats 1300000 in
theorem solution (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (v a : ℕ → ℝ → ℝ) (w B : ℝ → ℝ)
    (hW : ContinuousOn w (Icc 0 T))
    (hV : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) T, |v n s - w s| < ε)
    (hA : ∀ n, IntervalIntegrable (a n) volume 0 T)
    (hB : ∀ n s, s ∈ Icc 0 T → |a n s| ≤ C)
    (hI : ∀ n, IntervalIntegrable (fun s => v n s * a n s) volume 0 T)
    (hPrim : ∀ t ∈ Icc 0 T, Tendsto (fun n => ∫ s in (0:ℝ)..t, a n s) atTop (𝓝 (B t))) :
    ∃ x : ℝ, Tendsto (fun n => ∫ s in (0:ℝ)..T, v n s * a n s) atTop (𝓝 x) ∧
      Tendsto (fun m : ℕ => ∑ j ∈ range (m+1),
        w (T*j/(m+1:ℕ)) * (B (T*(j+1:ℕ)/(m+1:ℕ)) - B (T*j/(m+1:ℕ))))
        atTop (𝓝 x) := by
  let I (n : ℕ) := ∫ s in (0:ℝ)..T, v n s * a n s
  let F (n : ℕ) (t : ℝ) := ∫ s in (0:ℝ)..t, a n s
  let S (m : ℕ) := gridSum T w B m
  have hGridLimit (m : ℕ) : Tendsto (fun n => gridSum T w (F n) m) atTop (𝓝 (S m)) := by
    apply tendsto_finset_sum
    intro j hj
    have hj' := mem_range.1 hj
    exact tendsto_const_nhds.mul
      ((hPrim _ (grid_mem hT (Nat.succ_le_of_lt hj'))).sub (hPrim _ (grid_mem hT hj'.le)))
  have hClose (ε : ℝ) (hε : 0 < ε) :
      ∃ M : ℕ, ∀ m ≥ M, ∀ᶠ n in atTop, dist (I n) (S m) ≤ ε := by
    let d := ε/(4*(T*C+1))
    have hd : 0 < d := by dsimp [d]; positivity
    obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hW) d hd
    obtain ⟨M,hM⟩ := exists_nat_gt (T/δ)
    refine ⟨M, fun m hm => ?_⟩
    have hstep : T / (m+1:ℕ) < δ := by
      have h' := (div_lt_iff₀ hδ).1 hM
      apply (div_lt_iff₀ (by positivity)).2
      have hm' : (M:ℝ) ≤ m := by exact_mod_cast hm
      push_cast
      nlinarith
    have hc' := (Metric.tendsto_nhds.mp (hGridLimit m)) (ε/2) (by positivity)
    filter_upwards [hV d hd, hc'] with n hv hg
    have hR : |I n - gridSum T w (F n) m| ≤ T*C*(2*d) := by
      refine grid_riemann_error hT hC (v n) w (a n) (hA n) (hI n) (hB n) m ?_
      intro j hj s hs
      have hj0 := grid_mem hT hj.le
      have hj1 := grid_mem hT (Nat.succ_le_of_lt hj)
      have hs0 : s ∈ Icc 0 T := ⟨hj0.1.trans hs.1,hs.2.trans hj1.2⟩
      have hdiff : grid T m (j+1) - grid T m j = T / (m+1:ℕ) := by
        unfold grid
        rw [← sub_div]
        push_cast
        congr 1
        ring
      have hdist : dist s (grid T m j) < δ := by
        rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hs.1)]
        linarith [hs.2,hstep,hdiff]
      have hu := hmod s hs0 _ hj0 hdist
      rw [Real.dist_eq] at hu
      have h := abs_sub_le (v n s) (w s) (w (grid T m j))
      linarith [hv s hs0]
    have hRt : T*C*(2*d) ≤ ε/2 := by
      dsimp [d]
      have hm : 0 < T*C+1 := by positivity
      field_simp [hm.ne'] 
      nlinarith [mul_nonneg hT hC]
    rw [Real.dist_eq] at hg ⊢
    exact (abs_sub_le _ (gridSum T w (F n) m) _).trans (by linarith)
  have hCauchy : CauchySeq I := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨M,hM⟩ := hClose (ε/3) (by positivity)
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hM M le_rfl)
    refine ⟨N, fun n hn j hj => ?_⟩
    have h1 := hN n hn
    have h2 := hN j hj
    have h := dist_triangle (I n) (S M) (I j)
    rw [dist_comm (S M) (I j)] at h
    linarith
  obtain ⟨x,hx⟩ := cauchySeq_tendsto_of_complete hCauchy
  refine ⟨x,hx,Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  obtain ⟨M,hM⟩ := hClose (ε/2) (by positivity)
  filter_upwards [eventually_ge_atTop M] with m hm
  have h' := (hM m hm).and (Metric.tendsto_nhds.mp hx (ε/4) (by positivity))
  obtain ⟨n,hn,hx'⟩ := h'.exists
  change dist (S m) x < ε
  have h := dist_triangle (S m) (I n) x
  rw [dist_comm (S m) (I n)] at h
  linarith
