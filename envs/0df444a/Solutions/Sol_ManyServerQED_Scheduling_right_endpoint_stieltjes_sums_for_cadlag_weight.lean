-- Prove2me | solution 1 for ManyServerQED.Scheduling.right_endpoint_stieltjes_sums_for_cadlag_weight
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:24:14.457487+00:00
-- url     : https://prove2.me/submissions/184b77d5-4ac2-4996-9f6c-4d2d458e1327

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


set_option maxHeartbeats 1550000 in
theorem solution (T C D : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (w a : ℝ → ℝ)
    (hw : ∀ t ∈ Icc (0:ℝ) T, ContinuousWithinAt w (Ici t) t)
    (hW : ∀ t ∈ Icc (0:ℝ) T, |w t| ≤ D)
    (ha : IntervalIntegrable a volume 0 T)
    (hA : ∀ t ∈ Icc (0:ℝ) T, |a t| ≤ C) :
    let B (t : ℝ) := ∫ s in (0:ℝ)..t,a s
    Tendsto (fun m : ℕ => ∑ j ∈ range (m+1),
      w (T*(j+1:ℕ)/(m+1:ℕ)) *
      (B (T*(j+1:ℕ)/(m+1:ℕ))-B (T*j/(m+1:ℕ)))) atTop
      (𝓝 (∫ t in (0:ℝ)..T,w t*a t)) := by
  intro B
  classical
  let U (m j : ℕ) := Ioc (grid T m j) (grid T m (j+1))
  let f (m j : ℕ) := (U m j).indicator (fun t => w (grid T m (j+1))*a t)
  let F (m : ℕ) (t : ℝ) := ∑ j ∈ range (m+1), f m j t
  have ht0 (m : ℕ) : grid T m 0 = 0 := by simp [grid]
  have htM (m : ℕ) : grid T m (m+1) = T := by unfold grid; exact mul_div_cancel_right₀ _ (by positivity)
  have hstep (m j : ℕ) : grid T m (j+1)-grid T m j = T/(m+1:ℕ) := by
    unfold grid
    rw [← sub_div,Nat.cast_add,Nat.cast_one]
    ring
  have hSub (m j : ℕ) (hj : j < m+1) : U m j ⊆ Ioc (0:ℝ) T :=
    Ioc_subset_Ioc (grid_mem hT hj.le).1 (grid_mem hT (Nat.succ_le_of_lt hj)).2
  have hDisj (m i j : ℕ) (hij : i ≠ j) : Disjoint (U m i) (U m j) := by
    apply Set.disjoint_left.2
    intro t hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · exact (not_lt_of_ge (hi.2.trans (grid_mono hT m h))) hj.1
    · exact (not_lt_of_ge (hj.2.trans (grid_mono hT m h))) hi.1
  have hCell (t : ℝ) (ht : t ∈ Ioc (0:ℝ) T) (m : ℕ) : ∃ j ∈ range (m+1), t ∈ U m j := by
    have hS := Ioc_subset_biUnion_Ioc (m+1) (grid T m)
    rw [ht0,htM] at hS
    obtain ⟨j,hj⟩ := mem_iUnion.1 (hS ht)
    obtain ⟨hJ,hj⟩ := mem_iUnion.1 hj
    exact ⟨j,hJ,hj⟩
  have hF (m j : ℕ) (hj : j ∈ range (m+1)) (t : ℝ) (ht : t ∈ U m j) :
      F m t = w (grid T m (j+1))*a t := by
    unfold F
    rw [Finset.sum_eq_single_of_mem j hj]
    · exact Set.indicator_of_mem ht _
    · intro i hi hij
      exact Set.indicator_of_notMem (fun h => (Set.disjoint_left.1 (hDisj m i j hij) h ht)) _
  have hInt (m j : ℕ) (hj : j ∈ range (m+1)) :
      Integrable (f m j) (volume.restrict (Ioc (0:ℝ) T)) := by
    apply (integrable_indicator_iff measurableSet_Ioc).2
    rw [IntegrableOn,Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.2 (hSub m j (mem_range.1 hj))]
    exact (ha.1.mono_set (hSub m j (mem_range.1 hj))).const_mul _
  have hE (m : ℕ) :
      (∫ t in (0:ℝ)..T,F m t) =
        ∑ j ∈ range (m+1), w (grid T m (j+1))*(B (grid T m (j+1))-B (grid T m j)) := by
    rw [intervalIntegral.integral_of_le hT]
    change (∫ t, (∑ j ∈ range (m+1), f m j t) ∂volume.restrict (Ioc (0:ℝ) T)) = _
    rw [integral_finsetSum _ (hInt m)]
    apply sum_congr rfl
    intro j hj
    let l := grid T m j
    let r := grid T m (j+1)
    have hlr : l ≤ r := grid_mono hT m (Nat.le_succ j)
    have hl0 : 0 ≤ l := (grid_mem hT (mem_range.1 hj).le).1
    have hr0 : 0 ≤ r := (grid_mem hT (Nat.succ_le_of_lt (mem_range.1 hj))).1
    have hSub' (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) : IntervalIntegrable a volume 0 t := by
      apply ha.mono_set
      rw [uIcc_of_le ht.1,uIcc_of_le hT]
      exact Icc_subset_Icc_right ht.2
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hSub' l (grid_mem hT (mem_range.1 hj).le))
      ((hSub' l (grid_mem hT (mem_range.1 hj).le)).symm.trans
        (hSub' r (grid_mem hT (Nat.succ_le_of_lt (mem_range.1 hj)))))
    have hb : B r-B l = ∫ t in l..r,a t := by dsimp [B]; linarith
    rw [hb,intervalIntegral.integral_of_le hlr]
    unfold f
    rw [integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.2 (hSub m j (mem_range.1 hj)),integral_const_mul]
  have hDCT : Tendsto (fun m : ℕ => ∫ t in (0:ℝ)..T,F m t) atTop
      (𝓝 (∫ t in (0:ℝ)..T,w t*a t)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => D*C) ?_ ?_ intervalIntegrable_const ?_
    · apply Eventually.of_forall
      intro m
      rw [uIoc_of_le hT]
      exact (integrable_finsetSum _ (hInt m)).aestronglyMeasurable
    · apply Eventually.of_forall
      intro m
      apply Eventually.of_forall
      intro t ht
      rw [uIoc_of_le hT] at ht
      obtain ⟨j,hj,htj⟩ := hCell t ht m
      rw [hF m j hj t htj,Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hW _ (grid_mem hT (Nat.succ_le_of_lt (mem_range.1 hj))))
        (hA t ⟨ht.1.le,ht.2⟩) (abs_nonneg _) hD
    · apply Eventually.of_forall
      intro t ht
      rw [uIoc_of_le hT] at ht
      choose j hj hJ using hCell t ht
      let a₀ (m : ℕ) := grid T m (j m+1)
      have ha₀ (m : ℕ) : t ≤ a₀ m := (hJ m).2
      have hA₀ (m : ℕ) : a₀ m ≤ t + T/(m+1:ℕ) := by
        have hs := hstep m (j m)
        dsimp [a₀]
        linarith [(hJ m).1]
      have hDiv : Tendsto (fun m : ℕ => T/(m+1:ℕ)) atTop (𝓝 0) := by
        have hN : Tendsto (fun m : ℕ => (m+1:ℕ)) atTop atTop :=
          tendsto_add_atTop_nat 1
        exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hN)
      have hR' : Tendsto (fun m : ℕ => t+T/(m+1:ℕ)) atTop (𝓝 t) := by
        simpa only [add_zero] using (tendsto_const_nhds (x := t)).add hDiv
      have hT' : Tendsto a₀ atTop (𝓝[Ici t] t) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          hR' ha₀ hA₀,Eventually.of_forall ha₀⟩
      have hw' := ((hw t ⟨ht.1.le,ht.2⟩).tendsto.comp hT').mul_const (a t)
      exact hw'.congr' (Eventually.of_forall fun m => (hF m (j m) (hj m) t (hJ m)).symm)
  exact hDCT.congr' (Eventually.of_forall hE)
