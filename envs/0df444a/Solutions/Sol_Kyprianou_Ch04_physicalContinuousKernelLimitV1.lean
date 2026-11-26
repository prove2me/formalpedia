-- Prove2me | solution 1 for Kyprianou.Ch04.physicalContinuousKernelLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:21:56.645912+00:00
-- url     : https://prove2.me/submissions/556184b0-a289-499b-85f0-ca7cd465431e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_physicalRetainedMarkDCTV1
import Theorems.Thm_Kyprianou_Ch04_physicalWindowPositiveTimeCongrV1
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Retained-mark dominated convergence for a continuous state kernel on positive time. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : NNReal)
    (hz : R (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0)
    (Y : ℕ → NNReal → ℝ) (L : NNReal → ℝ) (e : ℕ → ℝ)
    (g : ℝ → ℝ → ℝ → ℝ) (B : ℝ → ℝ)
    (hY : ∀ n, Measurable (Y n)) (he : Tendsto e atTop (𝓝 0))
    (hg : Continuous (fun p : ℝ × ℝ × ℝ => g (max 0 p.1) p.2.1 p.2.2))
    (hzero : ∀ s x, g s x 0 = 0)
    (hB : IntegrableOn (fun z : ℝ × ℝ => B z.2)
      (Icc (0 : ℝ) (T : ℝ) ×ˢ univ) R)
    (hdom : ∀ s x z, 0 ≤ s → |g s x z| ≤ B z)
    (h : ∀ t : NNReal, 0 < t → t ≤ T →
      Tendsto (fun n => Y n t) atTop (𝓝 (L t))) :
    Tendsto (fun n => ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e n < |x|},
      g z.1 (Y n z.1.toNNReal) z.2 ∂ R) atTop
      (𝓝 (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ univ, g z.1 (L z.1.toNNReal) z.2 ∂ R)) := by
  let J (Z : NNReal → ℝ) (z : ℝ × ℝ) :=
    if 0 < z.1 then g (max 0 z.1) (Z z.1.toNNReal) z.2 else 0
  have hm (n : ℕ) : Measurable (J (Y n)) := by
    apply Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    · exact hg.measurable.comp (measurable_fst.prodMk
        (((hY n).comp (measurable_real_toNNReal.comp measurable_fst)).prodMk measurable_snd))
    · exact measurable_const
  have hd (n : ℕ) (z : ℝ × ℝ) (hz' : z ∈ Icc (0 : ℝ) (T : ℝ) ×ˢ univ) :
      |J (Y n) z| ≤ B z.2 := by
    have hnon : 0 ≤ B z.2 := (abs_nonneg _).trans (hdom 0 0 z.2 le_rfl)
    by_cases hp : 0 < z.1
    · simpa [J,hp] using hdom (max 0 z.1) (Y n z.1.toNNReal) z.2 (by positivity)
    · simp [J,hp,hnon]
  have hlim : ∀ᵐ z ∂ R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ univ),
      z.2 ≠ 0 → Tendsto (fun n => J (Y n) z) atTop (𝓝 (J L z)) := by
    filter_upwards [ae_restrict_mem (μ := R) (measurableSet_Icc.prod MeasurableSet.univ)]
      with z hz' _
    by_cases hp : 0 < z.1
    · have ht := h z.1.toNNReal (Real.toNNReal_pos.mpr hp)
          (Real.toNNReal_le_iff_le_coe.mpr hz'.1.2)
      have hprod : Tendsto (fun n => (z.1,Y n z.1.toNNReal,z.2)) atTop
          (𝓝 (z.1,L z.1.toNNReal,z.2)) :=
        tendsto_const_nhds.prodMk_nhds (ht.prodMk_nhds tendsto_const_nhds)
      simpa [J,hp,Function.comp_def] using (hg.tendsto _).comp hprod
    · simpa [J,hp] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hD := Kyprianou.Ch04.physicalRetainedMarkDCTV1 R T
    (fun n => J (Y n)) (J L) e (fun z => B z.2) he hm hB hd
    (fun n s => by simp [J,hzero]) (fun s => by simp [J,hzero]) hlim
  have hEq (Z : NNReal → ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
      (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ A, J Z z ∂ R) =
        ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ A, g z.1 (Z z.1.toNNReal) z.2 ∂ R :=
    Kyprianou.Ch04.physicalWindowPositiveTimeCongrV1 R T A hA hz _ _
      (fun z hp _ _ => by simp [J,hp,max_eq_right hp.le])
  rw [hEq L univ MeasurableSet.univ] at hD
  apply hD.congr'
  filter_upwards [] with n
  exact hEq (Y n) _ (measurableSet_lt measurable_const measurable_id.abs)
