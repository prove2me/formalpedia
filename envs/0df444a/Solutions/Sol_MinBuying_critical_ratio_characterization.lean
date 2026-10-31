-- Prove2me | solution 1 for MinBuying.critical_ratio_characterization
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:12:19.69935+00:00
-- url     : https://prove2.me/submissions/7d9e6689-7c47-466f-90dc-e7392b97e687

import Theorems.Thm_MinBuying_budget_characterization
import Theorems.Thm_MinBuying_benchmark_characterization

open Set MeasureTheory Filter
open scoped Interval Topology

noncomputable section

private lemma primitive_cont {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ico (0 : ℝ) 1)) :
    ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, g t) (Ico (0 : ℝ) 1) := by
  intro x hx
  let b := (x + 1) / 2
  have hxb : x < b := by dsimp [b]; linarith [hx.2]
  have hb0 : 0 ≤ b := le_trans hx.1 hxb.le
  have hb1 : b < 1 := by dsimp [b]; linarith [hx.2]
  have hg' : ContinuousOn g (Icc 0 b) := hg.mono (by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hb1⟩)
  have hi : IntervalIntegrable g volume 0 b := hg'.intervalIntegrable_of_Icc hb0
  have hc : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, g t) (Icc 0 b) := by
    simpa only [uIcc_of_le hb0] using
      (intervalIntegral.continuousOn_primitive_interval' hi
        (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 b))
  apply (hc x ⟨hx.1, hxb.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxb)] with t ht htb
  exact ⟨ht.1, htb.le⟩

private lemma primitive_deriv {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ico (0 : ℝ) 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, g t) (g x) x := by
  have hi : IntervalIntegrable g volume 0 x :=
    (hg.mono (show Icc (0 : ℝ) x ⊆ Ico 0 1 from fun _ ht =>
      ⟨ht.1, lt_of_le_of_lt ht.2 hx.2⟩)).intervalIntegrable_of_Icc hx.1.le
  have hm : StronglyMeasurableAtFilter g (𝓝 x) volume :=
    (hg.mono Ioo_subset_Ico_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
  exact intervalIntegral.integral_hasDerivAt_right hi hm
    (hg.continuousAt (Ico_mem_nhds_iff.mpr hx))

open MinBuying

private lemma exponent_cont : ContinuousOn odeExponent (Ico (0 : ℝ) 1) :=
  primitive_cont (continuousOn_id.mul budget_characterization.2.1)

private lemma exponent_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt odeExponent (x * budgetSlope x) x :=
  primitive_deriv (continuousOn_id.mul budget_characterization.2.1) hx

private lemma integrand_cont : ContinuousOn
    (fun t => budgetSlope t * Real.exp (odeExponent t)) (Ico (0 : ℝ) 1) :=
  budget_characterization.2.1.mul exponent_cont.rexp

private lemma benchmark_pos {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    0 < continuousBenchmark x := by
  have hJ : 0 ≤ ∫ t in (0 : ℝ)..x, budgetSlope t * Real.exp (odeExponent t) := by
    apply intervalIntegral.integral_nonneg hx.1
    intro t ht
    exact mul_nonneg
      (budget_characterization.2.2.1 t ⟨ht.1, ht.2.trans_lt hx.2⟩).2.1.le
      (Real.exp_pos _).le
  unfold continuousBenchmark
  exact mul_pos (Real.exp_pos _) (by linarith)

private def weightedGap (x : ℝ) : ℝ :=
  Real.exp (odeExponent x) * (1 - x * continuousBenchmark x)

private lemma weightedGap_cont : ContinuousOn weightedGap (Ico (0 : ℝ) 1) :=
  exponent_cont.rexp.mul
    (continuousOn_const.sub (continuousOn_id.mul benchmark_characterization.2.1))

private lemma weightedGap_zero : weightedGap 0 = 1 := by
  simp [weightedGap, odeExponent]

private lemma weightedGap_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt weightedGap (-Real.exp (odeExponent x) * continuousBenchmark x) x := by
  have hc := benchmark_characterization.2.2.1 x hx
  convert! (exponent_deriv hx).exp.mul
    ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).mul hc)) using 1
  dsimp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  ring

private lemma weightedGap_strictAnti : StrictAntiOn weightedGap (Ico (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 1) weightedGap_cont
  intro x hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ico] using hx
  rw [(weightedGap_deriv hx').deriv]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _))
    (benchmark_pos ⟨hx'.1.le, hx'.2⟩)

private lemma crossing_exists : ∃ r ∈ Ioo (0 : ℝ) 1, weightedGap r = 0 := by
  have hn : ∃ x ∈ Ioo (0 : ℝ) 1, weightedGap x ≤ 0 := by
    by_contra h
    push_neg at h
    have hm : StrictMonoOn continuousBenchmark (Ico (0 : ℝ) 1) := by
      apply strictMonoOn_of_deriv_pos (convex_Ico 0 1) benchmark_characterization.2.1
      intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ico] using hx
      rw [(benchmark_characterization.2.2.1 x hx').deriv]
      have hg : 0 < 1 - x * continuousBenchmark x := by
        exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp (h x hx')
      exact mul_pos (budget_characterization.2.2.1 x ⟨hx'.1.le, hx'.2⟩).2.1 hg
    let b : ℝ := continuousBenchmark (1 / 2)
    have hb : 1 < b := by
      have hh := hm (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
        (show (1 / 2 : ℝ) ∈ Ico 0 1 by norm_num) (by norm_num)
      simpa only [benchmark_characterization.1] using hh
    have hbpos : 0 < b := by linarith
    let t := (1 + 1 / b) / 2
    have ht_half : (1 / 2 : ℝ) < t := by
      dsimp [t]
      linarith [one_div_pos.mpr hbpos]
    have ht_one : t < 1 := by
      dsimp [t]
      have hdiv : 1 / b < 1 := (div_lt_one hbpos).mpr hb
      linarith
    have ht_pos : 0 < t := lt_trans (by norm_num) ht_half
    have hprod : t * b = (b + 1) / 2 := by
      dsimp [t]
      field_simp
      <;> ring
    have hbc : b ≤ continuousBenchmark t :=
      (hm (show (1 / 2 : ℝ) ∈ Ico 0 1 by norm_num)
        ⟨ht_pos.le, ht_one⟩ ht_half).le
    have hgap : 0 < 1 - t * continuousBenchmark t :=
      (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp (h t ⟨ht_pos, ht_one⟩)
    have hmult := mul_le_mul_of_nonneg_left hbc ht_pos.le
    linarith
  obtain ⟨x, hx, hxn⟩ := hn
  have hc := weightedGap_cont.mono
    (show Icc (0 : ℝ) x ⊆ Ico 0 1 from fun _ ht => ⟨ht.1, ht.2.trans_lt hx.2⟩)
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hx.1.le hc
    (show (0 : ℝ) ∈ Icc (weightedGap x) (weightedGap 0) by
      rw [weightedGap_zero]
      exact ⟨hxn, zero_le_one⟩)
  have hrpos : 0 < r := by
    have hrne : r ≠ 0 := by
      intro h0
      simp only [h0, weightedGap_zero] at hr0
      norm_num at hr0
    exact lt_of_le_of_ne hr.1 (Ne.symm hrne)
  exact ⟨r, ⟨hrpos, hr.2.trans_lt hx.2⟩, hr0⟩

theorem solution :
    criticalRatio ∈ Ioo (0 : ℝ) 1 ∧
    criticalRatio * continuousBenchmark criticalRatio = 1 ∧
    (∀ x ∈ Ioo (0 : ℝ) 1,
      x * continuousBenchmark x = 1 → x = criticalRatio) ∧
    (∀ x ∈ Ico (0 : ℝ) 1,
      1 ≤ continuousBenchmark x ∧ continuousBenchmark x ≤ 1 / criticalRatio) ∧
    StrictMonoOn continuousBenchmark (Icc (0 : ℝ) criticalRatio) ∧
    StrictAntiOn continuousBenchmark (Ico criticalRatio 1) := by
  obtain ⟨r, hr, hr0⟩ := crossing_exists
  have hroot : r * continuousBenchmark r = 1 := by
    have h := (mul_eq_zero.mp hr0).resolve_left (Real.exp_ne_zero _)
    linarith
  have hunique : ∀ x ∈ Ioo (0 : ℝ) 1,
      x * continuousBenchmark x = 1 → x = r := by
    intro x hx hxr
    apply weightedGap_strictAnti.injOn ⟨hx.1.le, hx.2⟩ ⟨hr.1.le, hr.2⟩
    rw [hr0]
    simp [weightedGap, hxr]
  have hroots : criticalRoots = {r} := by
    ext x
    constructor
    · intro hx
      exact mem_singleton_iff.mpr (hunique x hx.1 hx.2)
    · intro hx
      rcases mem_singleton_iff.mp hx with rfl
      exact ⟨hr, hroot⟩
  have hrho : criticalRatio = r := by simp [criticalRatio, hroots]
  rw [hrho]
  have hcr : continuousBenchmark r = 1 / r := by
    apply (eq_div_iff (ne_of_gt hr.1)).mpr
    nlinarith [hroot]
  have hm : StrictMonoOn continuousBenchmark (Icc (0 : ℝ) r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 r)
      (benchmark_characterization.2.1.mono (fun _ hx => ⟨hx.1, hx.2.trans_lt hr.2⟩))
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) r := by simpa only [interior_Icc] using hx
    have hxi : x ∈ Ioo (0 : ℝ) 1 := ⟨hx'.1, hx'.2.trans hr.2⟩
    rw [(benchmark_characterization.2.2.1 x hxi).deriv]
    have hw : 0 < weightedGap x := by
      rw [← hr0]
      exact weightedGap_strictAnti ⟨hxi.1.le, hxi.2⟩ ⟨hr.1.le, hr.2⟩ hx'.2
    exact mul_pos (budget_characterization.2.2.1 x ⟨hxi.1.le, hxi.2⟩).2.1
      ((mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hw)
  have ha : StrictAntiOn continuousBenchmark (Ico r 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ico r 1)
      (benchmark_characterization.2.1.mono (fun _ hx => ⟨hr.1.le.trans hx.1, hx.2⟩))
    intro x hx
    have hx' : x ∈ Ioo r (1 : ℝ) := by simpa only [interior_Ico] using hx
    have hxi : x ∈ Ioo (0 : ℝ) 1 := ⟨hr.1.trans hx'.1, hx'.2⟩
    rw [(benchmark_characterization.2.2.1 x hxi).deriv]
    have hw : weightedGap x < 0 := by
      rw [← hr0]
      exact weightedGap_strictAnti ⟨hr.1.le, hr.2⟩ ⟨hxi.1.le, hxi.2⟩ hx'.1
    have hgap : 1 - x * continuousBenchmark x < 0 :=
      neg_of_mul_neg_right hw (Real.exp_pos _).le
    exact mul_neg_of_pos_of_neg (budget_characterization.2.2.1 x ⟨hxi.1.le, hxi.2⟩).2.1 hgap
  refine ⟨hr, hroot, hunique, ?_, hm, ha⟩
  intro x hx
  by_cases hxr : x ≤ r
  · have hlow := hm.monotoneOn (show (0 : ℝ) ∈ Icc 0 r from ⟨le_rfl, hr.1.le⟩)
      ⟨hx.1, hxr⟩ hx.1
    have hupp := hm.monotoneOn ⟨hx.1, hxr⟩ ⟨hr.1.le, le_rfl⟩ hxr
    simpa only [benchmark_characterization.1, hcr] using And.intro hlow hupp
  · have hrx : r < x := lt_of_not_ge hxr
    have hupp := ha.antitoneOn ⟨le_rfl, hr.2⟩ ⟨hrx.le, hx.2⟩ hrx.le
    have hw : weightedGap x < 0 := by
      rw [← hr0]
      exact weightedGap_strictAnti ⟨hr.1.le, hr.2⟩ hx hrx
    have hgap : 1 - x * continuousBenchmark x < 0 :=
      neg_of_mul_neg_right hw (Real.exp_pos _).le
    have hpos := benchmark_pos hx
    have hlow : 1 ≤ continuousBenchmark x := by nlinarith [hx.2]
    exact ⟨hlow, by simpa only [hcr] using hupp⟩

