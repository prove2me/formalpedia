-- Prove2me | solution 1 for KTSPBounds.simplex_moment_integral
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:51:50.98338+00:00
-- url     : https://prove2.me/submissions/a8bcc517-861e-4188-94f1-4cba581e7b92

import Mathlib

open MeasureTheory Set

lemma beta_step (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∫ x in (0:ℝ)..t, x * (t - x) ^ m = t ^ (m + 2) / ((m + 1) * (m + 2)) := by
  have h1 : ∫ x in (0:ℝ)..t, x * (t - x) ^ m = ∫ u in (0:ℝ)..t, (t - u) * u ^ m := by
    have := intervalIntegral.integral_comp_sub_left (fun u => (t - u) * u ^ m) (a := 0) (b := t) t
    simp only [sub_sub_cancel, sub_self, sub_zero] at this
    rw [← this]
  rw [h1]
  have hA : IntervalIntegrable (fun u : ℝ => t * u ^ m) MeasureTheory.volume 0 t :=
    (continuous_const.mul (continuous_pow m)).intervalIntegrable 0 t
  have hB : IntervalIntegrable (fun u : ℝ => u ^ (m + 1)) MeasureTheory.volume 0 t :=
    (continuous_pow (m + 1)).intervalIntegrable 0 t
  have h2 : ∫ u in (0:ℝ)..t, (t - u) * u ^ m =
      t * (∫ u in (0:ℝ)..t, u ^ m) - ∫ u in (0:ℝ)..t, u ^ (m + 1) := by
    calc ∫ u in (0:ℝ)..t, (t - u) * u ^ m = ∫ u in (0:ℝ)..t, (t * u ^ m - u ^ (m + 1)) :=
          intervalIntegral.integral_congr (fun u _ => by ring)
      _ = (∫ u in (0:ℝ)..t, t * u ^ m) - ∫ u in (0:ℝ)..t, u ^ (m + 1) :=
          intervalIntegral.integral_sub hA hB
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have i1 : ∫ u in (0:ℝ)..t, u ^ m = t ^ (m + 1) / (m + 1) := by
    rw [integral_pow]; simp
  have i2 : ∫ u in (0:ℝ)..t, u ^ (m + 1) = t ^ (m + 2) / (m + 2) := by
    rw [integral_pow]; push_cast; simp; ring
  rw [h2, i1, i2]
  field_simp
  ring

def Sx (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) := {l | (∀ i, 0 ≤ l i) ∧ ∑ i, l i ≤ t}

lemma Sx_meas (k : ℕ) (t : ℝ) : MeasurableSet (Sx k t) := by
  unfold Sx
  have e : {l : Fin k → ℝ | (∀ i, 0 ≤ l i) ∧ ∑ i, l i ≤ t} =
      (⋂ i, {l : Fin k → ℝ | 0 ≤ l i}) ∩ {l | ∑ i, l i ≤ t} := by ext l; simp
  rw [e]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  · exact measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const

noncomputable def Gk (k : ℕ) (t : ℝ) : ℝ := ∫ l : Fin k → ℝ, (Sx k t).indicator (fun l => ∏ i, l i) l

lemma Sx_bdd (k : ℕ) (t : ℝ) : ∀ l ∈ Sx k t, ∀ i, 0 ≤ l i ∧ l i ≤ t := by
  intro l hl i
  refine ⟨hl.1 i, le_trans ?_ hl.2⟩
  exact Finset.single_le_sum (fun j _ => hl.1 j) (Finset.mem_univ i)

lemma Sx_integrable (k : ℕ) (t : ℝ) :
    Integrable ((Sx k t).indicator (fun l : Fin k → ℝ => ∏ i, l i)) := by
  rw [integrable_indicator_iff (Sx_meas k t)]
  have hbdd : Bornology.IsBounded (Sx k t) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨|t|, fun l hl => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (abs_nonneg t)]
    intro i
    have := Sx_bdd k t l hl i
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2.trans (le_abs_self t)
  refine Measure.integrableOn_of_bounded (M := |t| ^ k) hbdd.measure_lt_top.ne
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  rw [ae_restrict_iff' (Sx_meas k t)]
  filter_upwards with l hl
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc ∏ i, |l i| ≤ ∏ _i : Fin k, |t| := Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => by
        have := Sx_bdd k t l hl i
        rw [abs_of_nonneg this.1]; exact this.2.trans (le_abs_self t))
    _ = |t| ^ k := by simp

lemma Sx_empty (k : ℕ) (t : ℝ) (ht : t < 0) : Sx k t = ∅ := by
  ext l
  simp only [Sx, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro h
  exact lt_of_lt_of_le ht (Finset.sum_nonneg (fun i _ => h i))

lemma Gk_neg (k : ℕ) (t : ℝ) (ht : t < 0) : Gk k t = 0 := by
  rw [Gk, Sx_empty k t ht]; simp

lemma Gk_zero (t : ℝ) (ht : 0 ≤ t) : Gk 0 t = 1 := by
  rw [Gk]
  have : (Sx 0 t).indicator (fun l : Fin 0 → ℝ => ∏ i, l i) = fun _ => 1 := by
    funext l
    rw [Set.indicator_of_mem]
    · simp
    · exact ⟨fun i => i.elim0, by simpa using ht⟩
  rw [this]
  simp only [integral_const, smul_eq_mul, mul_one]
  rw [measureReal_def, show (volume : Measure (Fin 0 → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.pi_of_empty]; simp

lemma Gk_succ (k : ℕ) (t : ℝ) :
    Gk (k + 1) t = ∫ x : ℝ, (Set.Ici (0:ℝ)).indicator (fun x => x) x * Gk k (t - x) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0 with he
  have hmp : MeasurePreserving e.symm (volume.prod volume) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm
  set F := (Sx (k + 1) t).indicator (fun l : Fin (k + 1) → ℝ => ∏ i, l i) with hF
  have hcomp : ∀ p : ℝ × (Fin k → ℝ), F (e.symm p) =
      (Set.Ici (0:ℝ)).indicator (fun x => x) p.1 * (Sx k (t - p.1)).indicator (fun l => ∏ i, l i) p.2 := by
    rintro ⟨x, y⟩
    have hsymm : e.symm (x, y) = Fin.cons x y := by
      rw [he]; ext j
      simp [MeasurableEquiv.piFinSuccAbove]
    rw [hsymm, hF]
    simp only [Sx, Set.indicator, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero,
      Fin.cons_succ, Fin.sum_univ_succ, Fin.prod_univ_succ, Set.mem_Ici]
    by_cases hx : 0 ≤ x
    · by_cases hy : (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ t - x
      · rw [if_pos ⟨⟨hx, hy.1⟩, by linarith [hy.2]⟩, if_pos hx, if_pos hy]
      · rw [if_neg, if_pos hx, if_neg hy, mul_zero]
        rintro ⟨⟨_, h1⟩, h2⟩; exact hy ⟨h1, by linarith⟩
    · rw [if_neg (fun h => hx h.1.1), if_neg hx, zero_mul]
  have hint : Integrable (F ∘ e.symm) (volume.prod volume) :=
    (hmp.integrable_comp_emb e.symm.measurableEmbedding).mpr (Sx_integrable (k + 1) t)
  rw [Gk, ← hmp.integral_comp' F]
  change ∫ z, (F ∘ e.symm) z ∂(volume.prod volume) = _
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Function.comp_apply]
  simp_rw [hcomp]
  rw [integral_const_mul]
  rfl

lemma Gk_formula (k : ℕ) : ∀ t : ℝ, 0 ≤ t → Gk k t = t ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  induction k with
  | zero => intro t ht; rw [Gk_zero t ht]; simp
  | succ k ih =>
    intro t ht
    rw [Gk_succ]
    have hpt : ∀ x : ℝ, (Set.Ici (0:ℝ)).indicator (fun x => x) x * Gk k (t - x) =
        (Set.Icc 0 t).indicator (fun x => x * (t - x) ^ (2 * k) / ((2 * k).factorial : ℝ)) x := by
      intro x
      by_cases hx : 0 ≤ x
      · by_cases htx : x ≤ t
        · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hx),
            Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hx, htx⟩), ih (t - x) (by linarith)]
          ring
        · rw [Gk_neg k (t - x) (by linarith), mul_zero, Set.indicator_of_notMem]
          exact fun h => htx h.2
      · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Ici.mp h)), zero_mul,
          Set.indicator_of_notMem]
        exact fun h => hx (Set.mem_Icc.mp h).1
    simp_rw [hpt]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht, intervalIntegral.integral_div, beta_step (2 * k) t ht]
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem solution (k : ℕ) :
    ∫ l in {l : Fin k → ℝ | (∀ i, 0 ≤ l i) ∧ ∑ i, l i ≤ 1}, ∏ i, l i =
      1 / ((2 * k).factorial : ℝ) := by
  have h := Gk_formula k 1 zero_le_one
  rw [Gk, integral_indicator (Sx_meas k 1)] at h
  rw [one_pow] at h
  exact h
