-- Prove2me | solution 1 for MeasureTheory.Lp.infiniteDimensional_of_isOpen_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T22:21:21.482275+00:00
-- url     : https://prove2.me/submissions/685c0827-a694-4dbf-a2c9-02df091509fd

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory

theorem solution
    {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hn : 1 ≤ n) (hne : Ω.Nonempty) :
    ¬ FiniteDimensional ℝ (Lp ℝ 2 (volume.restrict Ω)) := by
  intro hfin
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
  set v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ 1
  have hv : ‖v‖ = 1 := by simp [v]
  set N := Module.finrank ℝ (Lp ℝ 2 (volume.restrict Ω)) + 1
  set δ : ℝ := r / (N + 1)
  have hδ : 0 < δ := by positivity
  let c : Fin N → EuclideanSpace ℝ (Fin n) := fun k => x + ((k : ℝ) * δ) • v
  let B : Fin N → Set (EuclideanSpace ℝ (Fin n)) := fun k => Metric.ball (c k) (δ / 3)
  have hBm : ∀ k, MeasurableSet (B k) := fun k => measurableSet_ball
  have hBsub : ∀ k, B k ⊆ Ω := by
    intro k y hy
    apply hball
    simp only [B, Metric.mem_ball] at hy ⊢
    have hck : dist (c k) x = (k : ℝ) * δ := by
      simp only [c, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs]
      exact abs_of_nonneg (by positivity)
    have hk : (k : ℝ) + 1 ≤ N := by exact_mod_cast k.2
    have : ((k : ℝ) + 1) * δ ≤ N * δ := mul_le_mul_of_nonneg_right hk hδ.le
    have hNδ : (N : ℝ) * δ < r := by
      simp only [δ]; rw [mul_div_assoc']; rw [div_lt_iff₀ (by positivity)]; nlinarith
    calc dist y x ≤ dist y (c k) + dist (c k) x := dist_triangle _ _ _
      _ < δ / 3 + k * δ := by rw [hck]; linarith
      _ < r := by nlinarith
  have hμ : ∀ k, (volume.restrict Ω) (B k) = volume (B k) := by
    intro k; rw [Measure.restrict_apply (hBm k), Set.inter_eq_left.2 (hBsub k)]
  have hfin' : ∀ k, (volume.restrict Ω) (B k) ≠ ⊤ := by
    intro k; rw [hμ k]; exact measure_ball_lt_top.ne
  let f : Fin N → Lp ℝ 2 (volume.restrict Ω) := fun k => indicatorConstLp 2 (hBm k) (hfin' k) 1
  have hdisj : ∀ i j, i ≠ j → B i ∩ B j = ∅ := by
    intro i j hij
    ext y; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hi hj
    simp only [B, Metric.mem_ball] at hi hj
    have hcc : dist (c i) (c j) = |(i : ℝ) - j| * δ := by
      simp only [c, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hv, mul_one,
        Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_pos hδ]
    have h1 : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      rw [le_abs]
      rcases Nat.lt_or_gt_of_ne this with h | h
      · have : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
        right; linarith
      · have : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast h
        left; linarith
    have : dist (c i) (c j) < 2 * δ / 3 := by
      calc dist (c i) (c j) ≤ dist (c i) y + dist y (c j) := dist_triangle _ _ _
        _ < δ / 3 + δ / 3 := by rw [dist_comm]; linarith
        _ = 2 * δ / 3 := by ring
    rw [hcc] at this
    nlinarith
  have hli : LinearIndependent ℝ f := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun k => ?_) (fun i j hij => ?_)
    · intro h0
      have := L2.real_inner_indicatorConstLp_one_indicatorConstLp_one (μ := volume.restrict Ω)
        (hBm k) (hBm k) (hfin' k) (hfin' k)
      change inner ℝ (f k) (f k) = _ at this
      rw [h0, inner_zero_left, Set.inter_self, measureReal_def, hμ k] at this
      have hpos : 0 < volume (B k) := Metric.measure_ball_pos _ _ (by positivity)
      have := (ENNReal.toReal_eq_zero_iff _).1 this.symm
      rcases this with h | h
      · exact hpos.ne' h
      · exact measure_ball_lt_top.ne h
    · have := L2.real_inner_indicatorConstLp_one_indicatorConstLp_one (μ := volume.restrict Ω)
        (hBm i) (hBm j) (hfin' i) (hfin' j)
      change inner ℝ (f i) (f j) = _ at this
      show inner ℝ (f i) (f j) = 0
      rw [this, hdisj i j hij]; simp
  have := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin, N] at this
  omega
