-- Prove2me | solution 1 for GeomDRSub.lemma_A_1_i
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:07:41.403316+00:00
-- url     : https://prove2.me/submissions/eaac2c6b-6fcb-4269-aca1-5869378412ab

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_gradQ

namespace Aux_GeomDRSub_A1

open GeomDRSub

lemma cube_convex (d : ℕ) : Convex ℝ (cube d) := by
  intro x hx y hy a b ha hb hab i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain ⟨hx0, hx1⟩ := hx i
  obtain ⟨hy0, hy1⟩ := hy i
  constructor
  · positivity
  · nlinarith

lemma cube_interior (d : ℕ) : (interior (cube d)).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun _ => (1 / 2 : ℝ)), ?_⟩
  rw [mem_interior]
  refine ⟨Metric.ball (WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))) (1 / 2), ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (by norm_num)⟩
  intro y hy i
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h1 : |y i - 1 / 2| ≤ ‖y - WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))‖ := by
    have := PiLp.norm_apply_le (y - WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))) i
    simpa [Real.norm_eq_abs] using this
  have h2 := abs_lt.1 (lt_of_le_of_lt h1 hy)
  constructor <;> linarith [h2.1, h2.2]

lemma inner_grad {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (y v : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (gradQ f y) v = fderivWithin ℝ f (cube d) y v := by
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
    simp
  conv_rhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [gradQ, pd, mul_comm]

end Aux_GeomDRSub_A1

open GeomDRSub Aux_GeomDRSub_A1 in
theorem solution {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContDiffOn ℝ 1 f (cube d))
    (a b : EuclideanSpace ℝ (Fin d)) (ha : a ∈ cube d) (hb : b ∈ cube d) :
    f b - f a = ∫ t in (0 : ℝ)..1, inner ℝ (gradQ f (a + t • (b - a))) (b - a) := by
  set γ : ℝ → EuclideanSpace ℝ (Fin d) := fun t => a + t • (b - a) with hγ
  have hconv := cube_convex d
  have hU : UniqueDiffOn ℝ (cube d) := uniqueDiffOn_convex hconv (cube_interior d)
  have hmaps : Set.MapsTo γ (Set.Icc 0 1) (cube d) := by
    intro t ht
    have : γ t = (1 - t) • a + t • b := by
      simp only [hγ]; rw [smul_sub, sub_smul, one_smul]; abel
    rw [this]
    exact hconv ha hb (by linarith [ht.2]) ht.1 (by ring)
  have hγd : ∀ t, HasDerivAt γ (b - a) t := by
    intro t
    have := ((hasDerivAt_id t).smul_const (b - a)).const_add a
    simpa [hγ] using this
  have hdiff : DifferentiableOn ℝ f (cube d) := hf.differentiableOn one_ne_zero
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (f ∘ γ) (fderivWithin ℝ f (cube d) (γ t) (b - a)) (Set.Icc 0 1) t := by
    intro t ht
    have h1 : HasFDerivWithinAt f (fderivWithin ℝ f (cube d) (γ t)) (cube d) (γ t) :=
      (hdiff _ (hmaps ht)).hasFDerivWithinAt
    exact h1.comp_hasDerivWithinAt t (hγd t).hasDerivWithinAt hmaps
  have hcont' : ContinuousOn (fun t => fderivWithin ℝ f (cube d) (γ t)) (Set.Icc 0 1) :=
    (hf.continuousOn_fderivWithin hU le_rfl).comp
      ((continuous_const.add (continuous_id.smul continuous_const)).continuousOn) hmaps
  have hint : IntervalIntegrable (fun t => inner ℝ (gradQ f (a + t • (b - a))) (b - a))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    have : (fun t => inner ℝ (gradQ f (a + t • (b - a))) (b - a))
        = fun t => fderivWithin ℝ f (cube d) (γ t) (b - a) := by
      funext t; rw [inner_grad]
    rw [this]
    exact hcont'.clm_apply continuousOn_const
  have hfc : ContinuousOn (f ∘ γ) (Set.Icc 0 1) :=
    hf.continuousOn.comp ((continuous_const.add (continuous_id.smul continuous_const)).continuousOn)
      hmaps
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hfc
    (fun t ht => by
      have h := hderiv t (Set.Ioo_subset_Icc_self ht)
      have hmem : Set.Icc (0 : ℝ) 1 ∈ nhds t := Icc_mem_nhds ht.1 ht.2
      have := h.hasDerivAt hmem
      rw [← inner_grad] at this
      exact this) hint]
  simp [hγ]
