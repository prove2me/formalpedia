-- Prove2me | solution 1 for Kyprianou.Ch04.physicalWeightedIntegralErrorRealClockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:28:45.546797+00:00
-- url     : https://prove2.me/submissions/13b14a15-554c-4439-be80-7645413def24

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_physicalWeightedIntegralErrorV1
import Theorems.Thm_Kyprianou_Ch04_pathWeightUniformLipschitzV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Apply the physical variation estimate to left-limit weights and the actual clock. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j Y Z L U : NNReal → ℝ) (g : ℝ → ℝ → ℝ)
    (b K d r : ℝ) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hS : ∀ s ∈ S, 0 < s ∧ s ≤ T ∧ 1/2 < |j s|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ s ∈ S, Measure.dirac ((s : ℝ),j s))
    (hL : Measurable L) (hU : Measurable U)
    (hY : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (hZ : ∀ t, 0 < t → Tendsto Z (nhdsWithin t (Iio t)) (nhds (U t)))
    (hb : ∀ t ≤ T, |Y t - Z t| ≤ d)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hg' : ∀ s, Differentiable ℝ (g s))
    (hKg : ∀ s x, 0 ≤ s → |g s x| ≤ K)
    (hKd : ∀ s x, 0 ≤ s → |deriv (g s) x| ≤ K)
    (A B : NNReal → ℝ) (hAB : ∀ t ≤ T, |A t - B t| ≤ r) :
    ∀ t ≤ T,
      |(b * (∫ s in Icc (0 : ℝ) (t : ℝ), g (s.toNNReal : ℝ) (L s.toNNReal)) +
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * g (z.1.toNNReal : ℝ) (L z.1.toNNReal) ∂ R) + A t) -
       (b * (∫ s in Icc (0 : ℝ) (t : ℝ), g s (U s.toNNReal)) +
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * g z.1 (U z.1.toNNReal) ∂ R) + B t)| ≤
      K * (|b| * (T : ℝ) + (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ
          {x : ℝ | 1/2 < |x|}, |z.2| ∂ R)) * d + r := by
  intro t ht
  obtain ⟨hI,hI',hW⟩ := Kyprianou.Ch04.pathWeightUniformLipschitzV1 Y Z L U T g K d
    hL hU hY hZ hb hg hg' hKg hKd
  have hV := Kyprianou.Ch04.physicalWeightedIntegralErrorV1 R T S j
    (fun s => g s (L s)) (fun s => g s (U s)) b (K*d) hS hR
    (mul_nonneg hK hd) hI hI' hW t ht
  let D : Set (ℝ × ℝ) := Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  have hc : (∫ s in Icc (0 : ℝ) (t : ℝ), g (s.toNNReal : ℝ) (U s.toNNReal)) =
      ∫ s in Icc (0 : ℝ) (t : ℝ), g s (U s.toNNReal) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp [Real.coe_toNNReal, max_eq_left hs.1, max_eq_right hs.1]
  have hj : (∫ z in D, z.2 * g (z.1.toNNReal : ℝ) (U z.1.toNNReal) ∂ R) =
      ∫ z in D, z.2 * g z.1 (U z.1.toNNReal) ∂ R := by
    apply setIntegral_congr_fun (measurableSet_Icc.prod
      (measurableSet_le measurable_const measurable_id.abs))
    intro z hz
    simp [Real.coe_toNNReal,max_eq_left hz.1.1,max_eq_right hz.1.1]
  rw [← hc,← hj]
  rw [show ∀ a c u v : ℝ, (a+u)-(c+v)=(a-c)+(u-v) by intros; ring]
  refine (abs_add_le _ _).trans ?_
  exact (add_le_add hV (hAB t ht)).trans_eq (by ring)
