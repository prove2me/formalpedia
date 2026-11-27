-- Prove2me | solution 1 for Kyprianou.Ch04.pathWeightUniformLipschitzV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:22:03.128096+00:00
-- url     : https://prove2.me/submissions/fcbdb3ea-ac0d-4b31-99bf-586b2ae9c23e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_positiveLeftDifferenceBoundV1
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Bounded differentiable state weights along measurable left-limit paths
are integrable on the clock and inherit a uniform Lipschitz perturbation bound. -/
theorem solution (Y Z L R : NNReal → ℝ) (T : NNReal)
    (g : ℝ → ℝ → ℝ) (K d : ℝ)
    (hL : Measurable L) (hR : Measurable R)
    (hY : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (hZ : ∀ t, 0 < t → Tendsto Z (nhdsWithin t (Iio t)) (nhds (R t)))
    (hb : ∀ t ≤ T, |Y t - Z t| ≤ d)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hg' : ∀ s, Differentiable ℝ (g s))
    (hK : ∀ s x, 0 ≤ s → |g s x| ≤ K)
    (hd : ∀ s x, 0 ≤ s → |deriv (g s) x| ≤ K) :
    IntegrableOn (fun s : ℝ => g (s.toNNReal : ℝ) (L s.toNNReal))
      (Ioc (0 : ℝ) (T : ℝ)) ∧
    IntegrableOn (fun s : ℝ => g (s.toNNReal : ℝ) (R s.toNNReal))
      (Ioc (0 : ℝ) (T : ℝ)) ∧
    ∀ t ≤ T, 0 < t → |g t (L t) - g t (R t)| ≤ K * d := by
  have hKg : 0 ≤ K := (abs_nonneg _).trans (hK 0 0 le_rfl)
  have hgc : Continuous (fun p : ℝ × ℝ => g (max 0 p.1) p.2) :=
    hg.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
      (fun p => ⟨(show (max 0 p.1) ∈ Ici (0 : ℝ) by simp),mem_univ _⟩)
  have hInt (A : NNReal → ℝ) (hA : Measurable A) :
      IntegrableOn (fun s : ℝ => g (s.toNNReal : ℝ) (A s.toNNReal))
        (Ioc (0 : ℝ) (T : ℝ)) := by
    have hm : Measurable (fun s : ℝ => g (s.toNNReal : ℝ) (A s.toNNReal)) := by
      have hm' := hgc.measurable.comp (measurable_id.prodMk
        (hA.comp measurable_real_toNNReal))
      have heq : (fun s : ℝ => g (s.toNNReal : ℝ) (A s.toNNReal)) =
          (fun p : ℝ × ℝ => g (max 0 p.1) p.2) ∘
            (fun s : ℝ => (s,A s.toNNReal)) := by
        funext s
        simp [Real.coe_toNNReal,max_comm]
      rw [heq]
      exact hm'
    apply (integrable_const K).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun s => by
      simpa only [Real.norm_eq_abs] using hK (s.toNNReal : ℝ) (A s.toNNReal) s.toNNReal.coe_nonneg
  refine ⟨hInt L hL,hInt R hR,?_⟩
  intro t ht ht0
  have hleft := Kyprianou.Ch04.positiveLeftDifferenceBoundV1 Y Z L R T d hY hZ hb t ht ht0
  have hl : |g (t : ℝ) (L t) - g (t : ℝ) (R t)| ≤ K * |L t - R t| := by
    simpa only [Real.norm_eq_abs] using
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun u _ => hg' t u) (fun u _ => by simpa only [Real.norm_eq_abs] using hd t u t.coe_nonneg)
        (Set.mem_univ (R t)) (Set.mem_univ (L t))
  exact hl.trans (mul_le_mul_of_nonneg_left hleft hKg)
