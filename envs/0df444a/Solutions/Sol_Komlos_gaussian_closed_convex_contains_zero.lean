-- Prove2me | solution 1 for Komlos.gaussian_closed_convex_contains_zero
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:44:00.347262+00:00
-- url     : https://prove2.me/submissions/937f8f04-10ba-47dc-b7fb-3db31d706669

import Definitions.Def_Komlos_model
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace GaussianConvexOrigin

lemma std_open_pos (m : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).IsOpenPosMeasure := by
  let : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:ℝ≥0) ≠ 0)).isOpenPosMeasure
  rw [← map_pi_eq_stdGaussian]
  exact (show Continuous (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) from
    by fun_prop).isOpenPosMeasure_map (fun x => ⟨WithLp.ofLp x, by simp⟩)

lemma std_neg (m : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).map Neg.neg =
      stdGaussian (EuclideanSpace ℝ (Fin m)) := by
  exact stdGaussian_map (LinearIsometryEquiv.neg ℝ)

end GaussianConvexOrigin

open GaussianConvexOrigin

theorem solution (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (hmass : (1/2:ℝ) ≤ (stdGaussian (EuclideanSpace ℝ (Fin m))).real K) :
    (0 : EuclideanSpace ℝ (Fin m)) ∈ K := by
  classical
  let mu := stdGaussian (EuclideanSpace ℝ (Fin m))
  let : mu.IsOpenPosMeasure := std_open_pos m
  by_contra hzero
  let N := Neg.neg ⁻¹' K
  have hN : IsClosed N := hclosed.preimage continuous_neg
  have hd : Disjoint K N := by
    rw [Set.disjoint_left]
    intro x hx hn
    apply hzero
    have hn' : -x ∈ K := hn
    have h := hconv hx hn' (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num)
    simpa using h
  have hmeasureN : mu.real N = mu.real K := by
    have hm := map_measureReal_apply (μ := stdGaussian (EuclideanSpace ℝ (Fin m)))
      (f := Neg.neg) (by fun_prop) hclosed.measurableSet
    rw [std_neg m] at hm
    exact hm.symm
  have hu : IsClosed (K ∪ N) := hclosed.union hN
  have hnonempty : ((K ∪ N)ᶜ).Nonempty := by
    refine ⟨0, ?_⟩
    simp [N,hzero]
  have hpositive : 0 < mu.real ((K ∪ N)ᶜ) := by
    exact ENNReal.toReal_pos (hu.isOpen_compl.measure_pos mu hnonempty).ne' (by finiteness)
  have hadd := measureReal_add_measureReal_compl (μ := mu) hu.measurableSet
  rw [measureReal_union hd hN.measurableSet, hmeasureN, probReal_univ] at hadd
  dsimp [mu] at hadd hpositive
  linarith

#print axioms solution
