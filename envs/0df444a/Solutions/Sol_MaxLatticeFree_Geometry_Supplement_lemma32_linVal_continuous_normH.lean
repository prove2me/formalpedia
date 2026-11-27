-- Prove2me | solution 1 for MaxLatticeFree.Geometry.Supplement.lemma32_linVal_continuous_normH
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:40.819666+00:00
-- url     : https://prove2.me/submissions/d700dded-65e8-4179-a9eb-d8acb37090da

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities
import Definitions.Def_MaxLatticeFree_Geometry_Supplement_NormH

open MaxLatticeFree.Inequalities

open MaxLatticeFree
open MaxLatticeFree.Geometry
open MaxLatticeFree.Geometry.Supplement

theorem solution {q : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (ψ : W → ℝ) (hcont : Continuous ψ) (hhom : IsPositivelyHomogeneous ψ) :
    ∀ s : W →₀ ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s' : W →₀ ℝ, normH (s' - s) < δ → |linVal ψ s' - linVal ψ s| < ε := by
        have h0 : ψ 0 = 0 := by
          have := hhom 0 0 le_rfl
          simpa using this
        obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.continuous_iff.mp hcont 0 1 one_pos
        have hbound : ∀ r : W, |ψ r| ≤ (2 / δ0) * ‖(r : EuclideanSpace ℝ (Fin q))‖ := by
          intro r
          by_cases hr : r = 0
          · subst hr; simp [h0]
          · have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
            set c : ℝ := δ0 / (2 * ‖r‖) with hc
            have hcpos : 0 < c := by positivity
            have hdist : dist (c • r) 0 < δ0 := by
              rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hcpos.le, hc]
              field_simp
              linarith
            have h1 := hδ0' (c • r) hdist
            rw [h0, dist_zero_right, Real.norm_eq_abs, hhom r c hcpos.le, abs_mul,
              abs_of_pos hcpos] at h1
            have : ‖(r : EuclideanSpace ℝ (Fin q))‖ = ‖r‖ := rfl
            rw [this]
            have h2 : |ψ r| < 1 / c := by
              rw [lt_div_iff₀ hcpos]; linarith
            have h3 : 1 / c = (2 / δ0) * ‖r‖ := by
              rw [hc]; field_simp
            linarith
        set K : ℝ := 2 / δ0 with hK
        have hKpos : 0 < K := by positivity
        have hlin : ∀ t : W →₀ ℝ, |linVal ψ t| ≤ K * normH t := by
          intro t
          unfold linVal normH
          have hs : t.sum (fun r c => ‖(r : EuclideanSpace ℝ (Fin q))‖ * |c|) ≥ 0 := by
            apply Finset.sum_nonneg; intro i _; positivity
          calc |t.sum (fun r c => ψ r * c)|
              ≤ t.sum (fun r c => |ψ r * c|) := Finset.abs_sum_le_sum_abs _ _
            _ ≤ t.sum (fun r c => K * (‖(r : EuclideanSpace ℝ (Fin q))‖ * |c|)) := by
                apply Finset.sum_le_sum
                intro i _
                simp only []; rw [abs_mul, ← mul_assoc]
                exact mul_le_mul_of_nonneg_right (hbound i) (abs_nonneg _)
            _ = K * t.sum (fun r c => ‖(r : EuclideanSpace ℝ (Fin q))‖ * |c|) := by
                unfold Finsupp.sum; rw [Finset.mul_sum]
            _ ≤ K * (|t 0| + t.sum (fun r c => ‖(r : EuclideanSpace ℝ (Fin q))‖ * |c|)) := by
                apply mul_le_mul_of_nonneg_left _ hKpos.le
                linarith [abs_nonneg (t 0)]
        intro s ε hε
        refine ⟨ε / K, by positivity, ?_⟩
        intro s' hs'
        have hsub : linVal ψ s' - linVal ψ s = linVal ψ (s' - s) := by
          unfold linVal
          rw [Finsupp.sum_sub_index]
          intro a b1 b2; ring
        rw [hsub]
        calc |linVal ψ (s' - s)| ≤ K * normH (s' - s) := hlin _
          _ < K * (ε / K) := mul_lt_mul_of_pos_left hs' hKpos
          _ = ε := by field_simp
