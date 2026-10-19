-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_one_sub_two_mul_Gamma_of_stieltjesPhaseProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/8accc946-a11f-44d7-befa-b0b901626b4b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_betaMap_half_half_ae_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_arcsine_integral_self_div_add
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_ambient_quadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exp_neg_stieltjesPhase_eq_product
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_quadratic_spectralAtom_identity
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_integral_exp_neg_stieltjesPhase_eq_one_sub_two_Gamma
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhaseProduct_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhaseProduct_le_one
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r j : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
    (hAB : Interlacing A B) (c : ℝ)
    (hproduct : ∀ t : ℝ, 0 < t →
      Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
        atTop (𝓝 (c * stieltjesPhaseProduct A B t))) :
    Tendsto (fun n => 1 - 2 * Gamma (a n) (b n))
      atTop (𝓝 (c * (1 - 2 * Gamma A B))) := by
  have hdom :
      Tendsto
        (fun n => ∫ t : ℝ,
          stieltjesPhaseProduct (a n) (b n) t ∂compactificationArcsineMeasure_metriccodes2_275785c2)
        atTop
        (𝓝 (∫ t : ℝ,
          c * stieltjesPhaseProduct A B t ∂compactificationArcsineMeasure_metriccodes2_275785c2)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
    · intro n
      apply Measurable.aestronglyMeasurable
      unfold stieltjesPhaseProduct
      fun_prop
    · exact integrable_const (1 : ℝ)
    · intro n
      filter_upwards [ArcsineTransform.betaMap_half_half_ae_pos] with t ht
      rw [Real.norm_eq_abs,
        abs_of_pos (stieltjesPhaseProduct_pos (h n) ht)]
      exact stieltjesPhaseProduct_le_one (h n) ht
    · filter_upwards [ArcsineTransform.betaMap_half_half_ae_pos] with t ht
      exact hproduct t ht
  have hnormalizer {q : ℕ}
      (x : Fin (q + 1) → ℝ) (y : Fin q → ℝ)
      (hxy : Interlacing x y) :
      (∫ t : ℝ, stieltjesPhaseProduct x y t ∂compactificationArcsineMeasure_metriccodes2_275785c2) =
        1 - 2 * Gamma x y := by
    calc
      (∫ t : ℝ,
          stieltjesPhaseProduct x y t ∂compactificationArcsineMeasure_metriccodes2_275785c2) =
        ∫ t : ℝ,
          Real.exp (-stieltjesPhase x y t) ∂compactificationArcsineMeasure_metriccodes2_275785c2 := by
            apply integral_congr_ae
            filter_upwards [ArcsineTransform.betaMap_half_half_ae_pos]
              with t ht
            exact (exp_neg_stieltjesPhase_eq_product hxy ht).symm
      _ = 1 - 2 * Gamma x y := by
        apply integral_exp_neg_stieltjesPhase_eq_one_sub_two_Gamma hxy
          compactificationArcsineMeasure_metriccodes2_275785c2
          ArcsineTransform.betaMap_half_half_ae_pos
        intro i
        rw [ArcsineTransform.arcsine_integral_self_div_add
          (hxy.ambient_quadratic_nonneg i),
          quadratic_spectralAtom_identity (hxy.ambient_nonneg i)]
  have htarget :
      (∫ t : ℝ,
        c * stieltjesPhaseProduct A B t ∂compactificationArcsineMeasure_metriccodes2_275785c2) =
        c * (1 - 2 * Gamma A B) := by
    rw [integral_const_mul, hnormalizer A B hAB]
  simpa only [hnormalizer (a _) (b _) (h _), htarget] using hdom
end MetricCodes.Spherical.HigherHierarchy
