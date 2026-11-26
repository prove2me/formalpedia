-- Prove2me | solution 1 for Malliavin.ae_eq_zero_of_orthogonal_elementaryPredictable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:35:19.755737+00:00
-- url     : https://prove2.me/submissions/a8fc72d0-ae6e-4b30-ab61-4d6b536d8cc1

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
import Theorems.Thm_Malliavin_integral_rectangle_eq_zero_of_orthogonal
import Theorems.Thm_Malliavin_integral_set_eq_zero_of_rectangles

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (horth : ∀ U : PredictableProcessL2 𝓕 P,
      U ∈ elementaryPredictableSpan (P := P) 𝓕 → ⟪U, g⟫_ℝ = 0) :
    (g : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] 0 := by
  apply lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero
    (predictable_le_prod 𝓕) g (by norm_num) (by norm_num)
  · intro s _hs hμs
    exact integrableOn_Lp_of_measure_ne_top
      (g : TimeProcessL2 P) one_le_two hμs.ne
  · intro s hs hμs
    exact integral_set_eq_zero_of_rectangles 𝓕 g
      (integral_rectangle_eq_zero_of_orthogonal 𝓕 g horth) s hs hμs
end Malliavin
