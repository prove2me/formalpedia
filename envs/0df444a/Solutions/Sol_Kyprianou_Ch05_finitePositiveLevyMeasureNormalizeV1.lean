-- Prove2me | solution 1 for Kyprianou.Ch05.finitePositiveLevyMeasureNormalizeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:06:06.133601+00:00
-- url     : https://prove2.me/submissions/2d85d051-f038-4342-b08b-3d847f9187ff

import Mathlib
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_jumpCount
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05 Set Complex
theorem solution
    (Pi : Measure ℝ) (hs : Pi (Iic (0 : ℝ)) = 0)
    (hf : Pi (Ioi (0 : ℝ)) < ⊤) (hp : 0 < Pi (Ioi (0 : ℝ))) :
    ∃ (r : NNReal) (F : Measure ℝ), 0 < r ∧ IsProbabilityMeasure F ∧
      Pi = (r : ENNReal) • F := by
  have he : Pi Set.univ = Pi (Ioi (0 : ℝ)) := by
    have hu : Ioi (0 : ℝ) ∪ Iic 0 = univ := by ext x; simp
    rw [← hu]
    apply le_antisymm
    · calc
        _ ≤ Pi (Ioi (0 : ℝ)) + Pi (Iic (0 : ℝ)) := measure_union_le _ _
        _ = _ := by rw [hs,add_zero]
    · exact measure_mono subset_union_left
  let r : NNReal := (Pi univ).toNNReal
  have hfin : Pi univ < ⊤ := he ▸ hf
  have hp' : 0 < Pi univ := he ▸ hp
  have hrcoe : (r : ENNReal) = Pi univ := ENNReal.coe_toNNReal (ne_of_lt hfin)
  have hr : 0 < r := ENNReal.toNNReal_pos (ne_of_gt hp') (ne_of_lt hfin)
  let F : Measure ℝ := (r : ENNReal)⁻¹ • Pi
  have hF : IsProbabilityMeasure F := ⟨by
    simp [F,Measure.smul_apply,← hrcoe,ENNReal.inv_mul_cancel,ne_of_gt hr]⟩
  refine ⟨r,F,hr,hF,?_⟩
  change Pi = (r : ENNReal) • ((r : ENNReal)⁻¹ • Pi)
  rw [smul_smul,ENNReal.mul_inv_cancel (by simpa using ne_of_gt hr) (by simp),one_smul]
