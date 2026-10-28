-- Prove2me | solution 1 for KyleProduction.Monopoly.firm_value_law
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:48:21.905617+00:00
-- url     : https://prove2.me/submissions/1a7e9e4b-3f4e-4c4a-af2e-767ff4fce861

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

open MeasureTheory ProbabilityTheory

namespace Aux_firm_value_law
open KyleProduction.Monopoly

theorem law_eq (P : Params) (q : ℝ) :
    (lawA P).map (firmValue q) =
      gaussianReal (q * (postMean P - q)) (q ^ 2 * postVar P).toNNReal := by
  have hf : firmValue q = (fun x : ℝ => q * x) ∘ (fun a : ℝ => a - q) := by
    funext a; simp [firmValue]
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold lawA
  rw [gaussianReal_map_sub_const, gaussianReal_map_const_mul]
  congr 1
  rw [Real.toNNReal_mul (sq_nonneg q)]
  congr 1
  ext
  simp [Real.coe_toNNReal _ (sq_nonneg q)]

end Aux_firm_value_law

open KyleProduction.Monopoly in
theorem solution (P : Params) (hS : P.Standing) (q : ℝ) :
    (lawA P).map (firmValue q) =
      gaussianReal (q * (postMean P - q)) (q ^ 2 * postVar P).toNNReal ∧
    expFirmValue P q = q * (postMean P - q) := by
  have h1 := Aux_firm_value_law.law_eq P q
  refine ⟨h1, ?_⟩
  have hm : Measurable (firmValue q) := by unfold firmValue; fun_prop
  unfold expFirmValue
  have : ∫ a, firmValue q a ∂lawA P = ∫ x, x ∂((lawA P).map (firmValue q)) :=
    (integral_map hm.aemeasurable aestronglyMeasurable_id).symm
  rw [this, h1, integral_id_gaussianReal]
