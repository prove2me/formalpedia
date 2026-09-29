-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisProd0001GraphCenterD.qJetBox_contains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:52:06.500195+00:00
-- url     : https://prove2.me/submissions/f34ce618-ee87-47be-a1bc-fa762d275c76

import Definitions.Def_GeneralCK_E8_Prod0001_graph_mixed_data
import Definitions.Def_GeneralCK_E8_Prod0001_inputs
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_GeneralCK_Certificates_E8TAxisStableInterval_checked_stable_contains_canonical

section
namespace GeneralCK.Certificates.E8TAxisProd0001StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000





theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide













































































end GeneralCK.Certificates.E8TAxisProd0001StableWitnesses
end

section
namespace GeneralCK.Certificates.E8TAxisProd0001PaddedInputs
open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000



















theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDInput.alpha)
      centerDInput.expNegTwo E8TAxisProd0001StableWitnesses.centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDInput.expNegTwo)
      centerDInput.logOnePlusExp E8TAxisProd0001StableWitnesses.centerDLogWitness = true := by decide























end GeneralCK.Certificates.E8TAxisProd0001PaddedInputs
end

section
namespace GeneralCK.Certificates.E8TAxisProd0001GraphCenterD
open DyadicInterval E8TAxisStableInterval E8TAxisProd0001PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000



theorem one_checked : DyadicJet5Enclosure.const precision 1 = one := by decide



theorem two_checked : DyadicJet5Enclosure.const precision 2 = two := by decide



theorem four_checked : DyadicJet5Enclosure.const precision 4 = four := by decide



theorem alphaJet_checked : DyadicJet5Enclosure.variableJet centerDInput.alpha = alphaJet := by decide



theorem logtwo_checked : constant centerDInput.logTwo = logtwo := by decide



theorem zData_checked : zBox centerDInput = zData := by decide



theorem onePlusZ_checked : one.add zData = onePlusZ := by decide



theorem negativeZ_checked : negative zData = negativeZ := by decide



theorem rNumerator_checked : one.add negativeZ = rNumerator := by decide



theorem onePlusZInv_checked : onePlusZ.inv = onePlusZInv := by decide



theorem rData_checked : rNumerator.mul onePlusZInv = rData := by decide



theorem qNumerator_checked : four.mul zData = qNumerator := by decide



theorem qDenominator_checked : onePlusZ.mul onePlusZ = qDenominator := by decide



theorem qDenominatorInv_checked : qDenominator.inv = qDenominatorInv := by decide



theorem qData_checked : qNumerator.mul qDenominatorInv = qData := by decide



theorem l1Data_checked : onePlusZ.log centerDInput.logOnePlusExp = l1Data := by decide



theorem ellData_checked : alphaJet.add l1Data = ellData := by decide



theorem twiceAlpha_checked : two.mul alphaJet = twiceAlpha := by decide



theorem twiceAlphaZ_checked : twiceAlpha.mul zData = twiceAlphaZ := by decide



theorem hCorrection_checked : twiceAlphaZ.mul onePlusZInv = hCorrection := by decide



theorem hData_checked : l1Data.add hCorrection = hData := by decide



theorem xNumerator_checked : logtwo.mul rData = xNumerator := by decide



theorem xDenominator_checked : two.mul hData = xDenominator := by decide



theorem xDenominatorInv_checked : xDenominator.inv = xDenominatorInv := by decide



theorem xJetBox_checked : xNumerator.mul xDenominatorInv = xJetBox := by decide



theorem logtwoInv_checked : logtwo.inv = logtwoInv := by decide



theorem yConstant_checked : two.mul logtwoInv = yConstant := by decide



theorem yNumerator_checked : rData.mul hData = yNumerator := by decide



theorem yDenominator_checked : qData.mul ellData = yDenominator := by decide



theorem yDenominatorInv_checked : yDenominator.inv = yDenominatorInv := by decide



theorem yCorrection_checked : yNumerator.mul yDenominatorInv = yCorrection := by decide



theorem ySum_checked : alphaJet.add yCorrection = ySum := by decide



theorem yJetBox_checked : yConstant.mul ySum = yJetBox := by decide



theorem qJetBox_checked : E8TAxisReparamInterval.eval xJetBox yJetBox = qJetBox := by decide

theorem onePlusZBox_eq : onePlusZBox centerDInput = onePlusZ := by
  simp only [onePlusZBox, one_checked, zData_checked, onePlusZ_checked]

theorem rBox_eq : rBox centerDInput = rData := by
  simp only [rBox, one_checked, zData_checked, onePlusZBox_eq, negativeZ_checked, rNumerator_checked, onePlusZInv_checked, rData_checked]

theorem qBox_eq : qBox centerDInput = qData := by
  simp only [qBox, four_checked, zData_checked, onePlusZBox_eq, qNumerator_checked, qDenominator_checked, qDenominatorInv_checked, qData_checked]

theorem l1Box_eq : l1Box centerDInput = l1Data := by
  simp only [l1Box, onePlusZBox_eq, l1Data_checked]

theorem ellBox_eq : ellBox centerDInput = ellData := by
  simp only [ellBox, alphaJet_checked, l1Box_eq, ellData_checked]

theorem hBox_eq : hBox centerDInput = hData := by
  simp only [hBox, l1Box_eq, two_checked, alphaJet_checked, zData_checked, onePlusZBox_eq, twiceAlpha_checked, twiceAlphaZ_checked, onePlusZInv_checked, hCorrection_checked, hData_checked]

theorem xBox_eq : xBox centerDInput = xJetBox := by
  simp only [xBox, logtwo_checked, rBox_eq, two_checked, hBox_eq, xNumerator_checked, xDenominator_checked, xDenominatorInv_checked, xJetBox_checked]

theorem yBox_eq : yBox centerDInput = yJetBox := by
  simp only [yBox, two_checked, logtwo_checked, alphaJet_checked, rBox_eq, hBox_eq, qBox_eq, ellBox_eq, logtwoInv_checked, yConstant_checked, yNumerator_checked, yDenominator_checked, yDenominatorInv_checked, yCorrection_checked, ySum_checked, yJetBox_checked]

theorem stable_eval_eq :
    E8TAxisReparamInterval.eval (xBox centerDInput) (yBox centerDInput) = qJetBox := by
  rw [xBox_eq, yBox_eq, qJetBox_checked]

theorem denominatorsPositive : DenominatorsPositive centerDInput := by
  simp only [DenominatorsPositive, onePlusZBox_eq, qDenominator_checked,
    two_checked, hBox_eq, xDenominator_checked, qBox_eq, ellBox_eq, yDenominator_checked]
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem yPrime_pos : 0 < (yBox centerDInput).d1.lo := by
  rw [yBox_eq]
  decide





end GeneralCK.Certificates.E8TAxisProd0001GraphCenterD
end

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisProd0001GraphCenterD
open DyadicInterval E8TAxisStableInterval E8TAxisProd0001PaddedInputs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem solution {a : ℝ} (ha : centerDInput.alpha.Contains a) (hapos : 0 < a) :
    qJetBox.Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (E8TAxisStableScalar.Y a) := by
  rw [← stable_eval_eq]
  exact checked_stable_contains_canonical
    centerD_primitive_checks.1 centerD_primitive_checks.2
    E8TAxisProd0001StableWitnesses.logTwo_checked denominatorsPositive yPrime_pos ha hapos
