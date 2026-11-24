-- Prove2me | solution 1 for GlobalTheory.SW.HeisH.expo_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:13.638993+00:00
-- url     : https://prove2.me/submissions/4b502b5f-1e51-4b07-8eed-b9c23f932ed5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {n N : ℕ}
namespace GlobalTheory.SW.HeisH
theorem _root_.solution {Ji Jp W Z K : Matrix (Fin N) (Fin N) ℂ}
    {P Q P' Q' w : Matrix (Fin n) (Fin N) ℂ} {Ps Qs Ps' Qs' u : Matrix (Fin N) (Fin n) ℂ}
    (hr : (Q + P * Z) * Ji = Q' + P' * W) (hs : Jp * (Qs + Z * Ps) = Qs' + W * Ps')
    (hrK : (Q + P * Z) * K = P - P' * Jp)
    (hKs : K * (Qs + Z * Ps) = Ps - Ji * Ps') :
    2 * ((P' * W * Ps').trace + (P' * (Jp * u)).trace + (w * Ji * Ps').trace) +
      ((Q' * Ps').trace + (P' * Qs').trace) +
      2 * ((w + Q + P * Z) * K * (u + Qs + Z * Ps)).trace =
    2 * (w * K * u).trace + (2 * ((P * Z * Ps).trace + (P * u).trace + (w * Ps).trace) +
      ((Q * Ps).trace + (P * Qs).trace)) := by
  have e0 : (w + Q + P * Z) * K * (u + Qs + Z * Ps) = w * K * u + w * (K * (Qs + Z * Ps)) +
      (Q + P * Z) * K * u + (Q + P * Z) * K * (Qs + Z * Ps) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
  have e1 : (Q + P * Z) * K * (Qs + Z * Ps) = P * Qs + P * Z * Ps - (P' * Qs' + P' * W * Ps') := by
    rw [hrK, Matrix.sub_mul, Matrix.mul_assoc P' Jp, hs]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
  have e2 : (Q + P * Z) * K * (Qs + Z * Ps) = Q * Ps + P * Z * Ps - (Q' * Ps' + P' * W * Ps') := by
    rw [Matrix.mul_assoc, hKs, Matrix.mul_sub, ← Matrix.mul_assoc, hr]
    simp only [Matrix.add_mul]
  have t0 := congrArg Matrix.trace e0
  have t1 := congrArg Matrix.trace e1
  have t2 := congrArg Matrix.trace e2
  rw [hKs, hrK] at t0
  rw [hrK] at t1 t2
  simp only [trace_add, trace_sub, Matrix.mul_sub w, Matrix.sub_mul _ _ u, Matrix.mul_assoc] at t0 t1 t2 ⊢
  linear_combination 2 * t0 + t1 + t2
end GlobalTheory.SW.HeisH
