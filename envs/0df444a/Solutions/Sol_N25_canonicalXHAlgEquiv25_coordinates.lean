-- Prove2me | solution 1 for N25.canonicalXHAlgEquiv25_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:18:35.253543+00:00
-- url     : https://prove2.me/submissions/8ccce3ed-8d45-44b2-8c30-cee040d89b70

import Definitions.Def_N25_CanonicalModularDictionary
import Theorems.Thm_N25_unitRelation25_qExpansion_certificate
import Theorems.Thm_N25_U25_zero_transcendental
import Theorems.Thm_N25_unitPlaneToXH25_coordinates

/-! Coordinates, degrees and orders under the canonical modular dictionary. -/
namespace N25

/-- The field dictionary retains the prescribed modular-unit coordinates. -/
theorem _root_.solution :
    canonicalXHAlgEquiv25 canonicalFunctionU25 = U25 0 ∧
      canonicalXHAlgEquiv25 canonicalFunctionV25 = U25 0 / U25 1 := by
  let φ : UnitPlaneFF25 →ₐ[ℚ] N25.Endgame.FQ :=
    unitPlaneFieldPointLift25 (U25 0) (U25 0 / U25 1)
      (unitRelation25_qExpansion_certificate ℚ) U25_zero_transcendental
  constructor
  · change φ (canonicalUnitPlaneAlgEquiv25.symm
      (canonicalUnitPlaneAlgEquiv25 unitPlaneFunctionU25)) = U25 0
    rw [AlgEquiv.symm_apply_apply]
    exact unitPlaneToXH25_coordinates.1
  · change φ (canonicalUnitPlaneAlgEquiv25.symm
      (canonicalUnitPlaneAlgEquiv25 unitPlaneFunctionV25)) = U25 0 / U25 1
    rw [AlgEquiv.symm_apply_apply]
    exact unitPlaneToXH25_coordinates.2

end N25
