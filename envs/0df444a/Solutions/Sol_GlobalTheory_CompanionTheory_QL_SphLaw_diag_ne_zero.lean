-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.SphLaw.diag_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:31.496443+00:00
-- url     : https://prove2.me/submissions/eff2cfd6-2fa4-411a-81dd-97b5df24b236

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangularStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SphericalFunctionInvarianceProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.SphLaw
namespace GlobalTheory.CompanionTheory.QL.SphLaw
theorem _root_.solution {F : Type} [Field F] {c : ℕ} (b : GL (Fin c) F)
    (hb : (b : Matrix (Fin c) (Fin c) F).BlockTriangular id) (i : Fin c) :
    (b : Matrix (Fin c) (Fin c) F) i i ≠ 0 := by
  have h : (b : Matrix (Fin c) (Fin c) F).det ≠ 0 := (Matrix.isUnits_det_units b).ne_zero
  rw [Matrix.det_of_upperTriangular hb] at h
  exact Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)
end GlobalTheory.CompanionTheory.QL.SphLaw
