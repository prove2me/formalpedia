-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.SphLaw.diag_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:29.690123+00:00
-- url     : https://prove2.me/submissions/51ca1c8e-3f78-4784-835f-16a776e15a6c

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
theorem _root_.solution {F : Type} [Field F] {c : ℕ} {a b : Matrix (Fin c) (Fin c) F}
    (ha : a.BlockTriangular id) (hb : b.BlockTriangular id) (i : Fin c) :
    (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [ha h, zero_mul]
    · rw [hb h, mul_zero]
  · simp
end GlobalTheory.CompanionTheory.QL.SphLaw
