-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:38.335919+00:00
-- url     : https://prove2.me/submissions/9b085da9-bac1-4f85-bfce-95b601322818

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {α κ β : Type} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (e : κ → α) (g : Matrix α α R) : g.submatrix e e = (Pm R e)ᵀ * g * Pm R e := by
  ext x y
  rw [mul_Pm, Pmt_mul]
  rfl
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
