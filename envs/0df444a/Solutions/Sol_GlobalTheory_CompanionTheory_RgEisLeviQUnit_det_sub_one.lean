-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.det_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:29.684948+00:00
-- url     : https://prove2.me/submissions/b3254559-22d9-4845-8dfd-0e4c156c9ddc

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
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution {α : Type} [Fintype α] [DecidableEq α] {S : Set α} {_ : Fintype S} {_ : DecidableEq S}
    (g : Matrix α α R) (h : ∀ a b : S, g a.1 b.1 = if a = b then 1 else 0) :
    (g.submatrix (Subtype.val : S → α) Subtype.val).det = 1 := by
  have : g.submatrix (Subtype.val : S → α) (Subtype.val : S → α) = 1 := by
    ext a b
    rw [Matrix.submatrix_apply, h, Matrix.one_apply]
  rw [this, Matrix.det_one]
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
