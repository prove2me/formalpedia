-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.det_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:28.628911+00:00
-- url     : https://prove2.me/submissions/98de0fd6-f39f-42a5-9596-e7e714132519

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
theorem _root_.solution {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (f : β → α)
    (hf : Function.Injective f) (T : Set α) (hT : T = Set.range f) {_ : Fintype T} {_ : DecidableEq T} (g : Matrix α α R) :
    (g.submatrix (Subtype.val : T → α) Subtype.val).det = (g.submatrix f f).det := by
  subst hT
  rw [← Matrix.det_submatrix_equiv_self (Equiv.ofInjective f hf) (g.submatrix _ _), Matrix.submatrix_submatrix]
  rfl
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
