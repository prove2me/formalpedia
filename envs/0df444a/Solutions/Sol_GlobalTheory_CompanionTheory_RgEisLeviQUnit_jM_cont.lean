-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.jM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:30.78708+00:00
-- url     : https://prove2.me/submissions/b4a7e87a-789f-4e17-b51b-89885105cdc2

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
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ)
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution : Continuous (jM (emb s) : Matrix (↥sᶜ ⊕ ↥sᶜ) (↥sᶜ ⊕ ↥sᶜ) R → Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
  unfold jM
  exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).add continuous_const
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
