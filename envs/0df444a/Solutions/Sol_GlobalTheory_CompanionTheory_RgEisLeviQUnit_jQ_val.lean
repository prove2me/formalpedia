-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.jQ_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:35.706294+00:00
-- url     : https://prove2.me/submissions/30896fec-7621-4685-b912-f5465697ad26

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
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
variable [Fintype ↥sᶜ] [DecidableEq ↥sᶜ]
variable (A : Ad E R) (ε : ℤˣ)
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (m : A.U ε ↥sᶜ) : ((jQ A ε m : A.U ε ι).1 : GL (ι ⊕ ι) R) = jG R m.1 := rfl
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
