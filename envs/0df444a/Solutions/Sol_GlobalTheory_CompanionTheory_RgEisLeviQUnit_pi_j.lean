-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.pi_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:42:56.096793+00:00
-- url     : https://prove2.me/submissions/a98517b9-4f6b-46a2-8ff8-26a3c703beb6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_sub_jM

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
theorem _root_.solution (hσ : ∀ x, A.σ (A.σ x) = x) (m : A.U ε ↥sᶜ) : piQ A ε hσ (jQ (s := s) A ε m) = m :=
  Subtype.ext (Units.ext (sub_jM emb_inj _))
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
