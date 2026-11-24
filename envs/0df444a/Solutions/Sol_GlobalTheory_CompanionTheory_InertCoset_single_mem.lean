-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.single_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:55:08.743639+00:00
-- url     : https://prove2.me/submissions/d8479f47-fb48-4f07-b418-3b1fe2061a61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertCoset
theorem _root_.solution (a : Fin n) (c : L) (hc : c ∈ intL L) (i : Fin n) : (Pi.single a c : Fin n → L) i ∈ intL L := by
  rw [Pi.single_apply]
  split_ifs
  · exact hc
  · exact (intL L).zero_mem
end GlobalTheory.CompanionTheory.InertCoset
