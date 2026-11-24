-- Prove2me | solution 1 for GlobalTheory.T.exists_prime_idempotent_integralAdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:17.356426+00:00
-- url     : https://prove2.me/submissions/c9b1a5db-77dd-4467-af59-dd7bf77afebb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdeles
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPrimeIdempotentIntegralAdelesStatement
import Theorems.Thm_GlobalTheory_RowLev_exists_prime_idempotent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E)), ∃ ε : IntAf I.F I.E, ε * ε = ε ∧ 1 - ε ∈ extId I w.asIdeal ∧ (∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ε ∈ extId I u.asIdeal) ∧ (∀ z : IntAf I.F I.E, z ∉ extId I w.asIdeal → ∃ t : IntAf I.F I.E, z * t * ε = ε) ∧ (¬ IsConj I w w → (ε : (I.E ⊗[I.F] Af I.F)) * Formalism.UG.sigR I.cm.sig (Af I.F) ε = 0) := by
  first | exact @GlobalTheory.RowLev.exists_prime_idempotent | exact GlobalTheory.RowLev.exists_prime_idempotent | (intros; apply GlobalTheory.RowLev.exists_prime_idempotent <;> assumption)
end _root_.GlobalTheory.T
