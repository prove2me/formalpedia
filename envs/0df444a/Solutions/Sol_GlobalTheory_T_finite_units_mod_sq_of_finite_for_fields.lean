-- Prove2me | solution 1 for GlobalTheory.T.finite_units_mod_sq_of_finite_for_fields
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:32:44.186805+00:00
-- url     : https://prove2.me/submissions/ba3e9d8c-268e-4d20-adf2-29004ea05d19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitsModSqFiniteOfFields
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitsModSqFiniteOfFieldsStatement
import Theorems.Thm_GlobalTheory_units_modSq_finite_of_fields


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [CharZero k], (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) → ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by
  first | exact @GlobalTheory.units_modSq_finite_of_fields | exact GlobalTheory.units_modSq_finite_of_fields | (intros; apply GlobalTheory.units_modSq_finite_of_fields <;> assumption)
end _root_.GlobalTheory.T
