-- Prove2me | solution 1 for GlobalTheory.T.unitaryCharacter_kills_unitaryTransvections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:23:04.19479+00:00
-- url     : https://prove2.me/submissions/ec73b198-e368-4bb6-b488-90652fa568ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvections
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvectionsStatement
import Theorems.Thm_GlobalTheory_UTrans_TvKill_char_tvGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ m ∈ GlobalTheory.UTrans.TvGen σ G, X m = 1 := by
  first | exact @GlobalTheory.UTrans.TvKill.char_tvGen | exact GlobalTheory.UTrans.TvKill.char_tvGen | (intros; apply GlobalTheory.UTrans.TvKill.char_tvGen <;> assumption)
end _root_.GlobalTheory.T
