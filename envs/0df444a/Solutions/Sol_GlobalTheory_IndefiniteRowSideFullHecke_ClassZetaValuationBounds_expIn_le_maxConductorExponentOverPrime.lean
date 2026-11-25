-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_maxConductorExponentOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:49:59.749726+00:00
-- url     : https://prove2.me/submissions/7680f830-45d8-4b55-a6a2-4b7f2cb32d81

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ClassZetaValuationBounds_ToricDenominatorLevel_exact
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ClassZetaValuationBounds_expIn_le_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory.CMVal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds
variable {E : Type} [Field E] [NumberField E]
variable {I : Type} [Fintype I]
namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds
theorem _root_.solution {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) {l : ℕ} {v : HeightOneSpectrum (OF E)}
    (hv : (l : OF E) ∈ v.asIdeal) : expIn 𝔣 v ≤ a0 𝔣 l :=
  le_csSup ⟨2, by rintro _ ⟨w, -, rfl⟩; exact expIn_le_two h w⟩ ⟨v, hv, rfl⟩
end GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds
