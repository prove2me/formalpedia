-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:38:32.973888+00:00
-- url     : https://prove2.me/submissions/60f1f6d8-cdb1-42ae-ba02-857e7e78fdff

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ClassZetaValuationBounds_ToricDenominatorLevel_exact

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
theorem _root_.solution {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) (v : HeightOneSpectrum (OF E)) : expIn 𝔣 v ≤ 2 := by
  by_cases hv : v.asIdeal ∣ 𝔣
  · exact (h.2.2 v hv).2.1
  · rw [expIn, multiplicity_eq_zero.2 hv]; omega
end GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds
