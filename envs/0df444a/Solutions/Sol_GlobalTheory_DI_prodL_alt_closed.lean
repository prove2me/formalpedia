-- Prove2me | solution 1 for GlobalTheory.DI.prodL_alt_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:47:02.523663+00:00
-- url     : https://prove2.me/submissions/41a6bb69-19aa-4c38-88f1-5747c950a4f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
import Theorems.Thm_GlobalTheory_DI_AltClosed_prodL_closed
import Theorems.Thm_GlobalTheory_DI_AltClosed_alt_closed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsOddDer d → IsDatum p d f h → (∀ vs : List V, Dtot d (prodL f h vs) = 0 ∧ prodL f h vs ∅ = 0) ∧ ∀ (a : ℕ) (v : Fin a → V), Dtot d (alt f h a v) = 0 ∧ alt f h a v ∅ = 0 := by
  intro K _ V _ _ ι _ p d f h hd hD
  exact ⟨fun vs => AltClosed.prodL_closed p d f h hd hD vs,
    fun a v => AltClosed.alt_closed p d f h hd hD a v⟩
end GlobalTheory.DI
