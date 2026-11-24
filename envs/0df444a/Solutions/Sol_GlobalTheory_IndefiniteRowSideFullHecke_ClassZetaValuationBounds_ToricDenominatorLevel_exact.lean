-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominatorLevel.exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:17.802384+00:00
-- url     : https://prove2.me/submissions/557ceac3-6cc3-46ad-809d-f6cb8ab860da

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory.CMVal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds
variable {E : Type} [Field E] [NumberField E]
variable {I : Type} [Fintype I]
namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds
namespace ToricDenominatorLevel
theorem _root_.solution (h : ToricDenominatorLevel) : ToricDenominator := by
  intro E _ _ _ _ I _ d φ s hd hs
  obtain ⟨z, hz, H⟩ := h E I d φ s hd hs
  refine ⟨z, hz, fun κ 𝔣 Λ χ h𝔣 hΛ hχ => H κ 𝔣 Λ χ h𝔣 hΛ ⟨hχ.1, hχ.2.1, hχ.2.2.1, fun v P hP => ?_⟩⟩
  exact (((hχ.2.2.2 v P hP).2 (by simp)) _).2 le_rfl
end ToricDenominatorLevel
end GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds
