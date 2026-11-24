-- Prove2me | solution 1 for GlobalTheory.LatPair.Red.card_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:37:34.962612+00:00
-- url     : https://prove2.me/submissions/196208f6-fef5-47e7-b8d3-078dc72823aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
open GlobalTheory.LatPair.Red
variable (L : Submodule 𝒪[k] (n → k))
variable {L}
namespace GlobalTheory.LatPair.Red
theorem _root_.solution [Fintype n] [L.IsLattice k] : Nat.card (Red L) = SplitWeil.resCard k ^ Fintype.card n := by
  rw [Module.natCard_eq_pow_finrank (K := 𝓀[k]), finrank_eq]
  rfl
end GlobalTheory.LatPair.Red
