-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.stable_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:23:53.035803+00:00
-- url     : https://prove2.me/submissions/d323a003-c0ad-4171-a589-9fb7fc8b44e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_adjoin_stable
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_adjoin_stable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (g Y : A)
    (h : Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A)) (L : Submodule O A) :
    (∀ y ∈ L, g * y ∈ L) ↔ (∀ y ∈ L, Y * y ∈ L) :=
  ⟨fun hL => adjoin_stable g L hL Y h.1, fun hL => adjoin_stable Y L hL g h.2⟩
end GlobalTheory.UnitLemma.CayleyCase
