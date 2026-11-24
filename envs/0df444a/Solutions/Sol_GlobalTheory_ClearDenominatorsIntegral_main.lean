-- Prove2me | solution 1 for GlobalTheory.ClearDenominatorsIntegral.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:33.798198+00:00
-- url     : https://prove2.me/submissions/4dad21c2-2d97-493a-a1ac-1a73d1d3fc9d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ClearDenominators
import Theorems.Thm_GlobalTheory_ClearDenominatorsIntegral_clear_denominators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClearDenominatorsIntegral
open GlobalTheory.UnitLemma
namespace GlobalTheory.ClearDenominatorsIntegral
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ) {V : Type} [inst : AddCommGroup V] [inst_1 : Module (GlobalTheory.UnitLemma.UQ.E K) V] [inst_2 : Module (GlobalTheory.UnitLemma.UQ.O K) V] [IsScalarTower (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) V] (M : Submodule (GlobalTheory.UnitLemma.UQ.O K) V) {x : V}, x ∈ Submodule.span (GlobalTheory.UnitLemma.UQ.E K) (↑M : Set V) → ∃ (d : GlobalTheory.UnitLemma.UQ.O K), d ≠ (0 : GlobalTheory.UnitLemma.UQ.O K) ∧ d • x ∈ M :=
  fun K _ _ _ _ _ M _ hx => clear_denominators K M hx
end GlobalTheory.ClearDenominatorsIntegral
