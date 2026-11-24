-- Prove2me | solution 1 for GlobalTheory.exists_algHom_powerSeries_apply_X_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:38:06.767799+00:00
-- url     : https://prove2.me/submissions/f93ebcc6-dcef-4645-86ae-0d22e30524d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_StalkGenericPointSpecializesOfSpecializes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory IsLocalRing
universe u
open GlobalTheory
open PowerSeries
namespace GlobalTheory
theorem _root_.solution {O : Type*} [CommRing O] (I : Ideal O)
    [h : IsAdicComplete I O] {π : O} (hπ : π ∈ I) : ∃ ev : O⟦X⟧ →ₐ[O] O, ev X = π := by
  let : WithIdeal O := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval π := WithIdeal.isTopologicallyNilpotent_of_mem hπ
  refine ⟨PowerSeries.aeval ha, ?_⟩
  rw [← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]
end GlobalTheory
