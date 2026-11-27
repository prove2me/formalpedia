-- Prove2me | solution 1 for GlobalTheory.UnimodMass.finite_dc_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:12.446415+00:00
-- url     : https://prove2.me/submissions/c2e0924a-c43d-4635-93f9-893cf490ad23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DoubleCosetSetoidRelIffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnimodMass
variable {G : Type*} [Group G]
namespace GlobalTheory.UnimodMass
theorem _root_.solution {Γ W K : Subgroup G} (hWK : W ≤ K) [Finite (DC Γ W)] : Finite (DC Γ K) := by
  let f : DC Γ W → DC Γ K := Quotient.map' (s₁ := dcSetoid Γ W) (s₂ := dcSetoid Γ K) id (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, e⟩ := hab
    exact ⟨γ, hγ, κ, hWK hκ, e⟩)
  refine Finite.of_surjective f ?_
  rintro ⟨x⟩
  exact ⟨Quotient.mk'' x, rfl⟩
end GlobalTheory.UnimodMass
