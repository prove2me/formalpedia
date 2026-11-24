-- Prove2me | solution 1 for GlobalTheory.IsInvariantSection.basicOpen_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:45:04.349415+00:00
-- url     : https://prove2.me/submissions/d598050a-6438-494c-b130-3058335b2757

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
variable {ρ : G →* Aut X}
namespace GlobalTheory
namespace IsInvariantSection
theorem _root_.solution {U : X.Opens} {s : Γ(X, U)}
    (hs : IsInvariantSection ρ U s) (g : G) : X.basicOpen s ≤ (ρ g).hom ⁻¹ᵁ X.basicOpen s := by
  obtain ⟨h, hgs⟩ := hs g
  have := Scheme.basicOpen_appLE (ρ g).hom U U h s
  rw [hgs] at this
  exact this.le.trans inf_le_right
end IsInvariantSection
end GlobalTheory
