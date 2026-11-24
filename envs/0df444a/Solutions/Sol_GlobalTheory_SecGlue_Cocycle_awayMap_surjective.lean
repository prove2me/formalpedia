-- Prove2me | solution 1 for GlobalTheory.SecGlue.Cocycle.awayMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:18.349891+00:00
-- url     : https://prove2.me/submissions/88821c15-cbe1-4d53-8aac-8073c4f2ee67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsAgreeOfCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Cocycle
namespace GlobalTheory.SecGlue.Cocycle
theorem _root_.solution {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (r : R) : Function.Surjective (Localization.awayMap π r) := by
  intro y
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (π r)) y
  obtain ⟨b, rfl⟩ := hπ a
  refine ⟨IsLocalization.mk' _ b (⟨r ^ m, m, rfl⟩ : Submonoid.powers r), ?_⟩
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk']
  congr 1
  ext
  simp
end GlobalTheory.SecGlue.Cocycle
