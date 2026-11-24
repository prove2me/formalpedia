-- Prove2me | solution 1 for GlobalTheory.SecGlue.ChartIndep.lands_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:11.478706+00:00
-- url     : https://prove2.me/submissions/a299d562-70f3-4b5d-ace1-4b5dcb1cb286

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SecGlue
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.ChartIndep
namespace GlobalTheory.SecGlue.ChartIndep
theorem _root_.solution {Y : Scheme.{0}} (W : Y.Opens) {S : Type} [CommRing S] (s : S) (f : Sp S ⟶ Y)
    (hs : ∀ p : Sp S, s ∉ p.asIdeal → p ∈ f ⁻¹ᵁ W) :
    (spMap (algebraMap S (Localization.Away s)) ≫ f) ⁻¹ᵁ W = ⊤ := by
  rw [Scheme.Hom.comp_preimage]
  refine top_le_iff.mp fun x _ => ?_
  rw [Scheme.Hom.mem_preimage]
  apply hs
  intro hx
  change s ∈ Ideal.comap (algebraMap S (Localization.Away s)) x.asIdeal at hx
  rw [Ideal.mem_comap] at hx
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.Away.algebraMap_isUnit s))
end GlobalTheory.SecGlue.ChartIndep
