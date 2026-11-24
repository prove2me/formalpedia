-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KaehlerSpread.bijective_linearCombination_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:48:17.672065+00:00
-- url     : https://prove2.me/submissions/4634adea-5ec6-4cf5-8574-bd5a45019187

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisSpreadsToNeighbourhood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KaehlerSpread
open KaehlerDifferential
namespace GlobalTheory.CompanionTheory.KaehlerSpread
theorem _root_.solution {B M ι : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (v : ι → M) :
    Function.Bijective (Finsupp.linearCombination B v) ↔
      LinearIndependent B v ∧ Submodule.span B (Set.range v) = ⊤ := by
  rw [Function.Bijective, ← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  rfl
end GlobalTheory.CompanionTheory.KaehlerSpread
