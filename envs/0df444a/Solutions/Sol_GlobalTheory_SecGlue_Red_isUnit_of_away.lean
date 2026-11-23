-- Prove2me | solution 1 for GlobalTheory.SecGlue.Red.isUnit_of_away
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:14.850797+00:00
-- url     : https://prove2.me/submissions/b07ff64c-70e8-4538-abf8-002fcc125fea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed

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
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red
namespace GlobalTheory.SecGlue.Red
theorem _root_.solution {R T : Type} [CommRing R] [CommRing T] [Algebra R T] (a : R)
    (ρ : Localization.Away a →+* T) (hρ : ρ.comp (algebraMap R _) = algebraMap R T) :
    IsUnit (algebraMap R T a) := by
  rw [← hρ]; exact (IsLocalization.Away.algebraMap_isUnit a).map ρ
end GlobalTheory.SecGlue.Red
