-- Prove2me | solution 1 for GlobalTheory.KeyInputCompare.keyInEquiv_symm_rig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:04:25.706468+00:00
-- url     : https://prove2.me/submissions/4306136a-365e-43e5-bcaa-e135f2aa9e7e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PolarizationCorrespondence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsBaseChangeIffKeyPB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence
open GlobalTheory GlobalTheory.KeyInputCompare
variable {R R' : Type} [CommRing R] [CommRing R']
namespace GlobalTheory.KeyInputCompare
theorem _root_.solution (y : KeyInput R) : ((keyInEquiv R).symm y).rig = y.rig := rfl
end GlobalTheory.KeyInputCompare
