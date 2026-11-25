-- Prove2me | solution 1 for GlobalTheory.KeyInputCompare.keyInEquiv_symm_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:59:46.657311+00:00
-- url     : https://prove2.me/submissions/8bb6fcb4-b3fe-4ab6-b403-b53fdbff8a19

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
theorem _root_.solution (y : KeyInput R) : ((keyInEquiv R).symm y).P = y.P := rfl
end GlobalTheory.KeyInputCompare
