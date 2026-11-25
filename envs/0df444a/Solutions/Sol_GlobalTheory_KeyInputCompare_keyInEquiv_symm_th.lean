-- Prove2me | solution 1 for GlobalTheory.KeyInputCompare.keyInEquiv_symm_th
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:56:19.876109+00:00
-- url     : https://prove2.me/submissions/65a9e1ff-2cd1-46c2-8438-92b85b5f1447

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
theorem _root_.solution (y : KeyInput R) : ((keyInEquiv R).symm y).th = y.th := rfl
end GlobalTheory.KeyInputCompare
