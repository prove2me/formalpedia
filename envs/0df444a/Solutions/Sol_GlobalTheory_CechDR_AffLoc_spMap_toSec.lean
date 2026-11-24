-- Prove2me | solution 1 for GlobalTheory.CechDR.AffLoc.spMap_toSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:17:39.759124+00:00
-- url     : https://prove2.me/submissions/3a66c741-e24a-4c0d-ae73-3044cf738402

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecFunctionsEqOfRestrictionsOnPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGlued

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
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
namespace GlobalTheory.CechDR.AffLoc
theorem _root_.solution (B : Type) [CommRing B] [Algebra R B] (V : (Sp B).affineOpens) :
    spMap (toSec R B V : B →+* Sec (algStr R B) V.1) = affPt (algStr R B) V :=
  (affPt_eq R B V).symm
end GlobalTheory.CechDR.AffLoc
