-- Prove2me | solution 1 for GlobalTheory.CechCmp.NE.set_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:29:16.326044+00:00
-- url     : https://prove2.me/submissions/b45fe9bd-f83b-40a6-ab17-0083d648ad33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechCmp
variable {I : Type} {X : Scheme.{0}}
namespace GlobalTheory.CechCmp
namespace NE
theorem _root_.solution (S T : NE I) : (S ⊓ T).set = S.set ∪ T.set := rfl
end NE
end GlobalTheory.CechCmp
