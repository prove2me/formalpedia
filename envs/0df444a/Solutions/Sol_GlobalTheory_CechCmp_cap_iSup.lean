-- Prove2me | solution 1 for GlobalTheory.CechCmp.cap_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:50.226123+00:00
-- url     : https://prove2.me/submissions/d070f247-4481-4386-a784-8f89287c0d26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
import Theorems.Thm_GlobalTheory_CechCmp_cap_single

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
theorem _root_.solution (U : I → X.Opens) (hU : ⨆ i, U i = ⊤) : ⨆ S, cap U S = ⊤ :=
  eq_top_iff.2 (hU ▸ iSup_le fun i => (cap_single U i).symm.le.trans (le_iSup (cap U) (NE.single i)))
end GlobalTheory.CechCmp
