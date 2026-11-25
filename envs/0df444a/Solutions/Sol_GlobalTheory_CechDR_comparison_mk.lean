-- Prove2me | solution 1 for GlobalTheory.CechDR.comparison_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:48:39.248534+00:00
-- url     : https://prove2.me/submissions/ff3a4ccf-b6ac-427e-847f-9ce70cf4f950

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration

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
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open CatCoh Cris
universe v u v' u'
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
namespace GlobalTheory.CechDR
theorem _root_.solution (s : X ⟶ Sp R) (f : Z1 (O (dp0 R) s)) :
    cmp1 s (H1.mk _ f) = Hyp1.mk _ (cmpZZ s f) := rfl
end GlobalTheory.CechDR
