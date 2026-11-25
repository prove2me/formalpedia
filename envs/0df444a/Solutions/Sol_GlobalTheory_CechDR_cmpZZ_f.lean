-- Prove2me | solution 1 for GlobalTheory.CechDR.cmpZZ_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:46:50.809035+00:00
-- url     : https://prove2.me/submissions/3d63e999-b5b9-4c58-b355-6038df6ba7ab

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
theorem _root_.solution (s : X ⟶ Sp R) (f : Z1 (O (dp0 R) s)) {U V : AffOp X} (a : U ⟶ V) :
    (cmpZZ s f).1.1 U V a = ev f (Thick.trivHom (hx := affPt_w s U.unop)
      (T := Thick.triv _ _ (affPt_w s V.unop)) (Sec.res s (leOfHom a.unop))
      (affPt_res s (leOfHom a.unop))) := rfl
end GlobalTheory.CechDR
