-- Prove2me | solution 1 for GlobalTheory.CechDR.IsPull1.cup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:03:10.991433+00:00
-- url     : https://prove2.me/submissions/c28e0af9-1d30-4d2b-966f-f13f855d7001

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Theorems.Thm_GlobalTheory_CechDR_pullHyp2_cup


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
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
variable (h : φ ≫ s = s' ≫ spMap σ)
variable {h}
namespace GlobalTheory.CechDR
namespace IsPull1
theorem _root_.solution {a b : HH1 s} {a' b' : HH1 s'} (ha : IsPull1 h a a') (hb : IsPull1 h b b') :
    IsPull2 h (cupHH s a b) (cupHH s' a' b') := by
  unfold IsPull1 IsPull2 at *; rw [pullHyp2_cup, pullHyp2_cup, ha, hb]
end IsPull1
end GlobalTheory.CechDR
