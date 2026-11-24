-- Prove2me | solution 1 for GlobalTheory.CechDR.IsPull1.toO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:59:52.521799+00:00
-- url     : https://prove2.me/submissions/3b21a1ee-9df0-4a01-b80f-87888866d78d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Theorems.Thm_GlobalTheory_CechDR_toO_pullHyp1


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
theorem _root_.solution {a : HH1 s} {a' : HH1 s'} (ha : IsPull1 h a a') :
    IsPullO h (toHO1 s a) (toHO1 s' a') := by
  unfold IsPull1 IsPullO at *; rw [← toO_pullHyp1, ← toO_pullHyp1, ha]
end IsPull1
end GlobalTheory.CechDR
