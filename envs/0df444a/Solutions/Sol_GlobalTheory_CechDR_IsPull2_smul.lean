-- Prove2me | solution 1 for GlobalTheory.CechDR.IsPull2.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:58:07.785236+00:00
-- url     : https://prove2.me/submissions/10a42d30-c210-4d14-92b1-2488f036d9a4

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
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
variable (h : φ ≫ s = s' ≫ spMap σ)
variable {h}
namespace GlobalTheory.CechDR
namespace IsPull2
theorem _root_.solution {a : HH2 s} {a' : HH2 s'} (ha : IsPull2 h a a') (r : R) :
    IsPull2 h (r • a) (σ r • a') := by
  unfold IsPull2 at *; rw [map_smulₛₗ, map_smulₛₗ, ha]; rfl
end IsPull2
end GlobalTheory.CechDR
