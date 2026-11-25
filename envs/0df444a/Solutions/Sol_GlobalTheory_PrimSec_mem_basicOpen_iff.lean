-- Prove2me | solution 1 for GlobalTheory.PrimSec.mem_basicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:15.7658+00:00
-- url     : https://prove2.me/submissions/1e90ed9a-9597-4cbc-bcbb-a62e4dbad293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.PrimSec
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
namespace GlobalTheory.PrimSec
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) (x : U) (s : Γ(X, U)) :
    x.1 ∈ X.basicOpen s ↔ s ∉ (hU.primeIdealOf x).asIdeal := by
  have h : (hU.primeIdealOf x : Spec Γ(X, U)) ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen s ↔
      x.1 ∈ X.basicOpen s := by
    conv_rhs => rw [← hU.fromSpec_primeIdealOf x]
    rfl
  rw [← h, hU.fromSpec_preimage_basicOpen]
  rfl
end GlobalTheory.PrimSec
