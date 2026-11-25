-- Prove2me | solution 1 for GlobalTheory.BoundedRegular.valF_mul_valF_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:05.129139+00:00
-- url     : https://prove2.me/submissions/a74dae29-6e2f-45d4-a064-84b2c57e0de6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
open GlobalTheory.BoundedRegular
namespace GlobalTheory.BoundedRegular
theorem _root_.solution {F : Type} [Field F] {X : Scheme.{0}} (t : Sp F ⟶ X) (U : X.Opens)
    (ht : Set.range t ⊆ U) {φ φ' : Γ(X, U)} (h : φ * φ' = 1) :
    valF t U φ * valF t U φ' = 1 := by
  have h' : ⊤ ≤ t ⁻¹ᵁ U := fun q _ => ht ⟨q, rfl⟩
  rw [valF, valF, dif_pos h', dif_pos h', ← map_mul, ← map_mul, h, map_one, map_one]
end GlobalTheory.BoundedRegular
