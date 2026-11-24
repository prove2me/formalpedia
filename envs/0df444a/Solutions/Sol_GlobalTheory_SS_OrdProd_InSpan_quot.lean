-- Prove2me | solution 1 for GlobalTheory.SS.OrdProd.InSpan.quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:34:16.830084+00:00
-- url     : https://prove2.me/submissions/b4fd3ead-c732-491c-87ae-c6eaf05172f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeron
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsEqDivOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsVf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VectorFieldOrderAddOfProdStrictHenselian

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
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdProd
variable {B E L J : Type} [CommRing B] [CommRing E] [Fintype L] (φ : B →+* E) (d : J → E →+ E)
  (T : L → B)
variable {φ d T}
namespace GlobalTheory.SS.OrdProd
namespace InSpan
theorem _root_.solution (h : ∀ i a b, d i (a * b) = a * d i b + b * d i a) {τ a b : B}
    (ha : InSpan φ d T a) (hb : InSpan φ d T b) (hu : IsUnit a) (e : τ * a = b) : InSpan φ d T τ := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨r', hr'⟩ := hb
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨fun l => c * (r' l - τ * r l), fun i => ?_⟩
  have h1 := h i (φ τ) (φ a)
  rw [← map_mul, e, hr, hr'] at h1
  have h2 : φ c * φ a = 1 := by rw [← map_mul, hc, map_one]
  simp only [map_mul, map_sub, _root_.mul_assoc, sub_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, h1]
  linear_combination (-(d i (φ τ))) * h2
end InSpan
end GlobalTheory.SS.OrdProd
