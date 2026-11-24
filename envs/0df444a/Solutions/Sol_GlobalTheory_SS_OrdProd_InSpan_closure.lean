-- Prove2me | solution 1 for GlobalTheory.SS.OrdProd.InSpan.closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:51:59.533006+00:00
-- url     : https://prove2.me/submissions/5742f519-fda6-4b89-88b8-510bb121366e

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
import Theorems.Thm_GlobalTheory_SS_OrdProd_der_one

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
theorem _root_.solution (h : ∀ i a b, d i (a * b) = a * d i b + b * d i a) {s : Set B}
    (hs : ∀ x ∈ s, InSpan φ d T x) {x : B} (hx : x ∈ Subring.closure s) : InSpan φ d T x := by
  induction hx using Subring.closure_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, fun i => by simp⟩
  | one => exact ⟨0, fun i => by simp [der_one (h i)]⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨r', hr'⟩ := hy
    exact ⟨r + r', fun i => by simp [hr, hr', add_mul, Finset.sum_add_distrib]⟩
  | neg x _ hx =>
    obtain ⟨r, hr⟩ := hx
    exact ⟨-r, fun i => by simp [hr]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨r', hr'⟩ := hy
    refine ⟨fun l => x * r' l + y * r l, fun i => ?_⟩
    simp [h, hr, hr', add_mul, Finset.sum_add_distrib, Finset.mul_sum, _root_.mul_assoc]
end InSpan
end GlobalTheory.SS.OrdProd
