-- Prove2me | solution 1 for GlobalTheory.SS.OrdProd.inSpan_of_cramer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:34:11.696028+00:00
-- url     : https://prove2.me/submissions/f67a59c9-7947-4c76-8571-a7c14cf18698

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
theorem _root_.solution [DecidableEq L] {d : L → E →+ E} {c : E} (hc : IsUnit c)
    (h : ∀ t : L → B, ∃ s, (Matrix.of fun i j => d i (φ (t j))).det = c * φ s) {s : B} (hs : IsUnit s)
    (hT : (Matrix.of fun i j => d i (φ (T j))).det = c * φ s) (u : B) : InSpan φ d T u := by
  choose σ hσ using h
  obtain ⟨s', hs'⟩ := hs.exists_left_inv
  refine ⟨fun l => s' * σ (Function.update T l u), fun i => ?_⟩
  have h1 := congrFun (Matrix.mulVec_cramer (Matrix.of fun i j => d i (φ (T j))) (fun i => d i (φ u))) i
  have h2 : ∀ l, Matrix.cramer (Matrix.of fun i j => d i (φ (T j))) (fun i => d i (φ u)) l =
      c * φ (σ (Function.update T l u)) := by
    intro l
    rw [Matrix.cramer_apply, ← hσ]
    congr 1
    ext a b
    by_cases hb : b = l
    · subst hb; simp
    · simp [hb]
  simp only [Matrix.mulVec, dotProduct, h2, hT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at h1
  have h3 : φ s' * φ s = 1 := by rw [← map_mul, hs', map_one]
  apply hc.mul_left_cancel
  have h4 : c * ∑ l, φ (s' * σ (Function.update T l u)) * d i (φ (T l)) =
      φ s' * ∑ l, d i (φ (T l)) * (c * φ (σ (Function.update T l u))) := by
    simp only [Finset.mul_sum, map_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h4, h1]
  linear_combination (-(c * d i (φ u))) * h3
end GlobalTheory.SS.OrdProd
