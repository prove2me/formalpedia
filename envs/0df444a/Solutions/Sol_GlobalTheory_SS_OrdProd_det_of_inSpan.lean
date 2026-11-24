-- Prove2me | solution 1 for GlobalTheory.SS.OrdProd.det_of_inSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:33:57.293002+00:00
-- url     : https://prove2.me/submissions/300ffbc7-b4fc-4e2e-91cd-3c571df6caa9

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
theorem _root_.solution [DecidableEq L] {d : L → E →+ E} {τ : L → B} (h : ∀ j, InSpan φ d T (τ j)) :
    ∃ ρ : B, (Matrix.of fun i j => d i (φ (τ j))).det = φ ρ * (Matrix.of fun i j => d i (φ (T j))).det := by
  choose r hr using h
  refine ⟨(Matrix.of fun l j => r j l).det, ?_⟩
  rw [RingHom.map_det, mul_comm, ← Matrix.det_mul]
  congr 1
  ext i j
  simp [hr, Matrix.mul_apply, mul_comm]
end GlobalTheory.SS.OrdProd
