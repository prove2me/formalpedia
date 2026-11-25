-- Prove2me | solution 1 for GlobalTheory.KeyPow.det_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:49:28.877917+00:00
-- url     : https://prove2.me/submissions/898c798d-9795-47bb-8ff4-87a6fb8f28d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaCharBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatuStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LatticeBlocks
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow
namespace GlobalTheory.KeyPow
theorem _root_.solution {j g G : ℕ} {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G)
    (M : Matrix (Fin g) (Fin g) R) :
    (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R).det = M.det ^ j := by
  have h : (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R) =
      Matrix.reindex ((Equiv.prodComm _ _).trans e) ((Equiv.prodComm _ _).trans e)
        (Matrix.blockDiagonal fun _ : Fin j => M) := by
    ext p q
    simp [Matrix.blockDiagonal_apply]
  rw [h, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  simp
end GlobalTheory.KeyPow
