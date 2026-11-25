-- Prove2me | solution 1 for GlobalTheory.T.torsionBasis_geometric_fibres_of_open_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:02.606024+00:00
-- url     : https://prove2.me/submissions/0715f452-321e-4a21-b317-fdc8b9c4ccd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionBasisGeometricFibresOfOpenCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionBasisGeometricFibresOfOpenCoverStatement
import Theorems.Thm_GlobalTheory_CoverGlue_torsionBasis_of_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (g k : ℕ) (P : Fin (2 * g) → (Out.baseOver S ⟶ A)) (Q : ∀ i, Fin (2 * g) → (Out.baseOver (U i).toScheme ⟶ G i)), (∀ i l, (Q i l).left ≫ ψ i = (U i).ι ≫ (P l).left) → (∀ i (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ (U i).toScheme) (y : Over.mk x ⟶ G i), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) (fun l => (c l).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ P l) (fun l => (c l).val) = y := by
  first | exact @GlobalTheory.CoverGlue.torsionBasis_of_cover | exact GlobalTheory.CoverGlue.torsionBasis_of_cover | (intros; apply GlobalTheory.CoverGlue.torsionBasis_of_cover <;> assumption)
end _root_.GlobalTheory.T
