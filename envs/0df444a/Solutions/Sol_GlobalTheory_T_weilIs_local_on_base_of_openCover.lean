-- Prove2me | solution 1 for GlobalTheory.T.weilIs_local_on_base_of_openCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:42.085121+00:00
-- url     : https://prove2.me/submissions/1c44d115-d447-4220-825b-2f2953a7c9dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsLocalOnBaseOfOpenCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsLocalOnBaseOfOpenCoverStatement
import Theorems.Thm_GlobalTheory_weilIs_of_openCover


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
theorem _root_.solution : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (k : ℤ) (x y : Out.baseOver S ⟶ A) (x' y' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i) (c : Γ(S, ⊤)ˣ), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, (y' i).left ≫ ψ i = (U i).ι ≫ y.left) → (∀ i, Out.WeilIs (G i) (M i) k (x' i) (y' i) (Units.map (U i).ι.appTop.hom.toMonoidHom c)) → Out.WeilIs A L k x y c := by
  first | exact @GlobalTheory.weilIs_of_openCover | exact GlobalTheory.weilIs_of_openCover | (intros; apply GlobalTheory.weilIs_of_openCover <;> assumption)
end _root_.GlobalTheory.T
