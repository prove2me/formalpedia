-- Prove2me | solution 1 for GlobalTheory.ExtDiv.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:16.879786+00:00
-- url     : https://prove2.me/submissions/a85c9d6f-53a7-49a3-84f3-7e3a9fd1beaa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DvdOfAppEqZeroOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_PGAppEqZeroIff
import Theorems.Thm_GlobalTheory_ExtDiv_pG_app_eq_zero_iff
import Theorems.Thm_GlobalTheory_ThickDiv_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExtDiv
namespace GlobalTheory.ExtDiv
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (e k : ℕ) (α : D.toPre.X) (f : D.toPre.SecB k α), (∀ j, ((U.gt e).pG.left.app _).hom (f.f j) = 0) ↔ ∃ g : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom (ϖ ^ (e + 1)) f g := by
  intro V _ _ _ ϖ hϖ D A G _ _ U e k α f

  have hflat : Flat D.toPre.P.A.hom := by
    have := D.toPre.P.smoothDim.smooth
    infer_instance

  have hiff : (∀ j, ((U.gt e).pG.left.app _).hom (f.f j) = 0) ↔
      ∀ j, ((fstG (maximalIdeal V) e D.toPre.P.A).left.app _).hom (f.f j) = 0 :=
    forall_congr' fun j => pG_app_eq_zero_iff (U.gt e) _ (f.f j)
  rw [hiff]
  exact GlobalTheory.ThickDiv.main V ϖ hϖ D.toPre.P.A _ f e
end GlobalTheory.ExtDiv
