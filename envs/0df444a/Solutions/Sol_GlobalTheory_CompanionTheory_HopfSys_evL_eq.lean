-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.evL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:21:54.531038+00:00
-- url     : https://prove2.me/submissions/1f5b510d-7b43-4807-a8e1-c2f8daab5cda

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_kMap_qA
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_kMap_pA
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {P : Type} [SemilatticeInf P] {S : Sys A.left P}
  [IsSeparated A.hom] {a₀ : P}
attribute [local instance] unit_isAffine
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ)
    (z : (OSys A.hom S).obj (op a₀) ⊗[R] (OSys A.hom S).obj b) :
    evL (OSys A.hom S) (op a₀) b (epsA ha) z = (kMap ha).α b (pjAlg A S ((tK a₀).obj b) z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm
  | add x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans ((congrArg _ (map_add _ _ _)).trans (map_add _ _ _)).symm)
  | tmul x y =>
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg _ (pjAlg_tmul A S ((tK a₀).obj b) x y).symm)
    refine Eq.trans ?_ (map_mul _ _ _).symm
    rw [kMap_pA, kMap_qA]
    rfl
end GlobalTheory.CompanionTheory.HopfSys
