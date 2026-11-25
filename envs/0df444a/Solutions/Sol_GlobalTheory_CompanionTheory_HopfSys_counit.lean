-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.counit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:50:23.172376+00:00
-- url     : https://prove2.me/submissions/5746b7fe-c433-4799-b1ea-6660d1e9bfaf

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_kMap_mMap
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_evL_eq
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_comp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_eq_of_natTrans
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_id
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_Cris_IsMor_pullCohomologyTwo_id


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
theorem _root_.solution (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (y : H2 (OSys A.hom S)) (w : H2 (box (OSys A.hom S)))
    (e : (pj A S).coef.pull2 w = (mMap A S).pull2 y) :
    (boxE (OSys A.hom S) (op a₀) (epsA ha)).pull2 w = y := by
  have e' := congrArg (kMap ha).pull2 e
  rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp] at e'
  have l1 : ((pj A S).coef.comp (kMap ha)).pull2 w = (boxE (OSys A.hom S) (op a₀) (epsA ha)).pull2 w := by
    let θ : ((pj A S).coef.comp (kMap ha)).G ⟶ (boxE (OSys A.hom S) (op a₀) (epsA ha)).G :=
      { app := fun b ↦ 𝟙 ((CategoryTheory.Prod.sectR (op a₀) Pᵒᵖ).obj b)
        naturality := fun _ _ f ↦ Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _) }
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((pj A S).coef.comp (kMap ha)) (boxE (OSys A.hom S) (op a₀) (epsA ha)) θ (fun b z ↦ ?_) w
    erw [mp_id]
    exact evL_eq ha b z
  have l2 : ((mMap A S).comp (kMap ha)).pull2 y = (CoefMap.id (OSys A.hom S)).pull2 y := by
    let θ : ((mMap A S).comp (kMap ha)).G ⟶ (CoefMap.id (OSys A.hom S)).G :=
      { app := fun b ↦ 𝟙 b
        naturality := fun _ _ f ↦ Subsingleton.elim _ _ }
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((mMap A S).comp (kMap ha)) (CoefMap.id (OSys A.hom S)) θ (fun b z ↦ ?_) y
    erw [mp_id]
    exact (kMap_mMap ha b z).symm
  rw [← l1, e', l2, CoefMap.pullCohomologyTwo_id]
end GlobalTheory.CompanionTheory.HopfSys
