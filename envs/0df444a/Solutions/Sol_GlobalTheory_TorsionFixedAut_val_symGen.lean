-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.val_symGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:32:52.366912+00:00
-- url     : https://prove2.me/submissions/61e04c86-4284-42a9-81f6-a9725769bdaa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution {k : ℤ} (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) : val (symGen A L k θ nu) r z J =
      thetaVal θ.φ
        (r ≫ (translT A θ.pt⁻¹).left) z J *
      negVal nu r z J *
      (thetaVal θ.φ
        (r ≫ (negT A T).left) z J *
      (negVal nu
        (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg (· * _) (val_pull hJ _ _ _)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))))
end GlobalTheory.TorsionFixedAut
