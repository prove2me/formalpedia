-- Prove2me | solution 1 for GlobalTheory.GlobalLift.val_symGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:20.987908+00:00
-- url     : https://prove2.me/submissions/b3c53324-3804-49d1-85f1-33e25afddfc3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
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
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GlobalLift
open CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.GlobalLift
theorem _root_.solution {T : Over S} (θ : ThetaGrp A L k T) (ν : LB.Gen (negLB A L k T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (symGen A L k θ ν) r z J = (tval θ (r ≫ (translT A θ.pt⁻¹).left) z J * nval ν r z J) *
      (tval θ (r ≫ (negT A T).left) z J * (nval ν (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg (· * nval ν r z J) (val_pull hJ _ _ _)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))))
end GlobalTheory.GlobalLift
