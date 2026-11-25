-- Prove2me | solution 1 for GlobalTheory.UU.CubTriv.twist_even_twistSym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:38.720799+00:00
-- url     : https://prove2.me/submissions/1e6d6af6-0565-4dfd-b365-c044d041f9c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}}
attribute [instance] TQ.grp TQ.comm
variable {X : Type} [AddCommGroup X]
variable {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G}
namespace GlobalTheory.UU
namespace CubTriv
theorem _root_.solution {P : CP (splitTorus S X)} {σ : CubTriv P.c (𝟙 _)} (hσ : σ.Even) (ψ : X) :
    CubTriv.Even (P := P.twistSym (-(ψ + ψ))) (σ.twist ψ) := by
  intro T x
  show ∀ (z : T.left) (J : (T.left ⟶ (splitTorus S X).left) → P.L.L.ι), Good P.L.L z J →
    val (scaleGen (charUnit S X ψ) σ.s) (x⁻¹).left z J =
      val (scaleGen (charUnit S X (-(ψ + ψ))) P.sym) (x ≫ 𝟙 _).left z J *
        val (scaleGen (charUnit S X ψ) σ.s) x.left z J
  intro z J hJ
  have hn : chV (x ≫ 𝟙 _) (-(ψ + ψ)) = (chV x ψ * chV x ψ)⁻¹ := by
    rw [Category.comp_id]
    exact eq_inv_of_mul_eq_one_left (by rw [← chV_add, ← chV_add, neg_add_cancel, chV_zero])
  rw [val_scaleGen _ _ _ hJ, val_scaleGen _ _ _ hJ, val_scaleGen _ _ _ hJ, gm_charUnit, gm_charUnit, gm_charUnit,
    hσ T x z J hJ, chV_inv, hn]
  simp only [map_inv, map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end CubTriv
end GlobalTheory.UU
