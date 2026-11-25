-- Prove2me | solution 1 for GlobalTheory.BiextSym.law_origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:36:24.730344+00:00
-- url     : https://prove2.me/submissions/279f815e-d60f-4446-902e-6603e5fe132f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawProduct
import Theorems.Thm_P2M_GlobalTheory_BiextSym_val_pull__289846acbbfe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BiextSym
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
namespace GlobalTheory.BiextSym
theorem _root_.solution {P : LB (A ⊗ A).left} (β : IsBiext A P) {T : Over S} {z : T.left} {J} (hJ : Good P z J) :
    val β.law1 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J =
      val β.law2 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J := by
  let ρ := lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A)))
  have a₀ : ρ ≫ x4 A 0 = 1 := by simp [ρ, x4]
  have a₁ : ρ ≫ x4 A 1 = 1 := by simp [ρ, x4]
  have a₂ : ρ ≫ x4 A 2 = 1 := by simp [ρ, x4]
  have a₃ : ρ ≫ x4 A 3 = 1 := by simp [ρ, x4]
  have b₀ : ρ ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁, _root_.mul_one])
  have b₁ : ρ ≫ padd A (x4 A 2) (x4 A 3) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₂, a₃, _root_.mul_one])
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    (val_pull₃ β.law1 ρ hJ _ _ _) (val_pull₃ β.law2 ρ hJ _ _ _))) (val_pull₃ β.law2 ρ hJ _ _ _))).symm.trans
    ((val_corr hJ β.compat ρ.left).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull₃ β.law2 ρ hJ _ _ _) (val_pull₃ β.law1 ρ hJ _ _ _))) (val_pull₃ β.law1 ρ hJ _ _ _))))
  rw [b₀, b₁, a₀, a₁, a₂, a₃, mul_comm (val β.law2 _ z J) (val β.law1 _ z J)] at e
  exact (mul_left_cancel e).symm
end GlobalTheory.BiextSym
