-- Prove2me | solution 1 for GlobalTheory.UT.TorusWeight.psi_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:52:05.265281+00:00
-- url     : https://prove2.me/submissions/45b07c30-3430-486c-a098-76cd92318b57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValPowGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFrameRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TxFrameOfOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_psi_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cPoint_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.TorusWeight
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.TorusWeight
theorem _root_.solution (hB : D.TauBimult) (z : (TF (R := R) F).left) {J} (hJ : Good D.P.L z J) :
    @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi 0) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J = 1 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have z0 : (0 : D.X) + 0 = 0 := add_zero 0
  have hpt : ∀ a b c : D.X, a = b → ∀ (r : (TF (R := R) F).left ⟶ _),
      val (D.tau a c) r z J = val (D.tau b c) r z J := by rintro a b c rfl r; rfl
  have hpp : ∀ a b : D.X, a = b → ∀ (r : (TF (R := R) F).left ⟶ _), val (D.psi a) r z J = val (D.psi b) r z J := by
    rintro a b rfl r; rfl
  have hτ0 := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 0
  rw [hpt _ _ _ z0, cPoint_zero, C.face] at hτ0
  have t00 := (mul_left_cancel hτ0).symm
  have hψ := UUA.psi_add (𝟙 (TF (R := R) F)) hJ (0 : D.X) 0
  rw [hpp _ _ z0, t00, _root_.one_mul, _root_.mul_assoc] at hψ
  have h1 := left_eq_mul.1 hψ
  rw [Over.id_left, Category.id_comp] at h1
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) h1
  exact (val_pull hJ (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (toUnit (TK R)).left (jFK (R := R) F)).symm
end GlobalTheory.UT.TorusWeight
