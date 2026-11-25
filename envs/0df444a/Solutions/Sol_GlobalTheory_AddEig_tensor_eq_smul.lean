-- Prove2me | solution 1 for GlobalTheory.AddEig.tensor_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:49:14.847094+00:00
-- url     : https://prove2.me/submissions/0998fd79-180d-46e3-bb41-4ca99f355ef3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSumTmulLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionTensorEigenDiagonalThetaOrderTwo
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
import Theorems.Thm_GlobalTheory_ThetaLin_gs_scal_comp
import Theorems.Thm_GlobalTheory_UU_SecMod_sval_smul
import Theorems.Thm_GlobalTheory_tensor_sections_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sval_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.AddEig
namespace GlobalTheory.AddEig
theorem _root_.solution {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) [QuasiCompact q] [IsSeparated q] {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {n : ℕ} (u u' t t' : Fin n → SecMod q (LB.LinComb L φ ε)) (r : F)
    (H : ∀ (Z : Scheme.{0}) (r₁ r₂ : Z ⟶ Y), r₁ ≫ q = r₂ ≫ q → ∀ (z : Z) (J), Good L z J →
      ∑ i, sval (u i).sec r₁ z J * sval (u' i).sec r₂ z J =
        gs (𝟙 _) z ⊤ (scal (r₁ ≫ q) r) * ∑ i, sval (t i).sec r₁ z J * sval (t' i).sec r₂ z J) :
    ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  have key := (GlobalTheory.tensor_sections_eq_zero_iff F _ L hL _ _ q q K K φ ε φ ε (n + n) (Fin.append u (fun i => (-r) • t i))
    (Fin.append u' t')).2 (by
      intro Z r₁ r₂ h z J hJ
      have ng : gs r₁ z ⊤ (scal q (-r)) = - gs (𝟙 _) z ⊤ (scal (r₁ ≫ q) r) := by
        rw [ThetaLin.gs_scal_comp, gs_eq _ z ⊤ trivial, gs_eq _ z ⊤ trivial, scal, scal, map_neg, map_neg, map_neg,
          map_neg]
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, SecMod.sval_smul hJ, ng, _root_.mul_assoc, neg_mul]
      rw [H Z r₁ r₂ h z J hJ, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel])
  rw [Fin.sum_univ_add] at key
  simp only [Fin.append_left, Fin.append_right, ← TensorProduct.smul_tmul', neg_smul, TensorProduct.neg_tmul,
    Finset.sum_neg_distrib] at key
  rw [Finset.smul_sum]
  exact add_neg_eq_zero.1 key
end GlobalTheory.AddEig
