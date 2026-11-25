-- Prove2me | solution 1 for GlobalTheory.addition_tensor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:56:12.795073+00:00
-- url     : https://prove2.me/submissions/2a74689b-feb2-465f-9a19-3f81705db58d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalNeZeroOfIsIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionFormulaTensorNeZero
import Theorems.Thm_GlobalTheory_AdditionTensor_sum_sval_mul_eq_zero
import Theorems.Thm_GlobalTheory_isIntegral_tensor_left_of_smooth_grpObj
import Theorems.Thm_GlobalTheory_sval_ne_zero_of_isIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → th ≠ 0 → ∑ i, TensorProduct.tmul F (t i) (t' i) ≠ 0 := by
  intro S P F _ p th n t t' hadd hth h0
  obtain ⟨κ, -, hκ⟩ := hadd
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : IsIntegral (Over.mk p).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have hI : IsIntegral (Over.mk p ⊗ P.A).left := isIntegral_tensor_left_of_smooth_grpObj S P.A (Over.mk p)
  obtain ⟨z⟩ : Nonempty (Over.mk p ⊗ P.A).left := inferInstance
  obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB z (K := PEmpty) (fun k => k.elim) (fun k => k.elim)
    (fun k => k.elim) (fun k => k.elim)
  have hne : ∃ j, th.sec.f j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hth (DVR.SecOps.sec_ext hc)
  have hv := sval_ne_zero_of_isIso P.A.left (Over.mk p ⊗ P.A).left P.L P.isLB (Fin 1)
    (fun _ => (snd (Over.mk p) P.A).left) (fun _ => ((1 : ℕ) : ℤ)) th.sec hne _ (𝟙 _) z J hJ
  have h1 := hκ (Over.mk p ⊗ P.A) (fst _ _) (snd _ _) 1 z J hJ
  have h2 := AdditionTensor.sum_sval_mul_eq_zero (fst (Over.mk p) P.A).left (fst (Over.mk p) P.A).left
    (fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (fun _ => ((2 : ℕ) : ℤ))
    (fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (fun _ => ((2 : ℕ) : ℤ)) t t' h0
    (lift (fst (Over.mk p) P.A) (snd (Over.mk p) P.A)).left (lift (fst (Over.mk p) P.A) (1 : Over.mk p ⊗ P.A ⟶ P.A)).left
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z hJ
  have h3 := h1.symm.trans h2
  rw [inv_one, _root_.mul_one, lift_fst_snd, Units.mul_right_eq_zero, mul_self_eq_zero] at h3
  exact hv h3
end GlobalTheory
