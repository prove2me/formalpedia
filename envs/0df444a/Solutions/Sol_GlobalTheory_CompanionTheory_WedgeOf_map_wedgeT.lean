-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.map_wedgeT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:35:57.750747+00:00
-- url     : https://prove2.me/submissions/c466a357-8157-430c-bb79-1347c10f353d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZero
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_tmul
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution {W : Type} [AddCommGroup W] [Module R W] (r : W →ₗ[R] V) (s : W ⊗[R] W) :
    exteriorPower.map 2 r (wedgeT (R := R) W s) = wedgeT (R := R) V (TensorProduct.map r r s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [TensorProduct.map_tmul, wedgeT_tmul, wedgeT_tmul, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    fin_cases i <;> rfl
  | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.CompanionTheory.WedgeOf
