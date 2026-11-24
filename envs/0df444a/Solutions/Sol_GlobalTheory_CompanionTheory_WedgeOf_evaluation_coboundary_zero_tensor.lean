-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.evaluation_coboundary_zero_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:43:31.080291+00:00
-- url     : https://prove2.me/submissions/b7643cc1-292c-451e-874a-9607fa02586d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_evaluation_zero_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_realTensorEvalAlgHom_tmul
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  (R' : Type) [CommRing R'] [Algebra R R']
variable {R'} {M : Type} [AddCommGroup M] [Module R M] (j : M →ₗ[R] R')
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution (y : M ⊗[R] C0 F) :
    ev1 F j ((d0 F).lTensor M y) = d0 (bcF F R') (ev0 F j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul n g =>
    funext T T' φ
    show ev1 F j (n ⊗ₜ d0 F g) T T' φ = ev0 F j (n ⊗ₜ g) T' - mp (bcF F R') φ (ev0 F j (n ⊗ₜ g) T)
    rw [realTensorEvalAlgHom_tmul, evaluation_zero_tmul, evaluation_zero_tmul, amitsur_d0_apply]
    show j n ⊗ₜ (g T' - mp F φ (g T)) =
      j n ⊗ₜ g T' - (Algebra.TensorProduct.map (AlgHom.id R' R') (mp F φ)) (j n ⊗ₜ g T)
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.tmul_sub]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.CompanionTheory.WedgeOf
