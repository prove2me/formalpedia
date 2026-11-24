-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.exists_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:43:32.047114+00:00
-- url     : https://prove2.me/submissions/37f9d3f5-dcb3-4426-9a77-99a81b541539

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_realTensorEvalAlgHom_tmul
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
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
theorem _root_.solution (e : R' ⊗[R] H1 F ≃ₗ[R'] H1 (bcF F R'))
    (he : ∀ c, e (1 ⊗ₜ c) = (bcM F R').coef.pull1 c) (t : M ⊗[R] Z1 F) :
    ∃ z : Z1 (bcF F R'), z.1 = ev1 F j ((Z1 F).subtype.lTensor M t) ∧
      H1.mk (bcF F R') z = e (j.rTensor (H1 F) ((H1.mk F).lTensor M t)) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | tmul n c =>
    refine ⟨j n • (bcM F R').coef.pullbackOneCocycle c, ?_, ?_⟩
    · funext T T' φ
      show j n • ((1 : R') ⊗ₜ[R] (c.1 T T' φ)) = ev1 F j (n ⊗ₜ c.1) T T' φ
      rw [realTensorEvalAlgHom_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    · rw [map_smul, ← CoefMap.pullCohomologyOne_class]
      show j n • (bcM F R').coef.pull1 (H1.mk F c) = e (j n ⊗ₜ H1.mk F c)
      rw [← he, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨z1, h1, h1'⟩ := hx
    obtain ⟨z2, h2, h2'⟩ := hy
    refine ⟨z1 + z2, ?_, ?_⟩
    · simp only [Submodule.coe_add, h1, h2, map_add]
    · simp only [map_add, h1', h2']
end GlobalTheory.CompanionTheory.WedgeOf
