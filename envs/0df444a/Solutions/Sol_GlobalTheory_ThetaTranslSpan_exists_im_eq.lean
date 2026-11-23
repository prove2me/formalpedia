-- Prove2me | solution 1 for GlobalTheory.ThetaTranslSpan.exists_im_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:39.967746+00:00
-- url     : https://prove2.me/submissions/2d136f59-177d-4b9c-b9c8-497ef48d2b67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslSpan
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.ThetaTranslSpan
theorem _root_.solution (hH : Hm.PosDef) (f : (Fin g → ℂ) →ₗ[ℝ] ℝ) :
    ∃ y, ∀ a, (star y ⬝ᵥ Hm.mulVec a).im = f a := by
  let B : LinearMap.BilinForm ℝ (Fin g → ℂ) := LinearMap.mk₂ ℝ
    (fun v a => (star v ⬝ᵥ Hm.mulVec a).im)
    (fun a b m => by rw [star_add, add_dotProduct, Complex.add_im])
    (fun t a m => by rw [star_smul, smul_dotProduct, Complex.smul_im, star_trivial])
    (fun m a b => by rw [mulVec_add, dotProduct_add, Complex.add_im])
    (fun t m a => by rw [mulVec_smul, dotProduct_smul, Complex.smul_im])
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun u hu => ?_
    by_contra hne
    have h1 := hH.dotProduct_mulVec_pos hne
    have h2 : (star u ⬝ᵥ Hm.mulVec (Complex.I • u)).im = 0 := LinearMap.congr_fun hu _
    rw [mulVec_smul, dotProduct_smul] at h2
    simp at h2
    have := (Complex.pos_iff.1 h1).1
    linarith
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := Fin g → ℂ)).symm).1 hinj
  obtain ⟨y, hy⟩ := hsurj f
  exact ⟨y, fun a => LinearMap.congr_fun hy a⟩
end GlobalTheory.ThetaTranslSpan
