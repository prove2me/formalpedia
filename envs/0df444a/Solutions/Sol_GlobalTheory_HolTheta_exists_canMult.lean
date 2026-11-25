-- Prove2me | solution 1 for GlobalTheory.HolTheta.exists_canMult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:57:19.284675+00:00
-- url     : https://prove2.me/submissions/e897fd5b-698f-4362-8d94-bf7bf1f9f118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsThetaHolomorphic
import Theorems.Thm_GlobalTheory_HolTheta_canMult_add
import Theorems.Thm_GlobalTheory_HolTheta_eq_of_cocycle
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_eq_sum
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_eq_sum
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.HolTheta
open Matrix GlobalTheory.CanTh GlobalTheory.RiemannRel
variable {g : ℕ}
namespace GlobalTheory.HolTheta
theorem _root_.solution {La : Type*} [AddCommGroup La] (bs : Module.Basis (Fin g ⊕ Fin g) ℤ La)
    (EF : LinearMap.BilinForm ℤ La) (halt : EF.IsAlt) (hbs : IsSymplecticBasis (-EF) bs) {χ : La → ℂ}
    (h1 : ∀ x, χ x = 1 ∨ χ x = -1) (hχ : ∀ x y, χ (x + y) = χ x * χ y * (-1) ^ EF x y) :
    ∃ a c : Fin g → ℝ, ∀ x, χ x =
      canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  classical
  have key : ∀ x, ∃ t : ℝ, Complex.exp (2 * Real.pi * Complex.I * t) = χ x := fun x => by
    rcases h1 x with h | h
    · exact ⟨0, by simp [h]⟩
    · refine ⟨1 / 2, ?_⟩
      rw [h, ← Complex.exp_pi_mul_I]
      congr 1
      push_cast
      ring
  choose t ht using key
  refine ⟨fun i => t (bs (Sum.inl i)), fun i => -t (bs (Sum.inr i)),
    eq_of_cocycle bs (fun x y => (-1) ^ EF x y) (fun x y => zpow_ne_zero _ (by norm_num))
      (fun x => by rcases h1 x with h | h <;> simp [h]) (fun x => Complex.exp_ne_zero _) hχ (fun x y => ?_) ?_⟩
  · have h := hbs.apply_eq_sum halt.neg x y
    have e : EF x y = (fun i => bs.repr x (Sum.inr i)) ⬝ᵥ (fun i => bs.repr y (Sum.inl i)) -
        (fun i => bs.repr x (Sum.inl i)) ⬝ᵥ (fun i => bs.repr y (Sum.inr i)) := by
      simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at h
      rw [h]
      simp [dotProduct]
    rw [e, ← canMult_add, map_add]
    rfl
  · rintro (i | i)
    · rw [← ht, canMult]
      simp [dotProduct, Finsupp.single_apply]
    · rw [← ht, canMult]
      simp [dotProduct, Finsupp.single_apply]
end GlobalTheory.HolTheta
