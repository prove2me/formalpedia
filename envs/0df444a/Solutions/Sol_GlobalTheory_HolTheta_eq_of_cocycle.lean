-- Prove2me | solution 1 for GlobalTheory.HolTheta.eq_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:41.986685+00:00
-- url     : https://prove2.me/submissions/169c3747-837c-4c9f-bc94-e32a97f599af

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
open Matrix
variable {g : ℕ}
namespace GlobalTheory.HolTheta
namespace _root_.GlobalTheory.HolTheta
theorem _root_.solution {La κ : Type*} [AddCommGroup La] (bs : Module.Basis κ ℤ La) (E : La → La → ℂ)
    {χ ψ : La → ℂ} (hE : ∀ x y, E x y ≠ 0) (hχ0 : ∀ x, χ x ≠ 0) (hψ0 : ∀ x, ψ x ≠ 0)
    (hχ : ∀ x y, χ (x + y) = χ x * χ y * E x y) (hψ : ∀ x y, ψ (x + y) = ψ x * ψ y * E x y)
    (hb : ∀ i, χ (bs i) = ψ (bs i)) (x : La) : χ x = ψ x := by
  have h0 : χ 0 = ψ 0 := by
    have h1 := hχ 0 0
    have h2 := hψ 0 0
    simp only [add_zero] at h1 h2
    have e1 : χ 0 * E 0 0 = 1 := by
      apply mul_left_cancel₀ (hχ0 0)
      linear_combination -h1
    have e2 : ψ 0 * E 0 0 = 1 := by
      apply mul_left_cancel₀ (hψ0 0)
      linear_combination -h2
    linear_combination ψ 0 * e1 - χ 0 * e2
  let S : AddSubgroup La :=
    { carrier := {x | χ x = ψ x}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [hχ, hψ, hx, hy]
      zero_mem' := h0
      neg_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        have h1 := hχ x (-x)
        have h2 := hψ x (-x)
        rw [add_neg_cancel] at h1 h2
        have hne : ψ x * E x (-x) ≠ 0 := mul_ne_zero (hψ0 x) (hE x (-x))
        apply mul_left_cancel₀ hne
        linear_combination -(E x (-x)) * χ (-x) * hx - h1 + h2 + h0 }
  have hspan : Submodule.span ℤ (Set.range bs) ≤ S.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hb i
  rw [bs.span_eq] at hspan
  exact hspan Submodule.mem_top
end _root_.GlobalTheory.HolTheta
end GlobalTheory.HolTheta
