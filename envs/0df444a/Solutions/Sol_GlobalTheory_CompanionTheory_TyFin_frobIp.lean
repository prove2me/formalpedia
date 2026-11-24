-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.frobIp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:08:16.297225+00:00
-- url     : https://prove2.me/submissions/667a44d0-e915-43f7-a638-6bf9692b2636

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FrobeniusReciprocityInnerProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_sum_sum_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.FrobIp := by
  intro Γ _ _ A a c hc
  classical
  have hne : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hU : ((Set.univ : Set Γ).ncard : ℂ) = (Fintype.card Γ : ℂ) := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  have hA : ((A : Set Γ).ncard : ℂ) = (Nat.card A : ℂ) := by
    rw [← Nat.card_coe_set_eq]; rfl
  have hinv : ∀ h : Γ, h⁻¹ ∈ A ↔ h ∈ A := fun h => inv_mem_iff
  have hcx : ∀ x g : Γ, c (x * g * x⁻¹) = c g := hc
  constructor
  · have key : ∀ g x : Γ, (if x * g⁻¹ * x⁻¹ ∈ A then a (x * g⁻¹ * x⁻¹) else 0) * c g =
        (fun h => if h ∈ A then a h⁻¹ * c h else 0) (x * g * x⁻¹) := by
      intro g x
      have e : x * g⁻¹ * x⁻¹ = (x * g * x⁻¹)⁻¹ := by group
      simp only [e, hinv, hcx]
      split_ifs <;> simp
    have S : ∑ g, ((Nat.card A : ℂ)⁻¹ *
          ∑ x, if x * g⁻¹ * x⁻¹ ∈ A then a (x * g⁻¹ * x⁻¹) else 0) * c g =
        (Nat.card A : ℂ)⁻¹ * ((Fintype.card Γ : ℂ) * ∑ h, if h ∈ A then a h⁻¹ * c h else 0) := by
      rw [← sum_sum_conj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [mul_assoc, Finset.sum_mul]
      exact congrArg _ (Finset.sum_congr rfl fun x _ => key g x)
    simp only [ip, indF, Set.mem_univ, if_true, SetLike.mem_coe, hU, hA]
    rw [S]
    field_simp
  · have key : ∀ g x : Γ, c g⁻¹ * (if x * g * x⁻¹ ∈ A then a (x * g * x⁻¹) else 0) =
        (fun h => if h ∈ A then c h⁻¹ * a h else 0) (x * g * x⁻¹) := by
      intro g x
      have e : (x * g * x⁻¹)⁻¹ = x * g⁻¹ * x⁻¹ := by group
      simp only [e, hcx]
      split_ifs <;> simp
    have S : ∑ g, c g⁻¹ * ((Nat.card A : ℂ)⁻¹ *
          ∑ x, if x * g * x⁻¹ ∈ A then a (x * g * x⁻¹) else 0) =
        (Nat.card A : ℂ)⁻¹ * ((Fintype.card Γ : ℂ) * ∑ h, if h ∈ A then c h⁻¹ * a h else 0) := by
      rw [← sum_sum_conj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [mul_left_comm, Finset.mul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun x _ => key g x)
    simp only [ip, indF, Set.mem_univ, if_true, SetLike.mem_coe, hU, hA]
    rw [S]
    field_simp
end GlobalTheory.CompanionTheory.TyFin
