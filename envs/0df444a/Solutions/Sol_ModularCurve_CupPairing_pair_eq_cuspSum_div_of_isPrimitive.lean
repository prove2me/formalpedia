-- Prove2me | solution 1 for ModularCurve.CupPairing.pair_eq_cuspSum_div_of_isPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1f725dee-05a9-591c-8317-ca8fa67c3743

import Mathlib
import Definitions.Def_ModularCurve_CupPairing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CupPairing_pair_eq_cuspSum_div_of_isPrimitive

set_option autoImplicit false

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "CupPairing.IsPrimitive CupPairing.mult CupPairing.pair PDPairing.cuspGen PDPairing.cuspSum"
namespace CupPairing
p2m_export "ModularCurve.CupPairing" "IsPrimitive mult pair pair_eq_dif"
namespace Indep
p2m_open "ModularCurve.CupPairing ModularCurve"

open ModularCurve.PDPairing

theorem S_sq : ModularGroup.S * ModularGroup.S = (-1 : SL(2, ℤ)) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simpa using ModularGroup.S_mul_S_eq

theorem S_pow_four : ModularGroup.S ^ 4 = (1 : SL(2, ℤ)) := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq ModularGroup.S, S_sq, neg_one_sq]

theorem ST_pow_three : (ModularGroup.S * ModularGroup.T) ^ 3 = (-1 : SL(2, ℤ)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_S, ModularGroup.coe_T, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.one_fin_two]

theorem ST_pow_six : (ModularGroup.S * ModularGroup.T) ^ 6 = (1 : SL(2, ℤ)) := by
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, ST_pow_three, neg_one_sq]

theorem hom_T_eq_one (f : SL(2, ℤ) →* Multiplicative ℚ) : f ModularGroup.T = 1 := by
  have hS : f ModularGroup.S = 1 := by
    have h : (f ModularGroup.S) ^ 4 = 1 := by rw [← map_pow, S_pow_four, map_one]
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_pow, toAdd_one, smul_eq_zero] at h'
    rcases h' with h' | h'
    · norm_num at h'
    · exact toAdd_eq_zero.mp h'
  have hU : f (ModularGroup.S * ModularGroup.T) = 1 := by
    have h : (f (ModularGroup.S * ModularGroup.T)) ^ 6 = 1 := by
      rw [← map_pow, ST_pow_six, map_one]
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_pow, toAdd_one, smul_eq_zero] at h'
    rcases h' with h' | h'
    · norm_num at h'
    · exact toAdd_eq_zero.mp h'
  have : ModularGroup.T = ModularGroup.S⁻¹ * (ModularGroup.S * ModularGroup.T) := by
    rw [inv_mul_cancel_left]
  rw [this, map_mul, map_inv, hS, hU, inv_one, one_mul]

variable (Γ : Subgroup SL(2, ℤ))

theorem sum_apply_cuspGen_eq_zero [Γ.FiniteIndex] (χ : Additive Γ →+ ℚ) :
    ∑ q : Cusp Γ, χ (Additive.ofMul (cuspGen Γ q)) = 0 := by
  have h := (AddMonoidHom.toMultiplicativeRight χ).transfer_eq_prod_quotient_orbitRel_zpowers_quot
    ModularGroup.T
  rw [hom_T_eq_one] at h
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_one, toAdd_prod] at h'
  rw [h']
  rfl

variable {Γ}

def diffChar (φ ψ : Additive Γ →+ ℚ) (h₀ h : Γ → ℚ) (hh₀ : IsPrimitive φ ψ h₀)
    (hh : IsPrimitive φ ψ h) : Additive Γ →+ ℚ where
  toFun g := h₀ (Additive.toMul g) - h (Additive.toMul g)
  map_zero' := by
    have e₀ := hh₀ 1 1
    have e := hh 1 1
    rw [one_mul, omega_one_left, sub_zero] at e₀ e
    change h₀ 1 - h 1 = 0
    linear_combination -e₀ + e
  map_add' a b := by
    change h₀ (Additive.toMul a * Additive.toMul b) - h (Additive.toMul a * Additive.toMul b) =
      (h₀ (Additive.toMul a) - h (Additive.toMul a)) + (h₀ (Additive.toMul b) - h (Additive.toMul b))
    rw [hh₀, hh]
    ring

theorem diffChar_apply (φ ψ : Additive Γ →+ ℚ) (h₀ h : Γ → ℚ) (hh₀ : IsPrimitive φ ψ h₀)
    (hh : IsPrimitive φ ψ h) (g : Γ) :
    diffChar φ ψ h₀ h hh₀ hh (Additive.ofMul g) = h₀ g - h g := rfl

theorem cuspSum_eq_of_isPrimitive [Γ.FiniteIndex] (φ ψ : Additive Γ →+ ℚ) (h₀ h : Γ → ℚ)
    (hh₀ : IsPrimitive φ ψ h₀) (hh : IsPrimitive φ ψ h) : cuspSum Γ h₀ = cuspSum Γ h := by
  have hsplit : h₀ = h + (fun g => diffChar φ ψ h₀ h hh₀ hh (Additive.ofMul g)) := by
    funext g
    simp only [Pi.add_apply, diffChar_apply]
    ring
  rw [hsplit, cuspSum_add]
  unfold cuspSum
  rw [sum_apply_cuspGen_eq_zero Γ (diffChar φ ψ h₀ h hh₀ hh), add_zero]

theorem main [Γ.FiniteIndex] (φ ψ : Additive Γ →+ ℚ) (h : Γ → ℚ) (hh : IsPrimitive φ ψ h) :
    pair Γ φ ψ = cuspSum Γ h / (2 * mult Γ) := by
  have hp : ∃ h' : Γ → ℚ, IsPrimitive φ ψ h' := ⟨h, hh⟩
  rw [pair_eq_dif Γ φ ψ hp, cuspSum_eq_of_isPrimitive φ ψ _ h (Classical.choose_spec hp) hh]

end ModularCurve.CupPairing.Indep

theorem solution (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] (φ ψ : Additive Γ →+ ℚ) (h : Γ → ℚ)
    (hh : ModularCurve.CupPairing.IsPrimitive φ ψ h) :
    ModularCurve.CupPairing.pair Γ φ ψ =
      ModularCurve.PDPairing.cuspSum Γ h / (2 * ModularCurve.CupPairing.mult Γ) :=
  ModularCurve.CupPairing.Indep.main φ ψ h hh

end S_ModularCurve_CupPairing_pair_eq_cuspSum_div_of_isPrimitive
end P2MW
export P2MW.S_ModularCurve_CupPairing_pair_eq_cuspSum_div_of_isPrimitive (solution)
