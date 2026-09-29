-- Prove2me | solution 1 for ModularCurve.coeffMap_pow_char_eq_qExpand_of_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d10d5be2-6ff4-5559-9ed6-839da0f16243

import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff coeffMap coeffMap_coeff coeffMap_coeffMap coeffMap_congr qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd coeffSemilinearAut pow_char_eq_map_frobenius_qExpand"
p2m_open "ModularCurve"

p2m_open "ModularCurve.coeffSemilinearAut"

section CoeffGrain

variable {A k : Type*} [CommRing A] [CommRing k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
variable (red : A →+* k) (τ : A →+* A)

private theorem coeffMap_pow_char_eq_qExpand_of_frobenius (hτ : ∀ a : A, red (τ a) ^ ℓ = red a) (x : LaurentSeries A) :
    coeffMap red (coeffMap τ x) ^ ℓ = qExpand k ℓ (coeffMap red x) := by
  rw [pow_char_eq_map_frobenius_qExpand ℓ (coeffMap red (coeffMap τ x)),
    show (qExpand k ℓ (coeffMap red (coeffMap τ x))).map (frobenius k ℓ)
        = coeffMap (frobenius k ℓ) (qExpand k ℓ (coeffMap red (coeffMap τ x))) from rfl,
    coeffMap_qExpand, coeffMap_coeffMap, coeffMap_coeffMap]
  congr 1
  refine coeffMap_congr (RingHom.ext fun a => ?_) x
  rw [RingHom.comp_apply, RingHom.comp_apply, frobenius_def]
  exact hτ a

private theorem coeffMap_eq_of_inertial (hτ : ∀ a : A, red (τ a) = red a) (x : LaurentSeries A) :
    coeffMap red (coeffMap τ x) = coeffMap red x := by
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun a => hτ a) x

end CoeffGrain

section ApparatusGrain

variable {L k : Type*} [CommRing L] [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
variable (A : Subring L) (red : A →+* k) (τL : L →+* L)

private theorem coeffMap_mem_integralCoeffs (hτA : ∀ a ∈ A, τL a ∈ A) {x : LaurentSeries L}
    (hx : x ∈ CharPReduction.integralCoeffs A) : coeffMap τL x ∈ CharPReduction.integralCoeffs A := fun n => by
  rw [coeffMap_coeff]
  exact hτA _ (hx n)

private def restrictEndo (hτA : ∀ a ∈ A, τL a ∈ A) : A →+* A := τL.restrict A A hτA

@[scoped simp] theorem coe_restrictEndo_apply (hτA : ∀ a ∈ A, τL a ∈ A) (a : A) :
    (restrictEndo A τL hτA a : L) = τL a := rfl

private theorem coeffRed_coeffMap_coeff (hτA : ∀ a ∈ A, τL a ∈ A) (x : CharPReduction.integralCoeffs A) (n : ℤ) :
    (CharPReduction.coeffRed A red ⟨coeffMap τL (x : LaurentSeries L), coeffMap_mem_integralCoeffs A τL hτA x.2⟩).coeff n
      = red (restrictEndo A τL hτA ⟨(x : LaurentSeries L).coeff n, x.2 n⟩) := by
  rw [CharPReduction.coeffRed_coeff]
  rfl

private theorem coeffRed_coeffMap_pow_char_eq_qExpand (hτA : ∀ a ∈ A, τL a ∈ A)
    (hF : ∀ a : A, red (restrictEndo A τL hτA a) ^ ℓ = red a) (x : CharPReduction.integralCoeffs A) :
    CharPReduction.coeffRed A red ⟨coeffMap τL (x : LaurentSeries L), coeffMap_mem_integralCoeffs A τL hτA x.2⟩ ^ ℓ
      = qExpand k ℓ (CharPReduction.coeffRed A red x) := by
  rw [pow_char_eq_map_frobenius_qExpand ℓ]
  ext n
  rw [HahnSeries.map_coeff]
  by_cases h : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffRed_coeffMap_coeff A red τL hτA, frobenius_def, hF,
      CharPReduction.coeffRed_coeff]
  · rw [qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

private theorem coeffRed_coeffMap_eq_of_inertial (hτA : ∀ a ∈ A, τL a ∈ A)
    (hI : ∀ a : A, red (restrictEndo A τL hτA a) = red a) (x : CharPReduction.integralCoeffs A) :
    CharPReduction.coeffRed A red ⟨coeffMap τL (x : LaurentSeries L), coeffMap_mem_integralCoeffs A τL hτA x.2⟩
      = CharPReduction.coeffRed A red x := by
  ext n
  rw [coeffRed_coeffMap_coeff A red τL hτA, hI, CharPReduction.coeffRed_coeff]

end ApparatusGrain

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius.ModularCurve"

#check @ModularCurve.coeffMap_pow_char_eq_qExpand_of_frobenius
#print axioms ModularCurve.coeffMap_pow_char_eq_qExpand_of_frobenius
#check @ModularCurve.coeffRed_coeffMap_pow_char_eq_qExpand
#print axioms ModularCurve.coeffRed_coeffMap_pow_char_eq_qExpand
#check @ModularCurve.coeffRed_coeffMap_eq_of_inertial

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius.ModularCurve in
theorem solution {A k : Type*} [CommRing A] [CommRing k] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP k ℓ] (red : A →+* k) (τ : A →+* A) (hτ : ∀ a : A, red (τ a) ^ ℓ = red a)
    (x : LaurentSeries A) :
    ModularCurve.coeffMap red (ModularCurve.coeffMap τ x) ^ ℓ
      = ModularCurve.qExpand k ℓ (ModularCurve.coeffMap red x) :=
  ModularCurve.coeffMap_pow_char_eq_qExpand_of_frobenius ℓ red τ hτ x

end S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius
end P2MW
export P2MW.S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius (solution)
