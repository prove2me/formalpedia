-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicGauss_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:42:47.154064+00:00
-- url     : https://prove2.me/submissions/a207bbb9-6e31-4ee4-bd5c-c15b5fe5fd62

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_pow_three
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_ne_one
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_order
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_eq_neg_primary_generator_of_principal

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution {E : Type*} [Field E] (ι : O →+* E)
    (hι : Function.Injective ι) (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
    (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 =
      -(ι p) * (Nat.card (O ⧸ P) : E) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := cubicChar P hgood
  let ξ := χ.ringHomComp ι
  have hχ3 : χ ^ 3 = 1 := cubicChar_pow_three P hgood
  have hχne : χ ≠ 1 := cubicChar_ne_one P hgood
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have hd : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [cubicChar_order P hgood] at hd
    norm_num at hd
  have hξne : ξ ≠ 1 := (MulChar.ringHomComp_ne_one_iff hι).mpr hχne
  have hξ2 : ξ * ξ ≠ 1 := by
    rw [show ξ * ξ = (χ * χ).ringHomComp ι by
      exact (MulChar.ringHomComp_mul χ χ ι).symm]
    exact (MulChar.ringHomComp_ne_one_iff hι).mpr hχ2
  have hχinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using hχ3
  have hξinv : ξ⁻¹ = ξ ^ 2 := by
    change (χ.ringHomComp ι)⁻¹ = (χ.ringHomComp ι) ^ 2
    rw [MulChar.ringHomComp_inv, MulChar.ringHomComp_pow, hχinv]
  have hξmul : ξ * ξ = ξ⁻¹ := by rw [hξinv, pow_two]
  have hχneg : χ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) hχ3
  have hξneg : ξ (-1) = 1 := by
    change ι (χ (-1)) = 1
    rw [hχneg, map_one]
  have hξinvneg : ξ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hξneg, inv_one]
  have hgs : gaussSum ξ ψ * gaussSum ξ⁻¹ ψ = (Nat.card (O ⧸ P) : E) := by
    have h := gaussSum_mul_gaussSum_eq_card hξne hψ
    have hshift := mul_gaussSum_inv_eq_gaussSum ξ⁻¹ ψ
    rw [hξinvneg, one_mul] at hshift
    rw [hshift] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hJ : jacobiSum ξ ξ = -(ι p) := by
    change jacobiSum (χ.ringHomComp ι) (χ.ringHomComp ι) = -(ι p)
    rw [jacobiSum_ringHomComp]
    rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
      map_neg]
  have hgj : gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ = gaussSum ξ ψ * gaussSum ξ ψ := by
    simpa only [hξmul] using jacobiSum_mul_nontrivial hξ2 ψ
  calc
    gaussSum ξ ψ ^ 3 = (gaussSum ξ ψ * gaussSum ξ ψ) * gaussSum ξ ψ := by ring
    _ = (gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ) * gaussSum ξ ψ := by rw [hgj]
    _ = (gaussSum ξ ψ * gaussSum ξ⁻¹ ψ) * jacobiSum ξ ξ := by ring
    _ = -(ι p) * (Nat.card (O ⧸ P) : E) := by rw [hgs, hJ]; ring
end OAI.ActualEisensteinCubic
