-- Prove2me | solution 1 for KummersLemma.map_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:15.954564+00:00
-- url     : https://prove2.me/submissions/c697b985-dff0-45d9-bc16-cba9ef9101d7

module
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_Field

set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField
attribute [local implicit_reducible] integralClosure NumberField.RingOfIntegers
variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K] (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
variable (u : (𝓞 K)ˣ)
  (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1) (hu : ∀ v : K, v ^ p ≠ u)
open Polynomial IsCyclotomicExtension.Rat
open KummersLemma
variable [IsCyclotomicExtension {p} ℚ K]
namespace KummersLemma
theorem _root_.solution : (poly hp hζ u hcong).map (algebraMap (𝓞 K) K) =
    (X - C (1 / (ζ - 1))) ^ p + C (u / (ζ - 1) ^ p : K) := by
  have hζ0 := hζ.sub_one_ne_zero hpri.out.one_lt
  apply mul_left_cancel₀ (C_ne_zero.mpr (pow_ne_zero p hζ0))
  have hspec := congr_arg (Polynomial.map (algebraMap (𝓞 K) K))
    (poly_spec hp hζ u hcong)
  simp only [Polynomial.map_mul, map_C, map_pow, map_sub, map_one, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, map_X] at hspec
  change (C ζ - 1) ^ p * _ = ((C ζ - 1) * X - 1) ^ p + C (u : K) at hspec
  rw [map_pow, map_sub, map_one, hspec, mul_add, ← mul_pow]
  congr 1
  · rw [mul_sub, ← C_1, ← C_sub, ← C_mul, mul_one_div_cancel hζ0]
  · rw [← C_1, ← C_sub, ← C_pow, ← C_mul, mul_div_cancel₀ _ (pow_ne_zero p hζ0)]
end KummersLemma
