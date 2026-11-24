-- Prove2me | solution 1 for KummersLemma.separable_poly_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:00.916804+00:00
-- url     : https://prove2.me/submissions/b0b20979-90ed-4e87-ab11-ecab81a67ee2

module
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_Field
public import Theorems.Thm_KummersLemma_map_poly_eq_prod

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
theorem _root_.solution {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) : Separable ((poly hp hζ u hcong).map
    (algebraMap (𝓞 K) (𝓞 L))) := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [map_poly_eq_prod (e := e)]
  refine separable_prod' ?_ (fun _ _ ↦ separable_X_sub_C)
  intros i hi j hj hij
  apply isCoprime_X_sub_C_of_isUnit_sub
  obtain ⟨v, hv⟩ : Associated (hζ.toInteger - 1 : 𝓞 K)
      ((hζ.toInteger : 𝓞 K) ^ j - (hζ.toInteger : 𝓞 K) ^ i) := by
    refine hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out ?_ ?_ ?_
    · rw [Finset.mem_coe, mem_nthRootsFinset (NeZero.pos p), ← pow_mul, mul_comm, pow_mul,
        hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    · rw [Finset.mem_coe, mem_nthRootsFinset (NeZero.pos p), ← pow_mul, mul_comm, pow_mul,
        hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    · exact mt (hζ.toInteger_isPrimitiveRoot.injOn_pow hj hi) hij.symm
  rw [NumberField.RingOfIntegers.ext_iff] at hv
  have hcoe : (algebraMap (𝓞 K) K) (↑hζ.toInteger) = ζ := rfl
  simp only [map_mul, map_sub, map_one, map_pow, hcoe] at hv
  have hα : IsIntegral (𝓞 K) α := by
    apply IsIntegral.of_pow (NeZero.pos p)
    rw [e]
    exact isIntegral_algebraMap
  have : IsUnit (⟨α, isIntegral_trans _ hα⟩ : 𝓞 L) := by
    rw [← isUnit_pow_iff (NeZero.pos p).ne.symm]
    have hpow : (⟨α, isIntegral_trans _ hα⟩ : 𝓞 L) ^ p =
        algebraMap (𝓞 K) (𝓞 L) ↑u := by
      ext
      simp only [SubmonoidClass.coe_pow, e]
      rfl
    rw [hpow]
    exact (algebraMap (𝓞 K) (𝓞 L)).isUnit_map u.isUnit
  convert ((algebraMap (𝓞 K) (𝓞 L)).isUnit_map v.isUnit).mul this using 1
  ext
  simp only [polyRoot, map_sub, map_one, sub_div, one_div, map_sub,
    sub_sub_sub_cancel_left, map_mul, NumberField.RingOfIntegers.map_mk]
  rw [← sub_div, ← sub_smul, ← hv, Algebra.smul_def, map_mul, map_sub, map_one, mul_assoc,
    mul_div_cancel_left₀ _ hζ']
  rfl
end KummersLemma
