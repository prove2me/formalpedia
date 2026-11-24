-- Prove2me | solution 1 for KummersLemma.isUnramified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:48:04.900404+00:00
-- url     : https://prove2.me/submissions/24e42a10-2238-4843-b0c6-5c3b7b0d1423

module
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_Field
public import Theorems.Thm_P2M_KummersLemma_minpoly_polyRoot__d5ceeb384e63
public import Theorems.Thm_KummersLemma_separable_poly
public import Theorems.Thm_KummersLemma_mem_adjoin_polyRoot
public import Theorems.Thm_isUnramifiedAt_of_Separable_minpoly


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
include hu hp hζ hcong
attribute [local instance] Ideal.Quotient.field
namespace KummersLemma
theorem _root_.solution (L) [Field L] [Algebra K L] [IsSplittingField K L (X ^ p - C (u : K))] :
    Algebra.Unramified (𝓞 K) (𝓞 L) := by
  let α := polyRoot hp hζ u hcong _ (rootOfSplitsXPowSubC_pow _ L) 0
  have := Polynomial.IsSplittingField.finiteDimensional L (X ^ p - C (u : K))
  have : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  have hα : Algebra.adjoin K {(α : L)} = ⊤ := by
    rw [eq_top_iff, ← Algebra.adjoin_root_eq_top_of_isSplittingField
      ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩
      (X_pow_sub_C_irreducible_of_prime hpri.out hu) (rootOfSplitsXPowSubC_pow (u : K) L),
      Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact mem_adjoin_polyRoot hp hζ u hcong _ _ 0
  refine Algebra.unramified_iff_forall.mpr ?_
  rintro ⟨P, hP⟩
  by_cases hPbot : P = ⊥
  · subst P
    exact Algebra.isUnramifiedAt_bot
  refine isUnramifiedAt_of_Separable_minpoly K L P hPbot α (IsIntegral.tower_top α.prop) hα ?_
  rw [minpoly_polyRoot' hp hζ u hcong hu]
  have hPbot' : P.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) hPbot
  have : (P.under (𝓞 K)).IsMaximal :=
    (inferInstance : (P.under (𝓞 K)).IsPrime).isMaximal hPbot'
  exact separable_poly hp hζ u hcong hu (P.under (𝓞 K))
end KummersLemma
