-- Prove2me | solution 1 for KummersLemma.separable_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:58.20016+00:00
-- url     : https://prove2.me/submissions/3e04aecc-535d-466d-858d-e3216d9b67b7

module
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_Field
public import Theorems.Thm_KummersLemma_separable_poly_aux

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
set_option backward.isDefEq.respectTransparency false
include hu
open scoped KummerExtension
attribute [local instance] Ideal.Quotient.field
namespace KummersLemma
theorem _root_.solution (I : Ideal (𝓞 K)) [I.IsMaximal] :
    Separable ((poly hp hζ u hcong).map (Ideal.Quotient.mk I)) := by
  let L := K[p√(u : K)]
  have := Fact.mk (X_pow_sub_C_irreducible_of_prime hpri.out hu)
  let J := I.map (algebraMap (𝓞 K) (𝓞 L))
  let i : 𝓞 K ⧸ I →+* 𝓞 L ⧸ J := Ideal.quotientMap _
    (algebraMap (𝓞 K) (𝓞 L)) Ideal.le_comap_map
  have : Nontrivial (𝓞 L ⧸ J) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    rw [ne_eq, Ideal.map_eq_top_iff]
    · exact Ideal.IsMaximal.ne_top ‹_›
    · intros x y e
      ext
      exact (algebraMap K L).injective (congr_arg Subtype.val e)
    · intro x
      exact IsIntegral.tower_top (IsIntegralClosure.isIntegral ℤ L x)
  rw [← Polynomial.separable_map i, map_map, Ideal.quotientMap_comp_mk, ← map_map]
  exact Separable.map <|
    separable_poly_aux hp hζ u hcong (AdjoinRoot.root _) (root_X_pow_sub_C_pow _ _)
end KummersLemma
