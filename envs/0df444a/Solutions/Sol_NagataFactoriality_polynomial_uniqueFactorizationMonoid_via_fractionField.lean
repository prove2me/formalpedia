-- Prove2me | solution 1 for NagataFactoriality.polynomial_uniqueFactorizationMonoid_via_fractionField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:05.97583+00:00
-- url     : https://prove2.me/submissions/48231fb0-b706-4a1f-a359-a7b6933fb212

import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Definitions.Def_NagataFactoriality_Applications_FractionField
import Theorems.Thm_NagataFactoriality_IsLocalization_map_eq_zero_iff
import Theorems.Thm_NagataFactoriality_IsLocalization_surj
import Theorems.Thm_NagataFactoriality_Localization_den_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_den
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_of
import Theorems.Thm_NagataFactoriality_Localization_mk_one
import Theorems.Thm_NagataFactoriality_Localization_of_add
import Theorems.Thm_NagataFactoriality_Localization_of_eq_zero_iff
import Theorems.Thm_NagataFactoriality_Localization_of_mul
import Theorems.Thm_NagataFactoriality_Localization_of_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_of_neg
import Theorems.Thm_NagataFactoriality_Localization_of_one
import Theorems.Thm_NagataFactoriality_Localization_of_zero
import Theorems.Thm_NagataFactoriality_Localization_surj
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
import Theorems.Thm_NagataFactoriality_multiset_prod_mem_of_factors
import Theorems.Thm_NagataFactoriality_nagata_theorem
import Theorems.Thm_NagataFactoriality_primeGenerated_closure_of_primes
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
attribute [local simp] NagataFactoriality.IsLocalization.map_eq_zero_iff
attribute [local simp] NagataFactoriality.Localization.den_mul_mk
attribute [local simp] NagataFactoriality.Localization.mk_mul_den
attribute [local simp] NagataFactoriality.Localization.mk_mul_mk
attribute [local simp] NagataFactoriality.Localization.mk_mul_of
attribute [local simp] NagataFactoriality.Localization.mk_one
attribute [local simp] NagataFactoriality.Localization.of_add
attribute [local simp] NagataFactoriality.Localization.of_eq_zero_iff
attribute [local simp] NagataFactoriality.Localization.of_mul
attribute [local simp] NagataFactoriality.Localization.of_mul_mk
attribute [local simp] NagataFactoriality.Localization.of_neg
attribute [local simp] NagataFactoriality.Localization.of_one
attribute [local simp] NagataFactoriality.Localization.of_zero
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil
attribute [local simp] P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096
attribute [local simp] P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
attribute [local simp] P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
attribute [local simp] P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c


section
namespace NagataFactoriality
open Polynomial
section FractionFieldRoute
noncomputable section
variable (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
omit [IsDomain R] [UniqueFactorizationMonoid R] in
private theorem constPrimeSubmonoid_primeGenerated :
    PrimeGenerated (constPrimeSubmonoid R) :=
  primeGenerated_closure_of_primes (fun _ ⟨_, hr, hrq⟩ => hrq ▸ Polynomial.prime_C_iff.mpr hr)
omit [UniqueFactorizationMonoid R] in
private theorem constPrimeSubmonoid_le_nzdMapC :
    constPrimeSubmonoid R ≤ nzdMapC R := by
  apply Submonoid.closure_le.mpr
  intro x hx
  rcases hx with ⟨r, hr, rfl⟩
  have hr' : Prime r := by simpa using hr
  exact Submonoid.mem_map.2 ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr'.ne_zero, rfl⟩
variable {R}
private theorem isUnit_algebraMap_C_of_ne_zero (r : R) (hr : r ≠ 0) :
    IsUnit (algebraMap R[X] (_root_.Localization (constPrimeSubmonoid R)) (C r)) := by
  obtain ⟨f, hf_prime, hf_assoc⟩ := UniqueFactorizationMonoid.exists_prime_factors r hr
  -- Associated (C f.prod) (C r) in R[X], mapping through algebraMap preserves this
  have hassocC := (hf_assoc.map (C : R →+* R[X])).map
    (algebraMap R[X] (_root_.Localization (constPrimeSubmonoid R)))
  -- C f.prod ∈ constPrimeSubmonoid, hence maps to a unit
  have hmem : C f.prod ∈ constPrimeSubmonoid R := by
    have : C f.prod = (f.map C).prod := by
      rw [Multiset.prod_hom]
    rw [this]
    exact multiset_prod_mem_of_factors (fun q hq => by
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hq
      exact Submonoid.subset_closure ⟨p, hf_prime p hp, rfl⟩)
  exact hassocC.isUnit_iff.mp (IsLocalization.map_units _ ⟨_, hmem⟩)
variable (R)
private theorem isLocalization_nzdMapC_localization :
    IsLocalization (nzdMapC R) (_root_.Localization (constPrimeSubmonoid R)) where
  map_units := by
    intro ⟨t, ht⟩
    obtain ⟨r, hr, rfl⟩ := ht
    exact isUnit_algebraMap_C_of_ne_zero r (mem_nonZeroDivisors_iff_ne_zero.mp hr)
  surj := by
    intro z
    obtain ⟨⟨a, s⟩, hz⟩ := _root_.IsLocalization.surj (M := constPrimeSubmonoid R) z
    exact ⟨⟨a, ⟨s, constPrimeSubmonoid_le_nzdMapC R s.2⟩⟩, hz⟩
  exists_of_eq := by
    intro x y hxy
    obtain ⟨⟨c, hc⟩, hcxy⟩ := _root_.IsLocalization.exists_of_eq (M := constPrimeSubmonoid R) hxy
    exact ⟨⟨c, constPrimeSubmonoid_le_nzdMapC R hc⟩, hcxy⟩
end
end FractionFieldRoute
end NagataFactoriality
end

set_option autoImplicit false
open NagataFactoriality
open Polynomial
noncomputable section
variable (R : Type*) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {R}
variable (R)
namespace NagataFactoriality
theorem _root_.solution
    [IsNoetherianRing R] : UniqueFactorizationMonoid R[X] := by
  let S := constPrimeSubmonoid R
  have hS : PrimeGenerated S := constPrimeSubmonoid_primeGenerated R
  letI : Fact ((0 : R[X]) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  -- Set up the algebra structure on (FractionRing R)[X] over R[X]
  letI : Algebra R[X] (FractionRing R)[X] :=
    (Polynomial.mapRingHom (algebraMap R (FractionRing R))).toAlgebra
  -- (FractionRing R)[X] is a localization of R[X] at nzdMapC
  letI : IsLocalization (nzdMapC R) (FractionRing R)[X] :=
    Polynomial.isLocalization (nonZeroDivisors R) (FractionRing R)
  -- The localization at constPrimeSubmonoid is also a localization at nzdMapC
  letI : IsLocalization (nzdMapC R) (_root_.Localization S) :=
    isLocalization_nzdMapC_localization R
  -- Build the algebra equivalence between (FractionRing R)[X] and Localization S
  let e := IsLocalization.algEquiv (nzdMapC R)
    (Polynomial (FractionRing R)) (_root_.Localization S)
  -- (FractionRing R)[X] is a UFD: FractionRing R is a field, hence a UFD
  haveI : UniqueFactorizationMonoid (FractionRing R)[X] := inferInstance
  -- Transfer UFD across the algebra equivalence
  have hUFDLoc : UniqueFactorizationMonoid (_root_.Localization S) :=
    MulEquiv.uniqueFactorizationMonoid e.toMulEquiv inferInstance
  exact nagata_theorem (R := R[X]) S hS hUFDLoc
end NagataFactoriality
