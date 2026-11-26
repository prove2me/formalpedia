-- Prove2me | solution 1 for NagataFactoriality.polynomial_toLaurent_prime_of_not_dvd_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:01:52.781079+00:00
-- url     : https://prove2.me/submissions/850b6fff-66a2-4892-9eb2-3b881ff70a4f

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Definitions.Def_NagataFactoriality_Applications_Laurent
import Theorems.Thm_NagataFactoriality_IsLocalization_map_eq_zero_iff
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
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
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



set_option autoImplicit false
open NagataFactoriality
open scoped LaurentPolynomial
open Polynomial
namespace NagataFactoriality
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : Prime p) (hX : ¬ p ∣ X) : Prime (Polynomial.toLaurent p) := by
  let M : Submonoid R[X] := Submonoid.powers X
  have hspanPrime : (Ideal.span ({p} : Set R[X])).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hdisj : Disjoint (M : Set R[X]) ↑(Ideal.span ({p} : Set R[X])) := by
    rw [Set.disjoint_left]
    intro m hm hmspan
    rcases hm with ⟨n, rfl⟩
    have hmspan' : p ∣ X ^ n := by
      simpa [Ideal.mem_span_singleton] using hmspan
    exact hX (hp.dvd_of_dvd_pow hmspan')
  have hmapPrime : (Ideal.map (algebraMap R[X] R[T;T⁻¹]) (Ideal.span ({p} : Set R[X]))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M R[T;T⁻¹] _ hspanPrime hdisj
  have hspanMap : Ideal.map (algebraMap R[X] R[T;T⁻¹]) (Ideal.span ({p} : Set R[X])) =
      Ideal.span ({Polynomial.toLaurent p} : Set R[T;T⁻¹]) := by
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent, Set.image_singleton] using
      (Ideal.map_span (algebraMap R[X] R[T;T⁻¹]) ({p} : Set R[X]))
  rw [hspanMap] at hmapPrime
  exact (Ideal.span_singleton_prime (Polynomial.toLaurent_ne_zero.2 hp.ne_zero)).1 hmapPrime
end NagataFactoriality
