-- Prove2me | solution 1 for NagataFactoriality.laurentPolynomial_uniqueFactorizationMonoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:55.726028+00:00
-- url     : https://prove2.me/submissions/83f23016-e629-42c4-988b-975d9f543441

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Definitions.Def_NagataFactoriality_Applications_Laurent
import Theorems.Thm_NagataFactoriality_polynomial_toLaurent_prime_of_not_dvd_X
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
import Theorems.Thm_NagataFactoriality_dvd_trans
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
    [UniqueFactorizationMonoid R] : UniqueFactorizationMonoid R[T;T⁻¹] := by
  letI : UniqueFactorizationMonoid R[X] := inferInstance
  rw [UniqueFactorizationMonoid.iff_exists_prime_factors]
  intro f hf
  obtain ⟨n, p, hpLaurent⟩ := LaurentPolynomial.exists_T_pow f
  have hp0 : p ≠ 0 := by
    intro hpz
    have hT0 : (LaurentPolynomial.T n : R[T;T⁻¹]) ≠ 0 := (LaurentPolynomial.isUnit_T n).ne_zero
    have : f * LaurentPolynomial.T n = 0 := by
      simpa [hpz] using hpLaurent.symm
    exact hf ((mul_eq_zero.mp this).resolve_right hT0)
  obtain ⟨q, hpq, hqX⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp0 0
  have hpq' : p = X ^ p.rootMultiplicity 0 * q := by
    simpa using hpq
  have hqX' : ¬ X ∣ q := by
    simpa using hqX
  have hq0 : q ≠ 0 := by
    intro hq0
    apply hp0
    rw [hpq', hq0, mul_zero]
  obtain ⟨w, hwprime, hwassoc⟩ := UniqueFactorizationMonoid.exists_prime_factors q hq0
  refine ⟨w.map Polynomial.toLaurent, ?_, ?_⟩
  · intro z hz
    rcases Multiset.mem_map.1 hz with ⟨r, hr, rfl⟩
    have hrdvdq : r ∣ q := hwassoc.dvd_iff_dvd_right.mp (Multiset.dvd_prod hr)
    have hrnot : ¬ r ∣ X := by
      intro hrX
      have hassoc : Associated r X :=
        (hwprime r hr).irreducible.associated_of_dvd Polynomial.irreducible_X hrX
      exact hqX' (dvd_trans hassoc.symm.dvd hrdvdq)
    exact polynomial_toLaurent_prime_of_not_dvd_X (hwprime r hr) hrnot
  · have hmapassoc : Associated (w.map Polynomial.toLaurent).prod (Polynomial.toLaurent q) := by
      rw [Multiset.prod_hom]
      exact hwassoc.map Polynomial.toLaurent
    have hfp : Associated f (Polynomial.toLaurent p) := by
      rw [hpLaurent]
      exact associated_mul_unit_right _ _ (LaurentPolynomial.isUnit_T n)
    have hpqAssoc : Associated (Polynomial.toLaurent p) (Polynomial.toLaurent q) := by
      rw [hpq', map_mul, Polynomial.toLaurent_X_pow]
      simpa [LaurentPolynomial.T_mul] using
        (associated_mul_unit_left (Polynomial.toLaurent q) (LaurentPolynomial.T (p.rootMultiplicity 0))
          (LaurentPolynomial.isUnit_T (p.rootMultiplicity 0)))
    exact hmapassoc.trans (hfp.trans hpqAssoc).symm
end NagataFactoriality
