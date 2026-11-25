-- Prove2me | solution 1 for MvPolynomial.exists_algebraMap_eq_of_isIntegral_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:45:01.299501+00:00
-- url     : https://prove2.me/submissions/487eace3-32cb-4c29-a116-f749c2d4083c

import Mathlib

set_option autoImplicit false

universe u

/-!
# S4-EtPi1 (O10, Mv part): `Frac A` is algebraically closed in `Frac A[y_1, …, y_k]`

Extracted from the Ramanujan-Petersson library file `Def_RP_EtPi1_Hom` (section `Mv`); Mathlib only.
-/

open Polynomial

namespace RamanujanPetersson
namespace EtPi1Mv

/-- A polynomial over a domain that is integral over the coefficients is constant. -/
theorem natDegree_eq_zero_of_isIntegral {R : Type u} [CommRing R] [IsDomain R] {Q : R[X]} (hQ : IsIntegral R Q) :
    Q.natDegree = 0 := by
  obtain ⟨p, hpm, hp⟩ := hQ
  have h1 : p.comp Q = 0 := by
    rw [Polynomial.comp_eq_aeval, Polynomial.aeval_def]
    exact hp
  have h2 := Polynomial.natDegree_comp (p := p) (q := Q)
  rw [h1, Polynomial.natDegree_zero] at h2
  rcases Nat.mul_eq_zero.1 h2.symm with h | h
  · rw [hpm.natDegree_eq_zero] at h
    rw [h, Polynomial.one_comp] at h1
    exact absurd h1 one_ne_zero
  · exact h

/-- A domain `A` is integrally closed in `A[y_1, …, y_k]`. -/
theorem exists_algebraMap_eq_of_isIntegral_mv {A : Type u} [CommRing A] [IsDomain A] :
    ∀ (k : ℕ) (P : MvPolynomial (Fin k) A), IsIntegral A P →
      ∃ a : A, algebraMap A (MvPolynomial (Fin k) A) a = P
  | 0, P, _ => ⟨MvPolynomial.isEmptyAlgEquiv A (Fin 0) P, by
      rw [← (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.commutes, Algebra.algebraMap_self_apply,
        AlgEquiv.symm_apply_apply]⟩
  | k + 1, P, hP => by
      let e := MvPolynomial.finSuccEquiv A k
      have h1 : IsIntegral A (e P) := hP.map e
      have h2 : IsIntegral (MvPolynomial (Fin k) A) (e P) := h1.tower_top
      have hC : e P = Polynomial.C ((e P).coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isIntegral h2)
      have hr : IsIntegral A ((e P).coeff 0) := by
        refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (MvPolynomial (Fin k) A)
          (MvPolynomial (Fin k) A)[X]) ?_).1 ?_
        · rw [IsScalarTower.coe_toAlgHom', Polynomial.algebraMap_eq]
          exact Polynomial.C_injective
        · rw [IsScalarTower.coe_toAlgHom', Polynomial.algebraMap_eq, ← hC]
          exact h1
      obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_isIntegral_mv k _ hr
      refine ⟨a, e.injective ?_⟩
      rw [AlgEquiv.commutes, hC, ← ha, Polynomial.algebraMap_apply]

/-- `Frac A` is algebraically closed in `Frac A[y_1, …, y_k]` (geometric connectedness of `A^{m+k} → A^m`). -/
theorem algClosed_frac_mv {A K K' : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    {k : ℕ} [Field K'] [Algebra (MvPolynomial (Fin k) A) K'] [IsFractionRing (MvPolynomial (Fin k) A) K']
    [Algebra K K'] [Algebra A K'] [IsScalarTower A K K'] [IsScalarTower A (MvPolynomial (Fin k) A) K']
    [IsIntegrallyClosed (MvPolynomial (Fin k) A)] (y : K') (hy : IsIntegral K y) :
    ∃ x : K, algebraMap K K' x = y := by
  have halg : IsAlgebraic A y := (IsFractionRing.isAlgebraic_iff A K K').2 hy.isAlgebraic
  obtain ⟨c, hc, hz⟩ := halg.exists_integral_multiple
  have hz' : IsIntegral (MvPolynomial (Fin k) A) (c • y) := hz.tower_top
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.isIntegral_iff.1 hz'
  have hPi : IsIntegral A P := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (MvPolynomial (Fin k) A) K')
      (IsFractionRing.injective (MvPolynomial (Fin k) A) K')).1 ?_
    rw [IsScalarTower.coe_toAlgHom', hP]
    exact hz
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_isIntegral_mv k P hPi
  have hinj : Function.Injective (algebraMap A K') := by
    rw [IsScalarTower.algebraMap_eq A K K', RingHom.coe_comp]
    exact (algebraMap K K').injective.comp (IsFractionRing.injective A K)
  have hc' : algebraMap A K' c ≠ 0 := fun h => hc (hinj (h.trans (map_zero _).symm))
  refine ⟨algebraMap A K a / algebraMap A K c, ?_⟩
  rw [map_div₀, ← IsScalarTower.algebraMap_apply A K K', ← IsScalarTower.algebraMap_apply A K K',
    div_eq_iff hc', mul_comm, ← Algebra.smul_def c y, ← hP, ← ha,
    ← IsScalarTower.algebraMap_apply A (MvPolynomial (Fin k) A) K']

end EtPi1Mv
end RamanujanPetersson

theorem solution
    (A K K' : Type u) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (k : ℕ) [Field K'] [Algebra (MvPolynomial (Fin k) A) K'] [IsFractionRing (MvPolynomial (Fin k) A) K']
    [Algebra K K'] [Algebra A K'] [IsScalarTower A K K'] [IsScalarTower A (MvPolynomial (Fin k) A) K']
    [IsIntegrallyClosed (MvPolynomial (Fin k) A)] (y : K') (hy : IsIntegral K y) :
    ∃ x : K, algebraMap K K' x = y := by
  exact RamanujanPetersson.EtPi1Mv.algClosed_frac_mv (A := A) (K := K) (k := k) y hy
