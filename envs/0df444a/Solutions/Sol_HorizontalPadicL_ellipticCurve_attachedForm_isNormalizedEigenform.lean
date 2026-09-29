-- Prove2me | solution 1 for HorizontalPadicL.ellipticCurve_attachedForm_isNormalizedEigenform
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-18T08:58:36.837582+00:00
-- url     : https://prove2.me/submissions/52f22168-7e7f-43df-a87f-2632021b6e7b

import Definitions.Def_KN_HorizontalPadicL
import Definitions.Def_FLTPrelim_Modularity
import Mathlib.FieldTheory.Cardinality
import Theorems.Thm_HorizontalPadicL_ellipticCurve_minimalModularLevel_iff_localEulerFactorDegree_lt_two

set_option autoImplicit false

open HorizontalPadicL

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E) :
    CuspForm.IsNormalizedEigenform (modularFormAtConductor E hmod).form := by
  let P := modularFormAtConductor E hmod
  have hmult : ArithmeticFunction.IsMultiplicative E.LFunction := by
    apply ArithmeticFunction.isMultiplicative_eulerProduct
    intro p
    let κ := IsLocalRing.ResidueField (p.adicCompletionIntegers ℚ)
    let q := Nat.card κ
    by_cases hq : 1 < q
    · apply ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow
      · haveI : Finite κ := (Nat.card_pos_iff.mp (by omega)).2
        letI : Fintype κ := Fintype.ofFinite κ
        simpa [q, κ, Nat.card_eq_fintype_card] using
          (Fintype.isPrimePow_card_of_field (α := κ))
      · simp [WeierstrassCurve.localPowerSeries]
    · rw [WeierstrassCurve.localEulerFactor]
      simp [ArithmeticFunction.ofPowerSeries, q, κ, hq,
        WeierstrassCurve.localPowerSeries]
  refine {
    qCoeff_one := ?_
    qCoeff_mul_of_coprime := ?_
    qCoeff_prime_pow_of_not_dvd := ?_
    qCoeff_prime_pow_of_dvd := ?_ }
  · rw [ModularFormClass.qCoeff, ← P.coeff_eq]
    exact_mod_cast hmult.map_one
  · intro m n hmn
    rw [ModularFormClass.qCoeff, ← P.coeff_eq,
      ModularFormClass.qCoeff, ← P.coeff_eq,
      ModularFormClass.qCoeff, ← P.coeff_eq]
    exact_mod_cast hmult.map_mul_of_coprime hmn
  · intro p r hp hpN
    have hrec :=
      (ellipticCurve_minimalModularLevel_iff_localEulerFactorDegree_lt_two
        E hmod p hp).2.mp hpN r
    rw [ModularFormClass.qCoeff, ← P.coeff_eq,
      ModularFormClass.qCoeff, ← P.coeff_eq,
      ModularFormClass.qCoeff, ← P.coeff_eq,
      ModularFormClass.qCoeff, ← P.coeff_eq]
    exact_mod_cast hrec
  · intro p r hp hpN
    have hrec :=
      (ellipticCurve_minimalModularLevel_iff_localEulerFactorDegree_lt_two
        E hmod p hp).1.mp hpN r
    rw [ModularFormClass.qCoeff, ← P.coeff_eq,
      ModularFormClass.qCoeff, ← P.coeff_eq,
      ModularFormClass.qCoeff, ← P.coeff_eq]
    exact_mod_cast hrec
