-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ord_residue_fst_eq_zero_of_forall_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4cbcf6ae-9f06-5ed6-b901-5379311a515f

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residue_fst_eq_zero_of_forall_ne
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve Polynomial IsDedekindDomain
open scoped Polynomial

namespace Ws25
namespace Liii

theorem exists_eq_placeOfPoint (K : Type*) [Field K] [IsAlgClosed K] (w : HeightOneSpectrum K[X]) :
    ∃ a : K, Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w
      = RationalFunctionField.placeOfPoint K a := by
  obtain ⟨p, hp, hwp⟩ := RationalFunctionField.exists_irreducible_span K w
  have hdeg : p.degree ≠ 0 := by
    rw [IsAlgClosed.degree_eq_one_of_irreducible K hp]; exact one_ne_zero
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg
  refine ⟨a, ?_⟩
  have hassoc : Associated ((X : K[X]) - C a) p :=
    (irreducible_X_sub_C a).associated_of_dvd hp (dvd_iff_isRoot.mpr ha)
  have hideal : w = RationalFunctionField.heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a) :=
    HeightOneSpectrum.ext (by
      rw [hwp, RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal]
      exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm)
  rw [hideal, RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum]

theorem eq_charLGeomPlaceOfPoint_or_eq_infty (k : Type*) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (v : Place k (modularFunctionFieldC k 1)) :
    (∃ a : k, v = charLGeomPlaceOfPoint k a) ∨
      v = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  set v' : Place k (RatFunc k) := (charLGeomPlaceEquiv k).symm v with hv'def
  have hvv : v = charLGeomPlaceEquiv k v' := ((charLGeomPlaceEquiv k).apply_symm_apply v).symm
  by_cases h : v' = RationalFunctionField.placeInfty k
  · exact Or.inr (by rw [hvv, h])
  · left
    obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum k[X], v' = Place.ofHeightOneSpectrum w := by
      by_contra hne
      push Not at hne
      exact h ((RationalFunctionField.eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum v').mpr hne)
    obtain ⟨a, ha⟩ := exists_eq_placeOfPoint k w
    exact ⟨a, by rw [hvv, hw, ha]; try rfl⟩

end Ws25.Liii

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq (RatFunc k)] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (g : R.R₁.integers) (v : Place k (modularFunctionFieldC k 1))
    (hv : ∀ a : k, v ≠ charLGeomPlaceOfPoint k a)
    (hv' : v ≠ charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k)) :
    v.ord (R.residue₁ g) = 0 := by
  haveI : IsAlgClosed k := P.isAlgClosed
  rcases Ws25.Liii.eq_charLGeomPlaceOfPoint_or_eq_infty k v with ⟨a, ha⟩ | h
  · exact absurd ha (hv a)
  · exact absurd h hv'

end

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residue_fst_eq_zero_of_forall_ne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residue_fst_eq_zero_of_forall_ne (solution)
