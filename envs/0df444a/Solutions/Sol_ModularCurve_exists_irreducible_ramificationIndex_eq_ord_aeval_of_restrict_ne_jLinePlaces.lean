-- Prove2me | solution 1 for ModularCurve.exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c5ebd8ec-b1d8-5444-a630-0a1a2eea9ae0

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField Polynomial

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial
attribute [local instance] ModularCurve.instDecidableEqRatFuncRat

namespace ModularCurve
p2m_export "ModularCurve" "jAdjoinAlgebra algebraMap_jGen_val jLineRingEquiv jLineRingEquiv_X instDecidableEqRatFuncRat jLinePlace1728 jLinePlaceZero jLinePlaceInfty jq modularFunctionField jq_mem jGen"
namespace JLineFiniteAux
p2m_open "ModularCurve"

theorem exists_eq_congr (v : Place ℚ ↥ℚ⟮ModularCurve.jq⟯) :
    ∃ v' : Place ℚ (RatFunc ℚ), v = Place.congrRingEquiv ModularCurve.jLineRingEquiv
      (RingHom.map_rat_algebraMap ModularCurve.jLineRingEquiv.toRingHom) v' :=
  ⟨(Place.congrEquiv ModularCurve.jLineRingEquiv
      (RingHom.map_rat_algebraMap ModularCurve.jLineRingEquiv.toRingHom)).symm v,
    ((Place.congrEquiv _ _).apply_symm_apply v).symm⟩

theorem equiv_algebraMap (p : ℚ[X]) :
    ModularCurve.jLineRingEquiv (algebraMap ℚ[X] (RatFunc ℚ) p)
      = Polynomial.aeval ModularCurve.jGen p := by
  have key : ModularCurve.jLineRingEquiv.toRingHom.comp (algebraMap ℚ[X] (RatFunc ℚ))
      = (Polynomial.aeval (R := ℚ) ModularCurve.jGen).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, RatFunc.algebraMap_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.aeval_C]
      exact RingHom.map_rat_algebraMap ModularCurve.jLineRingEquiv.toRingHom c
    · rw [RingHom.comp_apply, RatFunc.algebraMap_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.aeval_X]
      exact ModularCurve.jLineRingEquiv_X
  exact RingHom.congr_fun key p

end ModularCurve.JLineFiniteAux

open ModularCurve.JLineFiniteAux in
theorem solution (N : ℕ) [NeZero N] :
    letI := ModularCurve.jAdjoinAlgebra N
    ∀ [Algebra.IsIntegral ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N)]
      (w : AlgebraicCurve.Place ℚ ↥(ModularCurve.modularFunctionField N)),
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlace1728 →
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlaceZero →
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlaceInfty →
      ∃ p : Polynomial ℚ, Irreducible p ∧ p.Monic ∧ p.eval 0 ≠ 0 ∧ p.eval 1728 ≠ 0 ∧
        0 < w.ord (Polynomial.aeval (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) p) ∧
        (w.ramificationIndex ↥ℚ⟮ModularCurve.jq⟯ : ℤ) = w.ord (Polynomial.aeval (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) p) := by
  letI := ModularCurve.jAdjoinAlgebra N
  intro _ w h1728 h0 hinf
  obtain ⟨v', hv'⟩ := exists_eq_congr (w.restrict ↥ℚ⟮ModularCurve.jq⟯)

  have hinf' : v' ≠ placeInfty ℚ := by
    rintro rfl; exact hinf hv'
  have h0' : v' ≠ placeOfPoint ℚ 0 := by
    rintro rfl; exact h0 hv'
  have h1728' : v' ≠ placeOfPoint ℚ 1728 := by
    rintro rfl; exact h1728 hv'

  obtain ⟨P, rfl⟩ : ∃ P : IsDedekindDomain.HeightOneSpectrum ℚ[X], v' = Place.ofHeightOneSpectrum P := by
    rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v' with h | h
    · exact h
    · exact absurd h hinf'
  obtain ⟨g, hgirr, hPg⟩ := exists_irreducible_span ℚ P
  have hg0 : g ≠ 0 := hgirr.ne_zero
  set p : ℚ[X] := normalize g with hp
  have hpg : Associated g p := (associated_normalize g)
  have hpirr : Irreducible p := hpg.irreducible hgirr
  have hpmon : p.Monic := Polynomial.monic_normalize hg0
  have hp0 : p ≠ 0 := hpirr.ne_zero
  have hPp : P.asIdeal = Ideal.span {p} := by
    rw [hPg]; exact Ideal.span_singleton_eq_span_singleton.mpr hpg

  have hordv : (w.restrict ↥ℚ⟮ModularCurve.jq⟯).ord (Polynomial.aeval ModularCurve.jGen p) = 1 := by
    rw [hv', ← equiv_algebraMap, Place.ord_congrRingEquiv]
    exact ord_ofHeightOneSpectrum_of_span P hp0 hPp

  have hj : algebraMap ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N) ModularCurve.jGen
      = (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) :=
    Subtype.ext (ModularCurve.algebraMap_jGen_val N)
  have haeval : Polynomial.aeval (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) p
      = algebraMap ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N) (Polynomial.aeval ModularCurve.jGen p) := by
    rw [← hj, Polynomial.aeval_algebraMap_apply]
  have hordw : w.ord (Polynomial.aeval (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) p)
      = (w.ramificationIndex ↥ℚ⟮ModularCurve.jq⟯ : ℤ) := by
    rw [haeval, w.ord_restrict (F := ↥ℚ⟮ModularCurve.jq⟯), hordv, mul_one]
  have hepos : 0 < (w.ramificationIndex ↥ℚ⟮ModularCurve.jq⟯ : ℤ) := by
    exact_mod_cast w.ramificationIndex_pos (F := ↥ℚ⟮ModularCurve.jq⟯)

  have hroot : ∀ a : ℚ, Place.ofHeightOneSpectrum (K := ℚ) (F := RatFunc ℚ) P ≠ placeOfPoint ℚ a →
      p.eval a ≠ 0 := by
    intro a hne hpa
    apply hne
    have hdvd : (X - C a) ∣ p := dvd_iff_isRoot.mpr hpa
    have hass : Associated (X - C a) p := (irreducible_X_sub_C a).associated_of_dvd hpirr hdvd
    rw [placeOfPoint_eq_ofHeightOneSpectrum]
    congr 1
    ext1
    rw [hPp, heightOneSpectrumOfIrreducible_asIdeal]
    exact Ideal.span_singleton_eq_span_singleton.mpr hass.symm
  refine ⟨p, hpirr, hpmon, hroot 0 h0', hroot 1728 h1728', ?_, hordw.symm⟩
  rw [hordw]; exact hepos

end S_ModularCurve_exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces
end P2MW
export P2MW.S_ModularCurve_exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces (solution)
