-- Prove2me | solution 1 for ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/2feda3a4-a0ba-54bf-a8a9-1ede6beb3b4c

import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos.ModularCurve"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.mem_iff_adicValuation_le_one Place.ord_ofHeightOneSpectrum_ne_zero_iff Place.ord_congrRingEquiv Place Place.ord"
namespace Place
p2m_export "AlgebraicCurve.Place" "mem_iff_adicValuation_le_one ord_ofHeightOneSpectrum_ne_zero_iff ord_congrRingEquiv ext adicValuation adicValuation_ne_zero ord toValuationSubring"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_pos' {f : F} (h : 0 < v.ord f) : f ∈ v.toValuationSubring := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h
  have hne := v.adicValuation_ne_zero hf
  rw [Place.mem_iff_adicValuation_le_one]
  have hlog : WithZero.log (v.adicValuation f) < 0 := by
    simp only [Place.ord] at h
    omega
  have hlt := (WithZero.log_lt_iff_lt_exp hne).mp hlog
  rw [WithZero.exp_zero] at hlt
  exact hlt.le

p2m_export "AlgebraicCurve.Place" "mem_of_ord_pos'"
end AlgebraicCurve.Place

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.mem_iff_adicValuation_le_one Place.ord_ofHeightOneSpectrum_ne_zero_iff Place.ord_congrRingEquiv Place Place.ord"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "heightOneSpectrumOfIrreducible heightOneSpectrumOfIrreducible_asIdeal placeOfPoint placeOfPoint_eq_ofHeightOneSpectrum placeInfty placeInfty_toValuationSubring eq_ofHeightOneSpectrum_or_eq_placeInfty"
p2m_open "AlgebraicCurve.RationalFunctionField AlgebraicCurve"

open Polynomial

variable (K : Type*) [Field K]

private theorem algebraMap_X_sub_C (c : K) :
    algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C c)
      = RatFunc.X - algebraMap K (RatFunc K) c := by
  rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

private theorem eq_placeOfPoint_of_ord_X_sub_pos [DecidableEq (RatFunc K)]
    (v : Place K (RatFunc K)) (c : K) (h : 0 < v.ord (RatFunc.X - algebraMap K (RatFunc K) c)) :
    v = placeOfPoint K c := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · have hq : (Polynomial.X - Polynomial.C c : K[X]) ≠ 0 := X_sub_C_ne_zero c
    have hmem : (Polynomial.X - Polynomial.C c : K[X]) ∈ w.asIdeal := by
      rw [← Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hq,
        algebraMap_X_sub_C]
      exact h.ne'
    have hw : heightOneSpectrumOfIrreducible K (irreducible_X_sub_C c) = w := by
      refine IsDedekindDomain.HeightOneSpectrum.ext ?_
      rw [heightOneSpectrumOfIrreducible_asIdeal]
      exact (PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C c)).eq_of_le
        w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    rw [placeOfPoint_eq_ofHeightOneSpectrum, hw]
  · exfalso
    have hne : algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C c) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (X_sub_C_ne_zero c)
    have hmem := (placeInfty K).mem_of_ord_pos' h
    rw [← algebraMap_X_sub_C, placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
      RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero _ hne,
      RatFunc.intDegree_polynomial, natDegree_X_sub_C, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at hmem
    norm_num at hmem

end AlgebraicCurve.RationalFunctionField

namespace ModularCurve
p2m_export "ModularCurve" "ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint jqModC modularFunctionFieldC jqModC_mem transcendental_jqModC"
p2m_open "ModularCurve"

variable (k : Type*) [Field k]

private theorem ratFuncEquivCharLOneC_X :
    ratFuncEquivCharLOneC k RatFunc.X = ⟨jqModC k, jqModC_mem k 1⟩ := by
  apply Subtype.ext
  simp only [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (f := jqModC k) (h := transcendental_jqModC k)

private theorem ord_charLGeomPlaceEquiv (v₀ : Place k (RatFunc k)) (f : RatFunc k) :
    (charLGeomPlaceEquiv k v₀).ord (ratFuncEquivCharLOneC k f) = v₀.ord f :=
  Place.ord_congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC k).commutes a) v₀ f

end ModularCurve

end

theorem solution
    {k : Type*} [Field k] {v : Place k ↥(modularFunctionFieldC k 1)} {c : k}
    (h : 0 < v.ord ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)
      - algebraMap k (modularFunctionFieldC k 1) c)) :
    v = charLGeomPlaceOfPoint k c := by
  classical
  obtain ⟨v₀, rfl⟩ := (charLGeomPlaceEquiv k).surjective v
  have key : ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)
        - algebraMap k (modularFunctionFieldC k 1) c)
      = ratFuncEquivCharLOneC k (RatFunc.X - algebraMap k (RatFunc k) c) := by
    rw [map_sub, ModularCurve.ratFuncEquivCharLOneC_X, AlgEquiv.commutes]
  rw [key, ModularCurve.ord_charLGeomPlaceEquiv] at h
  rw [RationalFunctionField.eq_placeOfPoint_of_ord_X_sub_pos k v₀ c h]
  rfl

end S_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
end P2MW
export P2MW.S_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos (solution)
