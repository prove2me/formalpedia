-- Prove2me | solution 1 for ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_eq_order
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ca629d39-b82c-566c-aea5-24ed207f897a

import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open AlgebraicCurve ModularCurve Polynomial

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace CuspD2

variable (k : Type*) [Field k]

theorem orderTop_eq_coe_order {Γ R : Type*} [PartialOrder Γ] [Zero R] [Zero Γ] {x : HahnSeries Γ R} (hx : x ≠ 0) :
    x.orderTop = (x.order : WithTop Γ) := by
  rw [HahnSeries.order_of_ne hx, HahnSeries.orderTop_of_ne_zero hx]

theorem coeff_jqModC_neg_one : (jqModC k).coeff (-1) = 1 := by
  rw [jqModC, HahnSeries.coeff_single_mul, sub_neg_eq_add, show (-1 : ℤ) + 1 = ((0 : ℕ) : ℤ) by norm_num,
    HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one, one_mul]

theorem coeff_jqModC_of_lt {m : ℤ} (hm : m < -1) : (jqModC k).coeff m = 0 := by
  rw [jqModC, HahnSeries.coeff_single_mul, sub_neg_eq_add, ofPowerSeries_coeff_of_neg _ (by omega), mul_zero]

theorem jqModC_ne_zero' : jqModC k ≠ 0 := by
  intro h
  have := coeff_jqModC_neg_one k
  rw [h, HahnSeries.coeff_zero] at this
  exact zero_ne_one this

theorem order_jqModC : (jqModC k).order = -1 := by
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by rw [coeff_jqModC_neg_one]; exact one_ne_zero)
  · by_contra hlt
    push Not at hlt
    have h := mt HahnSeries.coeff_order_eq_zero.mp (jqModC_ne_zero' k)
    rw [coeff_jqModC_of_lt k hlt] at h
    exact h rfl

theorem aeval_jqModC_ne_zero_and_order (p : k[X]) (hp : p ≠ 0) :
    Polynomial.aeval (jqModC k) p ≠ 0 ∧ (Polynomial.aeval (jqModC k) p).order = -(p.natDegree : ℤ) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n IH =>

  set J := jqModC k with hJ
  have hJ0 : J ≠ 0 := jqModC_ne_zero' k
  have hlead : Polynomial.aeval J (C p.leadingCoeff * X ^ p.natDegree) = algebraMap k _ p.leadingCoeff * J ^ p.natDegree := by
    rw [map_mul, map_pow, aeval_C, aeval_X]
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hltop : (Polynomial.aeval J (C p.leadingCoeff * X ^ p.natDegree)).orderTop = ((-(p.natDegree : ℤ) : ℤ) : WithTop ℤ) := by
    rw [hlead]
    have hC : algebraMap k (LaurentSeries k) p.leadingCoeff = HahnSeries.C p.leadingCoeff := by
      rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
    rw [hC]
    have hC0 : (HahnSeries.C p.leadingCoeff : LaurentSeries k) ≠ 0 := HahnSeries.C_ne_zero hlc
    have hne : HahnSeries.C p.leadingCoeff * J ^ p.natDegree ≠ 0 := mul_ne_zero hC0 (pow_ne_zero _ hJ0)
    rw [orderTop_eq_coe_order hne, HahnSeries.order_mul hC0 (pow_ne_zero _ hJ0), HahnSeries.order_C,
      HahnSeries.order_pow, order_jqModC, zero_add, smul_neg, nsmul_eq_mul, mul_one]
  by_cases he : p.eraseLead = 0
  · have hp' : p = C p.leadingCoeff * X ^ p.natDegree := by
      conv_lhs => rw [← p.eraseLead_add_C_mul_X_pow, he, zero_add]
    rw [hp']
    have hne : Polynomial.aeval J (C p.leadingCoeff * X ^ p.natDegree) ≠ 0 := by
      intro h0; rw [h0, HahnSeries.orderTop_zero] at hltop; exact WithTop.top_ne_coe hltop
    refine ⟨hne, ?_⟩
    have := hltop
    rw [orderTop_eq_coe_order hne, WithTop.coe_eq_coe] at this
    rw [this, hn]
  · have hlt : p.eraseLead.natDegree < n := by
      rw [← hn]
      rcases p.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h | h
      · exact h
      · exact absurd h he
    obtain ⟨hne', hord'⟩ := IH _ hlt p.eraseLead he rfl
    have hsum : Polynomial.aeval J p = Polynomial.aeval J p.eraseLead + Polynomial.aeval J (C p.leadingCoeff * X ^ p.natDegree) := by
      conv_lhs => rw [← p.eraseLead_add_C_mul_X_pow]
      rw [map_add]
    have hcmp : (Polynomial.aeval J (C p.leadingCoeff * X ^ p.natDegree)).orderTop < (Polynomial.aeval J p.eraseLead).orderTop := by
      rw [hltop, orderTop_eq_coe_order hne', hord', WithTop.coe_lt_coe]
      have : p.eraseLead.natDegree < p.natDegree := by rw [hn]; exact hlt
      omega
    have htop : (Polynomial.aeval J p).orderTop = ((-(p.natDegree : ℤ) : ℤ) : WithTop ℤ) := by
      rw [hsum, HahnSeries.orderTop_add_eq_right hcmp, hltop]
    have hne : Polynomial.aeval J p ≠ 0 := by
      intro h0; rw [h0, HahnSeries.orderTop_zero] at htop; exact WithTop.top_ne_coe htop
    refine ⟨hne, ?_⟩
    rw [orderTop_eq_coe_order hne, WithTop.coe_eq_coe] at htop
    rw [htop, hn]

theorem coe_ratFuncEquivCharLOneC (u : RatFunc k) :
    ((ratFuncEquivCharLOneC k u : modularFunctionFieldC k 1) : LaurentSeries k) =
      Polynomial.aeval (jqModC k) u.num / Polynomial.aeval (jqModC k) u.denom := by
  rw [← RatFunc.algEquivOfTranscendental_apply (jqModC k) (transcendental_jqModC k) u]
  rfl

theorem ord_charLGeomPlaceEquiv (v₀ : Place k (RatFunc k)) (f : RatFunc k) :
    (charLGeomPlaceEquiv k v₀).ord (ratFuncEquivCharLOneC k f) = v₀.ord f :=
  Place.ord_congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC k).commutes a) v₀ f

theorem ord_placeInfty_eq_order [DecidableEq (RatFunc k)] (g : modularFunctionFieldC k 1) :
    (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord g = ((g : LaurentSeries k)).order := by
  obtain ⟨u, rfl⟩ := (ratFuncEquivCharLOneC k).surjective g
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  rw [ord_charLGeomPlaceEquiv, RationalFunctionField.ord_placeInfty hu, coe_ratFuncEquivCharLOneC]
  obtain ⟨hn0, hn⟩ := aeval_jqModC_ne_zero_and_order k u.num (RatFunc.num_ne_zero hu)
  obtain ⟨hd0, hd⟩ := aeval_jqModC_ne_zero_and_order k u.denom (RatFunc.denom_ne_zero u)
  have hq0 : Polynomial.aeval (jqModC k) u.num / Polynomial.aeval (jqModC k) u.denom ≠ 0 := div_ne_zero hn0 hd0
  have hmul := HahnSeries.order_mul hq0 hd0
  rw [div_mul_cancel₀ _ hd0] at hmul
  rw [RatFunc.intDegree, neg_sub]
  linarith

end CuspD2

theorem solution (k : Type*) [Field k] [DecidableEq (RatFunc k)]
    (g : ↥(modularFunctionFieldC k 1)) :
    (charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k)).ord g
      = (g : LaurentSeries k).order :=
  CuspD2.ord_placeInfty_eq_order k g

end
end S_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
end P2MW
export P2MW.S_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order (solution)
