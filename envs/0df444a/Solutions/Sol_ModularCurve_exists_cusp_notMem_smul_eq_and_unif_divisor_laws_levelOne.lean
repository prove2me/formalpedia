-- Prove2me | solution 1 for ModularCurve.exists_cusp_notMem_smul_eq_and_unif_divisor_laws_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0f7bc73f-d70b-56db-bea8-4967aaf71bb2

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_SpecializeModuli
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_arithFrobC_smul_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_smul_charLGeomPlaceEquiv_placeInfty_of_smul_jqModC
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldC_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_cusp_notMem_smul_eq_and_unif_divisor_laws_levelOne
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open AlgebraicCurve ModularCurve
open AlgebraicCurve.RationalFunctionField

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) :
    ∃ (cusp : Place k (modularFunctionFieldC k 1)) (unifFst unifSnd : Place k (modularFunctionFieldC k 1) → ↥(modularFunctionFieldC k 1)),
      cusp ∉ W ∧ arithFrobC q k 1 • cusp = cusp ∧
      (∀ w ∈ W,
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single w (1 : ℤ) - Finsupp.single cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (unifFst w)) ∧
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single (arithFrobC q k 1 • w) (1 : ℤ) - Finsupp.single cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (unifSnd w))) := by
  classical

  set jt : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩ with hjt
  set cusp : Place k ↥(modularFunctionFieldC k 1) := charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) with hcusp

  have hWpt : ∀ w ∈ W, ∃ a : k, charLGeomPlaceOfPoint k a = w := by
    intro w hw
    obtain ⟨a, -, ha⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k w).mp ((hW w).mp hw)
    exact ⟨a, ha⟩
  choose! av hav using hWpt

  have hordpt : ∀ a c : k, (charLGeomPlaceOfPoint k a).ord (jt - algebraMap k _ c) = if c = a then 1 else 0 :=
    fun a c => ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a c
  have hordcusp : ∀ c : k, cusp.ord (jt - algebraMap k _ c) = -1 := by
    intro c
    rw [hcusp, ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_eq_order]
    have hcoe : ((jt - algebraMap k ↥(modularFunctionFieldC k 1) c : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
        = jqModC k - HahnSeries.C c := by
      rw [hjt]
      push_cast
      rw [show (algebraMap k (LaurentSeries k)) c = HahnSeries.C c from by
        rw [ModularCurve.algebraMap_laurentSeries_apply_eq_single, HahnSeries.C_apply]]
    rw [hcoe]
    have h1 : (jqModC k - HahnSeries.C c).coeff (-1) = 1 := by
      rw [HahnSeries.coeff_sub, ModularCurve.coeff_jqModC_neg_one, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by norm_num),
        sub_zero]
    have hne : jqModC k - HahnSeries.C c ≠ 0 := by
      intro h; rw [h, HahnSeries.coeff_zero] at h1; exact zero_ne_one h1
    apply le_antisymm
    · exact HahnSeries.order_le_of_coeff_ne_zero (by rw [h1]; exact one_ne_zero)
    · have h2 := HahnSeries.min_order_le_order_add (x := jqModC k) (y := -HahnSeries.C c) (by rwa [← sub_eq_add_neg])
      rw [← sub_eq_add_neg, HahnSeries.order_neg, ModularCurve.order_jqModC_def, HahnSeries.order_C] at h2
      simpa using h2

  have hpt_ne_cusp : ∀ a : k, charLGeomPlaceOfPoint k a ≠ cusp := by
    intro a h
    have h1 := hordpt a a
    rw [if_pos rfl, h, hordcusp] at h1
    norm_num at h1

  have hdich : ∀ v : Place k ↥(modularFunctionFieldC k 1), v = cusp ∨ ∃ c : k, v = charLGeomPlaceOfPoint k c := by
    intro v
    rcases lt_or_ge (v.ord jt) 0 with hneg | hnn
    · exact Or.inl (ModularCurve.eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg hneg)
    · right
      have hjt0 : jt ≠ 0 := fun h => ModularCurve.jqModC_ne_zero_def k (congrArg Subtype.val h)
      have hmem : jt ∈ v.toValuationSubring := Place.mem_of_ord_nonneg v hjt0 hnn
      refine ⟨v.evalAt jt, ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos ?_⟩
      apply ModularCurve.ord_sub_evalAt_pos_of_isRational (ModularCurve.isRational_place_modularFunctionFieldC_one k v) hmem
      intro h0

      have := hordcusp (v.evalAt jt)
      rw [h0, Place.ord_zero] at this
      norm_num at this

  have hlaw : ∀ (a : k) (v : Place k ↥(modularFunctionFieldC k 1)),
      ((Finsupp.single (charLGeomPlaceOfPoint k a) (1 : ℤ) - Finsupp.single cusp 1 : Divisor k ↥(modularFunctionFieldC k 1)) v)
        = v.ord (jt - algebraMap k _ a) := by
    intro a v
    rcases hdich v with rfl | ⟨c, rfl⟩
    · rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (hpt_ne_cusp a), if_pos rfl, hordcusp]
      norm_num
    · rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (Ne.symm (hpt_ne_cusp c)), hordpt,
        (charLGeomPlaceOfPoint_injective k).eq_iff]
      by_cases hac : a = c
      · subst hac; simp
      · simp [hac]
  refine ⟨cusp, fun w => jt - algebraMap k _ (av w), fun w => jt - algebraMap k _ (av w ^ q), ?_, ?_, ?_⟩
  ·
    intro hc
    exact hpt_ne_cusp (av cusp) (hav cusp hc)
  ·
    exact ModularCurve.smul_charLGeomPlaceEquiv_placeInfty_of_smul_jqModC (arithFrobC q k 1) (ModularCurve.arithFrobC_smul_jq (q := q) (K := k) (N := 1))
  · intro w hw
    constructor
    · intro v
      have := hlaw (av w) v
      rwa [hav w hw] at this
    · intro v
      have := hlaw (av w ^ q) v
      rwa [← ModularCurve.arithFrobC_smul_charLGeomPlaceOfPoint q (av w), hav w hw] at this

end S_ModularCurve_exists_cusp_notMem_smul_eq_and_unif_divisor_laws_levelOne
end P2MW
export P2MW.S_ModularCurve_exists_cusp_notMem_smul_eq_and_unif_divisor_laws_levelOne (solution)
