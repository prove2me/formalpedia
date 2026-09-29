-- Prove2me | solution 1 for ModularCurve.exists_equiv_ssJSet_coe_eq_evalAt_jGeomGen_of_forall_mem_iff_mem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/db80f045-c5ab-5516-8e0b-c368877328dd

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SpecializeModuli
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_equiv_ssJSet_coe_eq_evalAt_jGeomGen_of_forall_mem_iff_mem_ssPlaces
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution
    (p : ℕ) (k : Type*) [Field k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 k) :
    ∃ τ : ↥W ≃ ↥(ssJSet p k),
      ∀ w : ↥W, ((τ w : k)) = (w : Place k (modularFunctionFieldC k 1)).evalAt (jGeomGen k 1) := by
  classical

  have hev : ∀ a ∈ ssJSet p k, (charLGeomPlaceOfPoint k a).evalAt (jGeomGen k 1) = a := by
    intro a ha
    have hss : charLGeomPlaceOfPoint k a ∈ ssPlaces p 1 k :=
      (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq p k _).mpr ⟨a, ha, rfl⟩
    have hc := (IsSupersingularPlace.isCentreOf_evalAt (q := p) (N := 1) (K := k) hss).1
    by_contra hne
    have h0 := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a
      ((charLGeomPlaceOfPoint k a).evalAt (jGeomGen k 1))
    rw [if_neg hne] at h0
    change 0 < (charLGeomPlaceOfPoint k a).ord
      ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - _) at hc
    rw [h0] at hc
    exact lt_irrefl _ hc
  have hmem : ∀ w : ↥W, (w : Place k (modularFunctionFieldC k 1)).evalAt (jGeomGen k 1) ∈ ssJSet p k :=
    fun w => ((hW _).mp w.2).2.2
  have hinv : ∀ a : ↥(ssJSet p k), charLGeomPlaceOfPoint k (a : k) ∈ W :=
    fun a => (hW _).mpr ((ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq p k _).mpr ⟨a, a.2, rfl⟩)
  refine ⟨{ toFun := fun w => ⟨_, hmem w⟩
            invFun := fun a => ⟨_, hinv a⟩
            left_inv := fun w => ?_
            right_inv := fun a => Subtype.ext (hev a a.2) }, fun w => rfl⟩
  apply Subtype.ext
  obtain ⟨a, ha, hwa⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq p k _).mp ((hW _).mp w.2)
  change charLGeomPlaceOfPoint k ((w : Place k (modularFunctionFieldC k 1)).evalAt (jGeomGen k 1)) = w
  rw [← hwa, hev a ha]

end S_ModularCurve_exists_equiv_ssJSet_coe_eq_evalAt_jGeomGen_of_forall_mem_iff_mem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_exists_equiv_ssJSet_coe_eq_evalAt_jGeomGen_of_forall_mem_iff_mem_ssPlaces (solution)
