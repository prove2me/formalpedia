-- Prove2me | solution 1 for ModularCurve.exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/3e65cedb-f536-5af0-a7b2-62b102f9d06e

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SpecializeModuli
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S : Finset k) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSet q k) :
    ∃ (W : Finset (Place k (modularFunctionFieldC k 1))) (τ : ↥S ≃ ↥W),
      (∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) ∧
        ∀ a : ↥S, (τ a : Place k (modularFunctionFieldC k 1)).evalAt (jGeomGen k 1) = (a : k) := by
  classical
  let f : k ↪ Place k (modularFunctionFieldC k 1) := ⟨charLGeomPlaceOfPoint k, charLGeomPlaceOfPoint_injective k⟩
  have hmem : ∀ w, w ∈ S.map f ↔ w ∈ ssPlaces q 1 k := by
    intro w
    rw [Finset.mem_map, mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k w]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, (hS a).mp ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, (hS a).mpr ha, h⟩⟩
  let g : ↥S → ↥(S.map f) := fun a => ⟨f a, Finset.mem_map_of_mem f a.2⟩
  have hg : Function.Bijective g := by
    refine ⟨fun a b h => Subtype.ext (f.injective (congrArg Subtype.val h)), fun w => ?_⟩
    obtain ⟨a, ha, haw⟩ := Finset.mem_map.mp w.2
    exact ⟨⟨a, ha⟩, Subtype.ext haw⟩
  refine ⟨S.map f, Equiv.ofBijective g hg, hmem, fun a => ?_⟩
  show (charLGeomPlaceOfPoint k (a : k)).evalAt (jGeomGen k 1) = (a : k)
  set w := charLGeomPlaceOfPoint k (a : k) with hw
  have hss : w ∈ ssPlaces q 1 k := (hmem w).mp (Finset.mem_map_of_mem f a.2)
  have hrat : w.IsRational := hss.1
  have haff : IsAffineGeomPlace k 1 w := hss.2.1
  have hc := exists_isCentreOf_of_isRational hrat haff
  have hw' : w = charLGeomPlaceOfPoint k (w.evalAt (jGeomGen k 1)) := eq_charLGeomPlaceOfPoint_of_ord_pos hc.1
  exact (charLGeomPlaceOfPoint_injective k (hw.symm.trans hw')).symm

end S_ModularCurve_exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq
end P2MW
export P2MW.S_ModularCurve_exists_finset_forall_mem_iff_mem_ssPlaces_equiv_evalAt_jGeomGen_eq (solution)
