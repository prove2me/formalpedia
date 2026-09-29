-- Prove2me | solution 1 for ModularCurve.exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/aee8f46a-8eef-59e4-8ff4-4c57dbdc9b07

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_arithFrobC_smul_charLGeomPlaceOfPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    ∃ W : Finset (Place k (modularFunctionFieldC k 1)),
      (∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) ∧
        nodePairsOfPlaces (arithFrobC q k 1) W = nodePairsOf q S₀ := by
  refine ⟨S₀.map ⟨charLGeomPlaceOfPoint k, charLGeomPlaceOfPoint_injective k⟩, ?_, ?_⟩
  · intro w
    rw [ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq, Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (hS₀ a).mp ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, (hS₀ a).mpr ha, rfl⟩
  · exact ModularCurve.nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf q (arithFrobC q k 1)
      (fun a => ModularCurve.arithFrobC_smul_charLGeomPlaceOfPoint q a) S₀

end S_ModularCurve_exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf
end P2MW
export P2MW.S_ModularCurve_exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf (solution)
