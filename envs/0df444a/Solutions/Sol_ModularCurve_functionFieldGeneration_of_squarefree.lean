-- Prove2me | solution 1 for ModularCurve.functionFieldGeneration_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/42bcbf2e-1dcb-55d8-8c93-45f2c31520f7

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_of_squarefree
import Theorems.Thm_ModularCurve_relfinrank_full_of_squarefree
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionField
import Theorems.Thm_ModularCurve_functionFieldGeneration_iff_full_eq
import Theorems.Thm_ModularCurve_dedekindPsi_of_squarefree
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_functionFieldGeneration_of_squarefree
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_functionFieldGeneration_of_squarefree.ModularCurve ModularCurve.PhiGen"
open scoped IntermediateField

namespace ModularCurve p2m_export "ModularCurve" "jq jqN dedekindPsi ModularPolynomialData FunctionFieldGeneration modularFunctionField adjoin_jq_le algebraMap_comp_evalAtJGen ModularPolynomialData.toAdjoin modularFunctionFieldFull modularFunctionField_le_full PhiIrreducible finrank_adjoin_jqN_eq_of_squarefree relfinrank_full_of_squarefree relfinrank_modularFunctionField functionFieldGeneration_iff_full_eq dedekindPsi_of_squarefree" end ModularCurve
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.functionFieldGeneration_of_squarefree (N : ℕ) [NeZero N] (hN : Squarefree N) : FunctionFieldGeneration N := by
  rw [functionFieldGeneration_iff_full_eq]
  refine le_antisymm ?_ (modularFunctionField_le_full N)
  have hψ : 0 < dedekindPsi N := by
    rw [dedekindPsi_of_squarefree hN]; exact Finset.prod_pos fun p _ => Nat.succ_pos p
  have h1 : IntermediateField.relfinrank ℚ⟮jq⟯ (modularFunctionField N) = dedekindPsi N := by
    rw [relfinrank_modularFunctionField, finrank_adjoin_jqN_eq_of_squarefree N hN]
  have hmul := IntermediateField.relfinrank_mul_relfinrank (adjoin_jq_le N) (modularFunctionField_le_full N)
  rw [h1, relfinrank_full_of_squarefree N hN] at hmul
  have hone : IntermediateField.relfinrank (modularFunctionField N) (modularFunctionFieldFull N) = 1 :=
    (Nat.eq_of_mul_eq_mul_left hψ (hmul.trans (Nat.mul_one _).symm))
  exact IntermediateField.relfinrank_eq_one_iff.mp hone

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.phiIrreducible_of_squarefree (N : ℕ) [NeZero N] (hN : Squarefree N) (data : ModularPolynomialData N) : PhiIrreducible data := by
  have hroot : Polynomial.aeval (jqN N) data.toAdjoin = 0 := by
    rw [ModularPolynomialData.toAdjoin, Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen]
    exact data.eval_eq_zero
  have hint : IsIntegral ℚ⟮jq⟯ (jqN N) := ⟨_, data.toAdjoin_monic, by rwa [Polynomial.aeval_def] at hroot⟩
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN N)).natDegree = dedekindPsi N := by
    rw [← IntermediateField.adjoin.finrank hint]; exact finrank_adjoin_jqN_eq_of_squarefree N hN
  have heq : data.toAdjoin = minpoly ℚ⟮jq⟯ (jqN N) := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) data.toAdjoin_monic
      (minpoly.dvd _ _ hroot) ?_
    rw [hdeg, ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]
  rw [PhiIrreducible, heq]
  exact minpoly.irreducible hint

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_functionFieldGeneration_of_squarefree.ModularCurve in

theorem solution (N : ℕ) [NeZero N] (hN : Squarefree N) : FunctionFieldGeneration N :=
  ModularCurve.functionFieldGeneration_of_squarefree N hN

#print axioms solution

end
end S_ModularCurve_functionFieldGeneration_of_squarefree
end P2MW
export P2MW.S_ModularCurve_functionFieldGeneration_of_squarefree (solution)
