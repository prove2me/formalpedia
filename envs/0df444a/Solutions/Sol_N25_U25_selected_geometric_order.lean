-- Prove2me | solution 1 for N25.U25_selected_geometric_order
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:58:07.415342+00:00
-- url     : https://prove2.me/submissions/ce645a84-fca5-4048-a1a7-01aa91debdfc

import Mathlib
import Theorems.Thm_N25_U25C_eq_mk
import Definitions.Def_N25_Units
import Theorems.Thm_N25_unitSeries25_mem
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_surjective_algebraMap_residueField_bar
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_diamondPlace_U25_ord
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_N25_unitSeries25_coeffEmb
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_N25_unitSeries25_order
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar

set_option autoImplicit false

open ModularCurve AlgebraicCurve

namespace N25

theorem _root_.solution (i j : Fin 5) :
    (N25.Endgame.pG25 j).ord (N25.Endgame.emb25 (U25 i)) = unitOrders25 i j := by
  let γ := SemilinearAut.ofAlgAut N25.Endgame.gammaF25
  let P := qInftyPlaceBar N25.Endgame.Qbar N25.Endgame.FG N25.Endgame.cuspChoice25.hG
  have hbase (k : Fin 5) : P.ord (N25.Endgame.emb25 (U25 k)) = unitQOrder25 k := by
    rw [show U25 k = ⟨unitSeries25 ℚ k, unitSeries25_mem ℚ k⟩ from U25C_eq_mk ℚ k, ord_qInftyPlaceBar]
    change (coeffEmb N25.Endgame.Qbar (unitSeries25 ℚ k)).order = unitQOrder25 k
    rw [unitSeries25_coeffEmb, unitSeries25_order]
  have hp (n : ℕ) (k : Fin 5) :
      (γ^n • P).ord (N25.Endgame.emb25 (U25 k)) = unitQOrder25 ⟨(k.val+n)%5, Nat.mod_lt _ (by decide)⟩ := by
    induction n generalizing k with
    | zero => simpa only [pow_zero, one_smul, add_zero, Nat.mod_eq_of_lt k.isLt] using hbase k
    | succ n ih =>
      rw [pow_succ', mul_smul]
      rw [diamondPlace_U25_ord]
      have heq : (⟨((k+1).val+n)%5, Nat.mod_lt _ (by decide)⟩ : Fin 5) =
          ⟨(k.val+(n+1))%5, Nat.mod_lt _ (by decide)⟩ := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one]
        omega
      simpa only [heq] using ih (k+1)
  have ht : unitQOrder25 (i+j) = unitOrders25 i j := by
    fin_cases i <;> fin_cases j <;> decide
  rw [← ht]
  exact hp j.val i

end N25
