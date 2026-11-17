-- Prove2me | solution 1 for N25.Endgame.xHGoodPrime_eq_adjoin_units25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:08.790231+00:00
-- url     : https://prove2.me/submissions/85e436f8-9519-4839-80ca-43586ce57bcd

import Mathlib
import Theorems.Thm_N25_unitLaurentField25C_eq_modularField_iff
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_N25_Endgame_xHSpecial_eq_adjoin_units25
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_N25_Endgame_nonempty_redDatum25
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le
import Theorems.Thm_N25_Endgame_unitLaurentField25C_eq_modularField_of_extension

/-! Descent to the prime field and coefficient extension of generation by the modular units. -/
noncomputable section

namespace N25.Endgame

open N25 AlgebraicCurve

/-- The reduced unit divisors force generation over the prime field itself. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) :
    IntermediateField.adjoin (ZMod p)
      ({U25C (ZMod p) 0, U25C (ZMod p) 0 / U25C (ZMod p) 1} :
        Set (FBase (ZMod p))) = ⊤ := by
  have hgood : ¬ p ∣ 25 := by
    rcases hp with rfl | rfl <;> norm_num
  obtain ⟨R⟩ := nonempty_redDatum25 hgood
  let : Algebra (ZMod p) (κ R.A) := ZMod.algebra _ _
  have hspecial : unitLaurentField25C (κ R.A) =
      ModularCurve.qExpFunctionFieldC (κ R.A) Γ25 :=
    (unitLaurentField25C_eq_modularField_iff (κ R.A)).mpr
      (xHSpecial_eq_adjoin_units25 hp R)
  exact (unitLaurentField25C_eq_modularField_iff (ZMod p)).mp
    (unitLaurentField25C_eq_modularField_of_extension (ZMod p) (κ R.A) hspecial)

end N25.Endgame
