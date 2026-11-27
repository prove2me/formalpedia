-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvEnd.dz_of_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:05:49.275517+00:00
-- url     : https://prove2.me/submissions/2ea3e5cc-8f96-4af6-861f-7706d8166a72

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_coeff_dz
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_weight_em

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd
open MvPowerSeries
variable {C : Type} [Field C]
variable {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw.CvEnd
theorem _root_.solution (i : κ) {F : MvPowerSeries (Fin 2 × κ) C} (hF : F ∈ ordGe C (wz κ) 2) : dz i F = 0 := by
  ext μ
  rw [coeff_dz, hF _ (by rw [weight_em]; omega), map_zero]
end GlobalTheory.RowLaw.CvEnd
