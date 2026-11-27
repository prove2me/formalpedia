-- Prove2me | solution 1 for GlobalTheory.RowLaw.FrobCurve.ge_zero_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:51:41.708835+00:00
-- url     : https://prove2.me/submissions/49fba3c2-4612-4984-b753-d7f6b0e591a1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemCvOfSubstXPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusMemTypicalCurveSet
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1


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
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.FrobCurve
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.FrobCurve
theorem _root_.solution (V : VF C) {ζ : C} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) : V.Ge 0 ζ := by
  have h1 : n • V.v ζ = 0 := by rw [← V.v.map_pow, h, V.v.map_one]
  unfold VF.Ge
  induction hv : V.v ζ using WithTop.recTopCoe with
  | top => exact le_top
  | coe r =>
    rw [hv, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, nsmul_eq_mul] at h1
    have : r = 0 := (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn.ne')
    rw [this]
end GlobalTheory.RowLaw.FrobCurve
