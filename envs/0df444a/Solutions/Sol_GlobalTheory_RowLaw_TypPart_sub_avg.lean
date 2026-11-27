-- Prove2me | solution 1 for GlobalTheory.RowLaw.TypPart.sub_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:25:48.370727+00:00
-- url     : https://prove2.me/submissions/a45cf470-d6a5-4e26-a182-33d1f5e1e049

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CurveLogarithmsInvNatCastSmulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowExponentPartMemGaugedCurveLogarithms
import Theorems.Thm_GlobalTheory_RowLaw_TypPart_sum_pow_root
import Theorems.Thm_GlobalTheory_RowLaw_TypPart_coeff_filt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.TypPart
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.TypPart
theorem _root_.solution [CharZero C] {ζ : C} {p : ℕ} (hp : 0 < p) (hζ : IsPrimitiveRoot ζ p) (f : PowerSeries C) :
    f + -((p : C)⁻¹ • ∑ j ∈ Finset.range p, PowerSeries.rescale (ζ ^ j) f) = filt (fun m => ¬ p ∣ m) f := by
  ext m
  have hp' : (p : C) ≠ 0 := by exact_mod_cast hp.ne'
  rw [coeff_filt, map_add, map_neg, PowerSeries.coeff_smul, map_sum]
  simp_rw [PowerSeries.coeff_rescale]
  rw [← Finset.sum_mul, sum_pow_root hζ]
  by_cases h : p ∣ m
  · simp [h, hp']
  · simp [h]
end GlobalTheory.RowLaw.TypPart
