-- Prove2me | solution 1 for GlobalTheory.RowVal.logInt_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:19:33.415625+00:00
-- url     : https://prove2.me/submissions/2efc25c5-4384-4f63-bbd8-34770b2cdb20

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CocycleIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Theorems.Thm_GlobalTheory_RowVal_cc_subst
import Theorems.Thm_GlobalTheory_RowVal_subst_mvExp
import Theorems.Thm_GlobalTheory_RowVal_intS_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.GaugeCocycle ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
open GlobalTheory GlobalTheory.RowVal
open MvPowerSeries
variable {C : Type} [Field C]
namespace GlobalTheory.RowVal
theorem _root_.solution [CharZero C] {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hi : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C}
    (hF : F ∈ logInt V σ) : subst a F ∈ logInt V τ :=
  ⟨by rw [cc_subst ha, hF.1], by rw [← subst_mvExp ha hF.1]; exact intS_subst ha hi hF.2⟩
end GlobalTheory.RowVal
