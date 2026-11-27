-- Prove2me | solution 1 for GlobalTheory.RowLaw.AddCurve.subst_eq_zero_of_van
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:24:24.451133+00:00
-- url     : https://prove2.me/submissions/d2888d83-f2cf-475e-9a51-b7861f288990

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
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
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.AddCurve
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.AddCurve
theorem _root_.solution {σ τ : Type} [Finite σ] {T : Set σ} {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (haT : ∀ s ∈ T, a s = 0) {f : MvPowerSeries σ C} (hf : Van T f) :
    subst a f = 0 := by
  have h : Van (∅ : Set τ) (subst a f) :=
    Van.subst T ha0 (fun s hs ν _ => by rw [haT s hs, map_zero]) hf
  ext ν
  rw [h ν (fun _ _ => Set.notMem_empty _), map_zero]
end GlobalTheory.RowLaw.AddCurve
