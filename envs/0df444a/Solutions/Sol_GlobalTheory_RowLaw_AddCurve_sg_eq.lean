-- Prove2me | solution 1 for GlobalTheory.RowLaw.AddCurve.sg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:35:43.356349+00:00
-- url     : https://prove2.me/submissions/a2740109-89a5-4625-a068-96b73f032b90

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw.AddCurve
theorem _root_.solution (X : RawChart C d I κ) (v : κ → C) :
    X.sg v = -∑ i, v i • killCompl (fstEmb κ) (pderiv C ((1 : Fin 2), i) X.h) := by
  ext μ
  rw [map_neg, map_sum]
  show -∑ i, v i * coeff
    (μ.mapDomain (fun x : κ => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), i) 1) X.h = _
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_smul, coeff_killCompl, coeff_pderiv, Finsupp.embDomain_notin_range, Finsupp.embDomain_eq_mapDomain]
  · rw [Nat.cast_zero, zero_add, mul_one]
    rfl
  · rintro ⟨x, hx⟩
    have : (0 : Fin 2) = 1 := (Prod.ext_iff.1 hx).1
    exact absurd this (by decide)
end GlobalTheory.RowLaw.AddCurve
