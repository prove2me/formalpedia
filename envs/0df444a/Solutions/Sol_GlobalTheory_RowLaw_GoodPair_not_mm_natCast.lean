-- Prove2me | solution 1 for GlobalTheory.RowLaw.GoodPair.not_mm_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:22:14.215258+00:00
-- url     : https://prove2.me/submissions/09c9b30f-7139-44e9-8de3-4eea9018e92b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusMemTypicalCurveSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodCurvesPairingMemMaxIdeal
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_mm_add
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_mm_mul
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_not_mm_one
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_mm_l
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_ge_intCast

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
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GoodPair
variable {C : Type} [Field C]
variable {V : VF C}
namespace GlobalTheory.RowLaw.GoodPair
theorem _root_.solution {k : ℕ} (h0 : 0 < k) (hk : k < V.l) : ¬ V.MM (k : C) := by
  intro h
  have hc : Nat.Coprime k V.l := (Nat.coprime_of_lt_prime h0.ne' hk V.l_prime).symm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have e : (k : C) * (a : C) + (V.l : C) * (b : C) = 1 := by
    have := congrArg (Int.cast : ℤ → C) hab
    push_cast at this
    rw [← this]; ring
  exact not_mm_one (e ▸ mm_add (mm_mul h (ge_intCast a)) (mm_mul mm_l (ge_intCast b)))
end GlobalTheory.RowLaw.GoodPair
