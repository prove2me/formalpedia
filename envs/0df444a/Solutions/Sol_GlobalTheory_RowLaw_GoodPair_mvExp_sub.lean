-- Prove2me | solution 1 for GlobalTheory.RowLaw.GoodPair.mvExp_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:12:15.246745+00:00
-- url     : https://prove2.me/submissions/314b3a01-5ae7-440c-87ee-701fa32b1437

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
import Theorems.Thm_P2M_GlobalTheory_RowLaw_GoodPair_ordGe_pow__6169f95a7950
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
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
noncomputable section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GoodPair
variable {C : Type} [Field C]
variable {τ : Type} {V : VF C}
namespace GlobalTheory.RowLaw.GoodPair
theorem _root_.solution {w : τ → ℕ} {m : ℕ} {f : MvPowerSeries τ C} (h0 : constantCoeff f = 0) (hf : f ∈ ordGe C w m) :
    mvExp f - 1 - f ∈ ordGe C w (2 * m) := by
  classical
  intro e he
  rw [map_sub, map_sub]
  show (∑ k ∈ Finset.range (e.degree + 1), coeff e (f ^ k) / (k.factorial : C)) - _ - _ = 0
  by_cases hne : e = 0
  · subst hne
    simp [h0]
  · have hd : e.degree ≠ 0 := fun h => hne ((Finsupp.degree_eq_zero_iff e).1 h)
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hd
    rw [hn, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp
    · intro k _
      rw [ordGe_pow' hf (k + 1 + 1) e (lt_of_lt_of_le he (Nat.mul_le_mul_right _ (by omega))), zero_div]
end GlobalTheory.RowLaw.GoodPair
