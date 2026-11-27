-- Prove2me | solution 1 for GlobalTheory.RowLaw.GoodPair.coeff_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:22:04.510575+00:00
-- url     : https://prove2.me/submissions/f56cee02-611c-43e4-a9fa-caf69e3e62b2

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
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_ee_zero
import Theorems.Thm_GlobalTheory_RowLaw_GoodPair_ee_one
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_sg_eq
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_sg_eq
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_subst_sum_smul
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


attribute [local simp] GlobalTheory.RowLaw.GoodPair.ee_zero
attribute [local simp] GlobalTheory.RowLaw.GoodPair.ee_one

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GoodPair
variable {C : Type} [Field C]
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}
namespace GlobalTheory.RowLaw.GoodPair
theorem _root_.solution (X : RawChart C d I κ) {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (v : κ → C) (n : ℕ) :
    PowerSeries.coeff n (alongCv γ (X.sg v)) = -∑ j, v j * PowerSeries.coeff n (alongCv γ (dz j X.h)) := by
  have hS : HasSubst γ := hasSubst_of_constantCoeff_zero (τ := Unit) hγ
  have : alongCv γ (X.sg v) = -∑ j, v j • alongCv γ (dz j X.h) := by
    unfold alongCv
    rw [CvEnd.sg_eq, ← CvEnd.subst_sum_smul hS, ← coe_substAlgHom hS, map_neg]
  rw [this, map_neg, map_sum]
  simp only [PowerSeries.coeff_smul, smul_eq_mul]
end GlobalTheory.RowLaw.GoodPair
