-- Prove2me | solution 1 for GlobalTheory.RowLaw.RLaw.coeff_single_endP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:23:54.461944+00:00
-- url     : https://prove2.me/submissions/bcfdfee4-1f9f-48df-a6f7-3a1722661a61

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGaugeBilinearTermOfTypeNe
import Theorems.Thm_GlobalTheory_RowLaw_coeff_single_subst
import Theorems.Thm_GlobalTheory_RowLaw_RLaw_constantCoeff_lg
import Theorems.Thm_GlobalTheory_RowLaw_RLaw_coeff_single_lg
import Theorems.Thm_GlobalTheory_RowLaw_RLaw_coeff_single_ex
import Theorems.Thm_GlobalTheory_RowLaw_RLaw_constantCoeff_lin
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
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
variable {Y : RawChart C d I κ} {V : VF C}
namespace GlobalTheory.RowLaw
namespace RLaw
theorem _root_.solution (h : RLaw Y V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ x, constantCoeff (a x) = 0) (x : κ) (t : τ) :
    coeff (Finsupp.single t 1) (endP Y M a x) = ∑ y, M x y * coeff (Finsupp.single t 1) (a y) := by
  unfold endP
  rw [coeff_single_subst (h.constantCoeff_lin M ha) (h.exc x)]
  simp only [h.coeff_single_ex, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [coeff_smul, coeff_single_subst ha (h.constantCoeff_lg y)]
  simp only [h.coeff_single_lg, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end RLaw
end GlobalTheory.RowLaw
