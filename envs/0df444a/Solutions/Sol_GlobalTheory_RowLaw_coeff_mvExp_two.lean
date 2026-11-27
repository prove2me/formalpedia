-- Prove2me | solution 1 for GlobalTheory.RowLaw.coeff_mvExp_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:20:46.358312+00:00
-- url     : https://prove2.me/submissions/7a9ab5a7-8c27-4531-87a4-7ab2266a76d0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGaugeBilinearTermOfTypeNe
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
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
namespace GlobalTheory.RowLaw
theorem _root_.solution {τ : Type} {F : MvPowerSeries τ C} (hF : ((2 : ℕ) : ℕ∞) ≤ F.order) (m : τ →₀ ℕ)
    (hm : m.degree = 2) : coeff m (mvExp F) = coeff m F := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have h2 : coeff m (F ^ 2) = 0 := by
    apply coeff_of_lt_order
    refine lt_of_lt_of_le ?_ (le_order_pow 2)
    refine lt_of_lt_of_le ?_ (nsmul_le_nsmul_right hF 2)
    rw [hm]
    decide
  show ∑ k ∈ Finset.range (m.degree + 1), coeff m (F ^ k) / (k.factorial : C) = _
  rw [hm]
  simp [Finset.sum_range_succ, h2, coeff_one, hm0]
end GlobalTheory.RowLaw
