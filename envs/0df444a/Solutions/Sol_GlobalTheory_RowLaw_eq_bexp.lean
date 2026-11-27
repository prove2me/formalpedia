-- Prove2me | solution 1 for GlobalTheory.RowLaw.eq_bexp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:53:31.589517+00:00
-- url     : https://prove2.me/submissions/a20b309d-2560-4af2-931a-2c0349f742b7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGaugeBilinearTermOfTypeNe
import Theorems.Thm_GlobalTheory_RowLaw_bexp_degree
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
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
namespace GlobalTheory.RowLaw
theorem _root_.solution {κ : Type} (e : Fin 2 × κ →₀ ℕ) (he : e.degree < 3) {a b : κ}
    (ha : (0, a) ∈ e.support) (hb : (1, b) ∈ e.support) : e = bexp a b := by
  have hle : bexp a b ≤ e := by
    intro p
    have ha' := Finsupp.mem_support_iff.1 ha
    have hb' := Finsupp.mem_support_iff.1 hb
    simp only [bexp, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with h1 h2 h2
    · rw [← h1] at h2; simp at h2
    · rw [← h1]; omega
    · rw [← h2]; omega
    · omega
  have hsum : bexp a b + (e - bexp a b) = e := add_tsub_cancel_of_le hle
  have hd : (bexp a b).degree + (e - bexp a b).degree = e.degree := by rw [← map_add, hsum]
  rw [bexp_degree] at hd
  have h0 : (e - bexp a b).degree = 0 := by omega
  rw [Finsupp.degree_eq_zero_iff] at h0
  rw [h0, add_zero] at hsum
  exact hsum.symm
end GlobalTheory.RowLaw
