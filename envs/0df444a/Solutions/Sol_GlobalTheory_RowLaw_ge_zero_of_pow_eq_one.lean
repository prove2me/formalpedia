-- Prove2me | solution 1 for GlobalTheory.RowLaw.ge_zero_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:21:34.268825+00:00
-- url     : https://prove2.me/submissions/cc7b7fc6-065d-4df8-98d0-53fede04c953

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGaugeBilinearTermOfTypeNe

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
open GlobalTheory GlobalTheory.RowLaw
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw
theorem _root_.solution (V : VF C) {N : ℕ} (hN : N ≠ 0) {a : C} (ha : a ^ N = 1) : V.Ge 0 a := by
  have h := V.v.map_pow a N
  rw [ha, V.v.map_one] at h
  unfold VF.Ge
  induction hv : V.v a using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv] at h
    have h' : ((0 : ℝ) : WithTop ℝ) = ((N • t : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_nsmul]; exact h
    have h'' : (0 : ℝ) = N • t := by exact_mod_cast h'
    rw [nsmul_eq_mul] at h''
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have : t = 0 := by
      rcases mul_eq_zero.1 h''.symm with h | h
      · exact absurd h hN'
      · exact h
    rw [this]
end GlobalTheory.RowLaw
