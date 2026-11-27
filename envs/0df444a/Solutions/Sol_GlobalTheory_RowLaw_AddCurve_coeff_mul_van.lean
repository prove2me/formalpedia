-- Prove2me | solution 1 for GlobalTheory.RowLaw.AddCurve.coeff_mul_van
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:16:47.376971+00:00
-- url     : https://prove2.me/submissions/842252c2-a421-434a-8579-eb58362adced

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
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.AddCurve
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.AddCurve
theorem _root_.solution {τ : Type} {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g)
    (ν : τ →₀ ℕ) (hν : ∀ w ∈ ν.support, w ∉ T) (t : τ) : coeff (ν + Finsupp.single t 1) (f * g) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = ν + Finsupp.single t 1 := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  by_cases h : ∀ w ∈ a.support, w ∉ T
  · simp [hf a h]
  · push Not at h
    obtain ⟨w, hw, hwT⟩ := h
    have hb : ∀ w' ∈ b.support, w' ∉ T := by
      intro w' hw' hw'T
      have h1 := Finsupp.mem_support_iff.1 hw
      have h2 := Finsupp.mem_support_iff.1 hw'
      have n1 : ν w = 0 := by
        by_contra hc
        exact hν w (Finsupp.mem_support_iff.2 hc) hwT
      have n2 : ν w' = 0 := by
        by_contra hc
        exact hν w' (Finsupp.mem_support_iff.2 hc) hw'T
      have e1 := DFunLike.congr_fun hab' w
      have e2 := DFunLike.congr_fun hab' w'
      simp only [Finsupp.add_apply, n1, n2, Finsupp.single_apply] at e1 e2
      have t1 : t = w := by
        by_contra hc
        rw [if_neg hc] at e1
        omega
      have t2 : t = w' := by
        by_contra hc
        rw [if_neg hc] at e2
        omega
      subst t1
      subst t2
      rw [if_pos rfl] at e1
      omega
    simp [hg b hb]
end GlobalTheory.RowLaw.AddCurve
