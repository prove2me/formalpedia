-- Prove2me | solution 1 for GlobalTheory.RowLaw.AddCurve.subst_pderiv_hAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:45:36.79443+00:00
-- url     : https://prove2.me/submissions/c80030b5-746d-4296-9a7a-553d4365056c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_pair_const
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_gp_const
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst
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
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw.AddCurve
theorem _root_.solution (X : RawChart C d I κ) {τ : Type} {A : κ → MvPowerSeries (Fin 3 × κ) C}
    (hA : ∀ s, constantCoeff (A s) = 0) (i : κ) (hA' : ∀ x, pderiv C ((2 : Fin 3), i) (A x) = 0)
    {a : Fin 3 × κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) (ha2 : ∀ x, a (2, x) = 0) :
    subst a (pderiv C ((2 : Fin 3), i) (hAt X A (gp C κ 2))) =
      subst (fun p : Fin 2 × κ => if p.1 = 0 then subst a (A p.2) else 0) (pderiv C ((1 : Fin 2), i) X.h) := by
  have hS := hasSubst_of_constantCoeff_zero ha
  have hP := hasSubst_of_constantCoeff_zero (pair_const hA (gp_const (C := C) (κ := κ) (2 : Fin 3)))
  unfold hAt
  rw [FormalCalc.pderiv_subst hP, Finset.sum_eq_single ((1 : Fin 2), i)]
  · have : pderiv C ((2 : Fin 3), i) (if ((1 : Fin 2), i).1 = 0 then A ((1 : Fin 2), i).2
        else gp C κ (2 : Fin 3) ((1 : Fin 2), i).2) = 1 := by
      rw [if_neg (by simp)]
      exact pderiv_X_self
    rw [this, mul_one, subst_comp_subst_apply hP hS]
    congr 1
    funext p
    split_ifs
    · rfl
    · unfold gp
      rw [subst_X hS, ha2]
  · rintro ⟨g, x⟩ _ hb
    split_ifs with hg
    · rw [hA', mul_zero]
    · have hg1 : g = 1 := by
        have : g ≠ 0 := hg
        omega
      subst hg1
      unfold gp
      rw [pderiv_X_of_ne, mul_zero]
      intro h
      apply hb
      have := (Prod.ext_iff.1 h).2
      simp only at this
      rw [this]
  · intro h
    exact absurd (Finset.mem_univ _) h
end GlobalTheory.RowLaw.AddCurve
