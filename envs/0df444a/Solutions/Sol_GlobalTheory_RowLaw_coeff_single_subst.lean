-- Prove2me | solution 1 for GlobalTheory.RowLaw.coeff_single_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:53:13.749815+00:00
-- url     : https://prove2.me/submissions/7f5a5fd3-94cd-4538-bdeb-61b86617a3a6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGaugeBilinearTermOfTypeNe
import Theorems.Thm_GlobalTheory_RowLaw_coeff_subst_eq_zero_of_lt_order
import Theorems.Thm_GlobalTheory_RowLaw_subst_sum_smul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_finsupp_deg_one
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
theorem _root_.solution {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) (t : τ) :
    coeff (Finsupp.single t 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single t 1) (a s) := by
  have hs := hasSubst_of_constantCoeff_zero ha
  set L : MvPowerSeries σ C := ∑ s, coeff (Finsupp.single s 1) f • (X s : MvPowerSeries σ C) with hL
  have hr : ((2 : ℕ) : ℕ∞) ≤ (subst a (f - L)).order := by
    apply coeff_subst_eq_zero_of_lt_order ha
    intro e he
    rw [map_sub, hL, map_sum, sub_eq_zero]
    simp only [coeff_smul, coeff_X]
    by_cases h0 : e.degree = 0
    · rw [Finsupp.degree_eq_zero_iff] at h0
      subst h0
      rw [coeff_zero_eq_constantCoeff_apply, hf]
      symm
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [if_neg, mul_zero]
      exact (Finsupp.single_ne_zero.2 one_ne_zero).symm
    · obtain ⟨i, rfl⟩ := finsupp_deg_one e (by omega)
      rw [Finset.sum_eq_single i]
      · simp
      · intro s _ hsi
        rw [if_neg, mul_zero]
        exact fun h => hsi (Finsupp.single_left_injective one_ne_zero h).symm
      · simp
  have hz : coeff (Finsupp.single t 1) (subst a (f - L)) = 0 :=
    coeff_of_lt_order (lt_of_lt_of_le (by rw [Finsupp.degree_single]; exact_mod_cast one_lt_two) hr)
  rw [subst_sub hs, map_sub, sub_eq_zero] at hz
  rw [hz, hL, subst_sum_smul hs, map_sum]
  simp only [coeff_smul, subst_X hs]
end GlobalTheory.RowLaw
