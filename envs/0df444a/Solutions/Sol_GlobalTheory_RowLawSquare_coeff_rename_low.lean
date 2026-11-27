-- Prove2me | solution 1 for GlobalTheory.RowLawSquare.coeff_rename_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:37:07.801993+00:00
-- url     : https://prove2.me/submissions/25823362-3d1b-412f-bb78-28d3acfa059d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_prod
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
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLawSquare
variable {C : Type} [Field C] {σ τ : Type}
namespace GlobalTheory.RowLawSquare
theorem _root_.solution [Finite σ] (φ : σ → τ) {f g : MvPowerSeries σ C} {N : ℕ}
    (hfg : ∀ e : σ →₀ ℕ, e.degree ≤ N → coeff e f = coeff e g) (μ : τ →₀ ℕ) (hμ : μ.degree ≤ N) :
    coeff μ (subst (fun s => (X (φ s) : MvPowerSeries τ C)) f) =
      coeff μ (subst (fun s => (X (φ s) : MvPowerSeries τ C)) g) := by
  have hS : HasSubst (fun s => (X (φ s) : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _
  rw [coeff_subst hS, coeff_subst hS]
  refine finsum_congr fun e => ?_
  by_cases he : e.degree ≤ N
  · rw [hfg e he]
  · have h1 : (e.prod fun s m => (X (φ s) : MvPowerSeries τ C) ^ m) = monomial (e.mapDomain φ) 1 := by
      rw [monomial_one_eq, Finsupp.prod_mapDomain_index (by simp) (fun _ _ _ => pow_add _ _ _)]
    have h2 : μ ≠ e.mapDomain φ := by
      rintro rfl
      apply he
      rwa [Finsupp.degree_mapDomain] at hμ
    rw [h1, coeff_monomial_ne h2, smul_zero, smul_zero]
end GlobalTheory.RowLawSquare
