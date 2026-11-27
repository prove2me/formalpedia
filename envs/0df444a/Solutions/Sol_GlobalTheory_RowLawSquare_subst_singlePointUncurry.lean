-- Prove2me | solution 1 for GlobalTheory.RowLawSquare.subst_singlePointUncurry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:29:51.143541+00:00
-- url     : https://prove2.me/submissions/88fcbdbf-6f93-4606-9f0e-3ee47d6b8033

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
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
variable {dd : ℕ}
namespace GlobalTheory.RowLawSquare
theorem _root_.solution {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (f : PS C 1 dd) :
    subst a (un1 f) = subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  ext μ
  let e : Fin dd ≃ Fin 1 × Fin dd :=
    ⟨fun x => (0, x), fun p => p.2, fun _ => rfl, fun p => Prod.ext (Subsingleton.elim _ _) rfl⟩
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha),
    coeff_subst (hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin dd => ha p.2),
    ← finsum_comp_equiv (Finsupp.domCongr (M := ℕ) e).toEquiv]
  refine finsum_congr fun ν => ?_
  have h1 : (Finsupp.domCongr (M := ℕ) e).toEquiv ν = ν.mapDomain fun x : Fin dd => ((0 : Fin 1), x) :=
    Finsupp.equivMapDomain_eq_mapDomain e ν
  rw [h1, Finsupp.prod_mapDomain_index (by simp) (fun _ _ _ => pow_add _ _ _)]
  rfl
end GlobalTheory.RowLawSquare
