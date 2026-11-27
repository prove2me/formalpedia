-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvEnd.taylor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:13:20.961332+00:00
-- url     : https://prove2.me/submissions/38bc64cc-ce75-4d12-aa32-db34e2241b57

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_ordGe_zero
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_ordGe_mul
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_ordGe_X
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_coeff_dz
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_exists_em
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_dz_X_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_sum_mem
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
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd
open MvPowerSeries
variable {C : Type} [Field C]
variable {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw.CvEnd
theorem _root_.solution {F : MvPowerSeries (Fin 2 × κ) C} (hF : F ∈ ordGe C (wz κ) 1) :
    F - ∑ j, X ((1 : Fin 2), j) * rename (e0 κ) (dz j F) ∈ ordGe C (wz κ) 2 := by
  classical
  intro e he
  by_cases h1 : Finsupp.weight (wz κ) e = 1
  · obtain ⟨i, μ, rfl⟩ := exists_em e h1
    rw [← coeff_dz, map_sub, map_sum]
    simp [dz_X_mul]
  · have : F - ∑ j, X ((1 : Fin 2), j) * rename (e0 κ) (dz j F) ∈ ordGe C (wz κ) 1 :=
      Submodule.sub_mem _ hF (Submodule.sum_mem _ fun j _ => ordGe_mul (ordGe_X ((1 : Fin 2), j)) (ordGe_zero _))
    exact this e (by omega)
end GlobalTheory.RowLaw.CvEnd
