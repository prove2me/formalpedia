-- Prove2me | solution 1 for GlobalTheory.ActionLimit.Low.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:32:54.954676+00:00
-- url     : https://prove2.me/submissions/4dfc8798-215a-42da-baf1-d56458a1e5cb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ActionConvergesLadicCauchyAndStar
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.ActionLimit
open MvPowerSeries GlobalTheory.GaugeAdjoint
variable {C : Type} [Field C] {V : VF C} {σ τ : Type}
namespace GlobalTheory.ActionLimit
namespace Low
theorem _root_.solution {D : ℕ} {w w' : ℝ} {g h : MvPowerSeries τ C} (hg : Low V D w g) (hh : Low V D w' h) :
    Low V D (w + w') (g * h) := fun μ hμ => by
  classical
  rw [coeff_mul]
  refine VF.Ge.sum fun p hp => ?_
  have e : p.1.degree + p.2.degree = μ.degree := by
    rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  exact (hg _ (by omega)).mul (hh _ (by omega))
end Low
end GlobalTheory.ActionLimit
