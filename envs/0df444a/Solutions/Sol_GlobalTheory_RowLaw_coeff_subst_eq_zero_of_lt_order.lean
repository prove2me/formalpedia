-- Prove2me | solution 1 for GlobalTheory.RowLaw.coeff_subst_eq_zero_of_lt_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:42:30.846318+00:00
-- url     : https://prove2.me/submissions/a48a23b3-8ded-4850-bd6a-a75ca3cb8942

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGaugeBilinearTermOfTypeNe
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1


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
namespace GlobalTheory.RowLaw
theorem _root_.solution {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ C} {n : ℕ}
    (hf : ∀ e : σ →₀ ℕ, e.degree < n → coeff e f = 0) :
    (n : ℕ∞) ≤ (subst a f).order := by
  refine le_trans ?_ (le_order_subst (hasSubst_of_constantCoeff_zero ha) f)
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
    le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha i)
  calc (n : ℕ∞) = 1 * n := (one_mul _).symm
    _ ≤ _ := mul_le_mul' h1 (nat_le_order hf)
end GlobalTheory.RowLaw
