-- Prove2me | solution 1 for GlobalTheory.CongruentCharacters.eq_zero_of_ge_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:28:56.165192+00:00
-- url     : https://prove2.me/submissions/fe4799e4-5364-4c83-8ea1-dc4c2369d807

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RingHomEqOfCongruentIntegralUnramified

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
open GlobalTheory GlobalTheory.CongruentCharacters
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.CongruentCharacters
theorem _root_.solution {a : C} (h : ∀ n : ℕ, V.Ge n a) : a = 0 := by
  apply (AddValuation.top_iff V.v).1
  induction hv : V.v a using WithTop.recTopCoe with
  | top => rfl
  | coe t =>
    exfalso
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have := h n
    unfold VF.Ge at this
    rw [hv] at this
    have h' : (n : ℝ) ≤ t := WithTop.coe_le_coe.1 this
    linarith
end GlobalTheory.CongruentCharacters
