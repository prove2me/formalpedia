-- Prove2me | solution 1 for GlobalTheory.RowLaw.EndBlock.hAt_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:18:04.902543+00:00
-- url     : https://prove2.me/submissions/18193b17-d798-430d-8d03-33b7049216f6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeAdjointEndPairElementaryBlock
import Theorems.Thm_GlobalTheory_RowLaw_EndBlock_eq_zero_of_van
import Theorems.Thm_GlobalTheory_RowLaw_EndBlock_cc_pair
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.EndBlock
open MvPowerSeries
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace GlobalTheory.RowLaw.EndBlock
theorem _root_.solution (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → coeff e X.h = 0) {τ : Type}
    {b : κ → MvPowerSeries τ C} (hb : ∀ i, constantCoeff (b i) = 0) : hAt X (fun _ => 0) b = 0 := by
  refine eq_zero_of_van (Van.subst {s : Fin 2 × κ | s.1 = 0} (cc_pair (fun _ => map_zero _) hb) ?_ hh)
  intro s hs ν _
  have h0 : s.1 = 0 := hs
  rw [if_pos h0, map_zero]
end GlobalTheory.RowLaw.EndBlock
