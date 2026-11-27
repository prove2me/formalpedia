-- Prove2me | solution 1 for GlobalTheory.RowLaw.GaugeDeriv.pr_prop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:28:22.491941+00:00
-- url     : https://prove2.me/submissions/bd6417e8-1323-4ab9-8167-2950f1111c88

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLaw

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
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}
omit [Fintype κ]
namespace GlobalTheory.RowLaw.GaugeDeriv
theorem _root_.solution {P : MvPowerSeries τ C → Prop} {a b : κ → MvPowerSeries τ C} (ha : ∀ i, P (a i))
    (hb : ∀ i, P (b i)) : ∀ p, P (pr a b p) := by
  intro p
  unfold pr
  split_ifs
  · exact ha _
  · exact hb _
end GlobalTheory.RowLaw.GaugeDeriv
