-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvGroup.zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:20:32.105752+00:00
-- url     : https://prove2.me/submissions/4d0ec373-e3a0-498a-a47d-34aa67956c90

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupResca
import Theorems.Thm_GlobalTheory_RowLaw_CvGroup_lg_const
import Theorems.Thm_GlobalTheory_RowLaw_CvGroup_sg_const
import Theorems.Thm_GlobalTheory_RowLaw_CvGroup_isCv_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_alongCv_zero
import Theorems.Thm_GlobalTheory_RowLaw_AddCurve_lg_const


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
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvGroup
variable {C : Type} [Field C]
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}
namespace GlobalTheory.RowLaw.CvGroup
theorem _root_.solution (H : RLaw X V) (g : Fin 2) : 0 ∈ Cv X V g :=
  ⟨fun _ => 0, fun _ => 0, isCv_zero, isCv_zero, fun i => alongCv_zero (lg_const H i), fun q => by
    rw [alongCv_zero (sg_const H _), sub_zero]; rfl⟩
end GlobalTheory.RowLaw.CvGroup
