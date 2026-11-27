-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvEnd.isCv_along
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:04:29.445686+00:00
-- url     : https://prove2.me/submissions/bc38f71a-2fc8-48dc-9446-056b38df6dfe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_intS_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_subst_zero


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
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd
open MvPowerSeries
variable {C : Type} [Field C]
variable {V : VF C} {σ τ : Type}
namespace GlobalTheory.RowLaw.CvEnd
theorem _root_.solution [Finite σ] {γ : σ → PowerSeries C} (hγ : IsCv V γ) {ι : Type} {f : ι → MvPowerSeries σ C}
    (h0 : ∀ i, constantCoeff (f i) = 0) (hf : ∀ i, IntS V (f i)) : IsCv V fun i => alongCv γ (f i) := by
  intro i
  refine ⟨constantCoeff_subst_zero (τ := Unit) (fun s => (hγ s).1) (h0 i), fun n => ?_⟩
  refine intS_subst (τ := Unit) (hasSubst_of_constantCoeff_zero fun s => (hγ s).1) (fun s e => ?_) (hf i)
    (Finsupp.single () n)
  have he : e = Finsupp.single () (e ()) := Finsupp.unique_single e
  rw [he]
  exact (hγ s).2 _
end GlobalTheory.RowLaw.CvEnd
