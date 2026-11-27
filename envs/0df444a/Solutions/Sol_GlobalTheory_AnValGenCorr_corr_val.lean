-- Prove2me | solution 1 for GlobalTheory.AnValGenCorr.corr_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:41.996832+00:00
-- url     : https://prove2.me/submissions/5f1ae8cb-1f11-4280-b30a-2ea20b66ab4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv
import Theorems.Thm_GlobalTheory_AnValGenCorr_chart_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AnValGenCorr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnValGenCorr
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (hc : LB.Gen.Corr L φ ε φ' ε' t t')
    (J : (Y ⟶ X) → L.ι) (p : Sp ℂ ⟶ Y) (hJ : ∀ ψ, ⊤ ≤ (p ≫ ψ) ⁻¹ᵁ L.U (J ψ)) :
    valAt' p (LB.wchart L φ fun k => J (φ k)) (t.s fun k => J (φ k)).val =
      valAt' p (LB.wchart L φ' fun k => J (φ' k)) (t'.s fun k => J (φ' k)).val := by
  have h1 := (chart_iff L φ (fun k => J (φ k)) p).2 fun k => hJ _
  have h2 := (chart_iff L φ' (fun k => J (φ' k)) p).2 fun k => hJ _
  have h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ (fun k => J (φ k)) ⊓ LB.wchart L φ' fun k => J (φ' k)) :=
    fun z hz => ⟨h1 hz, h2 hz⟩
  have e0 := hc (fun k => J (φ k)) (fun k => J (φ' k)) (fun _ _ e => congrArg J e) (fun _ _ e => congrArg J e)
    (fun _ _ e => congrArg J e)
  have e := congrArg (fun u : Γ(Y, LB.wchart L φ (fun k => J (φ k)) ⊓ LB.wchart L φ' fun k => J (φ' k))ˣ =>
    valAt' p _ u.val) e0
  exact (vtf_val_res p _ h _).symm.trans (e.trans (vtf_val_res p _ h _))
end GlobalTheory.AnValGenCorr
