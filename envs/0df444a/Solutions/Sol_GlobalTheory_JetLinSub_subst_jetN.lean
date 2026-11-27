-- Prove2me | solution 1 for GlobalTheory.JetLinSub.subst_jetN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:38:09.508502+00:00
-- url     : https://prove2.me/submissions/64f94900-0118-469b-8b9f-856c8dcde812

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Theorems.Thm_GlobalTheory_JetLinSub_colsOf_flatL
import Theorems.Thm_GlobalTheory_JetLinSub_subst_renN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetOf_comp_anLin


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetLinSub
namespace GlobalTheory.JetLinSub
theorem _root_.solution {n n' g m : ℕ} (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ))
    (σ : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
    (hσ : ∀ p, σ (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2))
    (f : (Fin n → Fin g → ℂ) → ℂ) (hf : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0) :
    σ (jetN m f) = jetN m (fun w => f (B w)) := by
  rw [jetN, subst_renN B σ hσ, ← jetOf_comp_anLin m hf (flatL B), jetN]
  congr 2
  funext v
  simp only [Function.comp_apply, colsOf_flatL]
end GlobalTheory.JetLinSub
