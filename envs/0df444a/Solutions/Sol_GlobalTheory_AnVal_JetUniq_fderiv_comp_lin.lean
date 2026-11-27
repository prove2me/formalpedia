-- Prove2me | solution 1 for GlobalTheory.AnVal.JetUniq.fderiv_comp_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:19.423385+00:00
-- url     : https://prove2.me/submissions/4a09b6bc-57ab-4091-b9c0-2e864790a71a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf

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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetUniq
namespace GlobalTheory.AnVal.JetUniq
theorem _root_.solution {a b : ℕ} (θ : (Fin b → ℂ) → ℂ) (hθ : DifferentiableAt ℂ θ 0)
    (T : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ)) (v : Fin a → ℂ) :
    fderiv ℂ (fun z => θ (T z)) 0 v = fderiv ℂ θ 0 (T v) := by
  set Tc := LinearMap.toContinuousLinearMap T with hTc
  have hT : HasFDerivAt (⇑Tc) Tc 0 := Tc.hasFDerivAt
  have hθ' : HasFDerivAt θ (fderiv ℂ θ 0) (Tc 0) := by
    rw [map_zero]
    exact hθ.hasFDerivAt
  change fderiv ℂ (θ ∘ ⇑Tc) 0 v = _
  rw [(hθ'.comp (0 : Fin a → ℂ) hT).fderiv]
  rfl
end GlobalTheory.AnVal.JetUniq
