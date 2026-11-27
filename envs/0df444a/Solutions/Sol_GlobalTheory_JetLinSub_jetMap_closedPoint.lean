-- Prove2me | solution 1 for GlobalTheory.JetLinSub.jetMap_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:59:36.869338+00:00
-- url     : https://prove2.me/submissions/e458f7dc-6d03-45c1-8633-18ebadd9c59f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Theorems.Thm_GlobalTheory_JetLinSub_spMap_closedPoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_jetMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_closedPoint


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
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.JetLinSub
theorem _root_.solution {n m : ℕ} (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : Φ.JetMap m ψ Λ) :
    ψ (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) = (Φ.e 0).left PullbackSections.cpt := by
  obtain ⟨hol, rfl⟩ := h
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  refine (congrArg _ (spMap_closedPoint _ (isLocalHom_jetMap _ _))).trans ?_
  refine (jetPt_closedPoint _ hol m).trans ?_
  have : Λ (colsOf n g 0) = 0 := map_zero Λ
  simp only [this]
end GlobalTheory.JetLinSub
