-- Prove2me | solution 1 for GlobalTheory.AnValJetGlob.appLE_spMap_jetPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:59.332936+00:00
-- url     : https://prove2.me/submissions/55c1ab5d-a0bb-4201-aa6d-ded634d2d501

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_closedPoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_specMap_comp_appLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnValJetGlob
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.AnValJetGlob
theorem _root_.solution {N m : ℕ} {I : Type} {Z : Scheme.{0}} (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (hq : IsHolFam q)
    (χ : Jet ℂ (Fin 1 × Fin N) m →+* Jet ℂ I m) [IsLocalHom χ] (U : Z.Opens)
    (h : ⊤ ≤ (spMap χ ≫ jetPt q hq m) ⁻¹ᵁ U) :
    q 0 cpt ∈ U ∧ ∀ f : Γ(Z, U), (spMap χ ≫ jetPt q hq m).appLE U ⊤ h f =
      toΓ _ (χ (jetOf m fun v => valAt' (q v) U f)) := by
  have hU : q 0 cpt ∈ U := by
    have : (spMap χ ≫ jetPt q hq m) (IsLocalRing.closedPoint _) ∈ U :=
      h (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [Scheme.Hom.comp_apply, spMap, Spec_closedPoint, jetPt_closedPoint] at this
  refine ⟨hU, fun f => ?_⟩
  have hp : ⊤ ≤ jetPt q hq m ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (jetPt q hq m) (by rw [jetPt_closedPoint]; exact hU)).ge
  have k := specMap_comp_appLE (CommRingCat.ofHom χ) (jetPt q hq m) U h hp
  rw [jetPt_appLE q hq m U hU hp, Category.assoc, Iso.inv_hom_id_assoc, ← Iso.eq_comp_inv] at k
  have k' := ConcreteCategory.congr_hom k f
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, jetψ_apply] at k'
  exact k'
end GlobalTheory.AnValJetGlob
