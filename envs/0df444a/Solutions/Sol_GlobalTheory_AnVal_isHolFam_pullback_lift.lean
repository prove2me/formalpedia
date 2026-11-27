-- Prove2me | solution 1 for GlobalTheory.AnVal.isHolFam_pullback_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:56.908195+00:00
-- url     : https://prove2.me/submissions/f9c4d353-df73-4bc2-a42b-31c650fde363

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Theorems.Thm_GlobalTheory_HolFibre_isHolTo_of_isPullback


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
open GlobalTheory GlobalTheory.AnVal
namespace GlobalTheory.AnVal
theorem _root_.solution : ∀ (X Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (N : ℕ) (e₁ : (Fin N → ℂ) → (Sp ℂ ⟶ Y₁)) (e₂ : (Fin N → ℂ) → (Sp ℂ ⟶ Y₂)) (u : Sp ℂ ⟶ X) (h₁ : ∀ z, e₁ z ≫ p₁ = u) (h₂ : ∀ z, e₂ z ≫ p₂ = u), IsHolFam e₁ → IsHolFam e₂ → IsHolFam (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm)) := by
  intro X Y₁ Y₂ p₁ p₂ N e₁ e₂ u h₁ h₂ hol₁ hol₂
  have ea : (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.fst p₁ p₂) = e₁ :=
    funext fun z => pullback.lift_fst _ _ _
  have eb : (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.snd p₁ p₂) = e₂ :=
    funext fun z => pullback.lift_snd _ _ _
  have ha : IsHolTo (Set.univ : Set (Fin N → ℂ))
      (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.fst p₁ p₂) := by
    rw [ea]
    intro U f
    simpa using hol₁ U f
  have hb : IsHolTo (Set.univ : Set (Fin N → ℂ))
      (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.snd p₁ p₂) := by
    rw [eb]
    intro U f
    simpa using hol₂ U f
  have hc := GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback p₁ p₂) ha hb
  intro U f
  simpa using hc U f
end GlobalTheory.AnVal
