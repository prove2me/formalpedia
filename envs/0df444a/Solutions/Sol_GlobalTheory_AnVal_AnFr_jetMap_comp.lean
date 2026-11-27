-- Prove2me | solution 1 for GlobalTheory.AnVal.AnFr.jetMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:58:40.488638+00:00
-- url     : https://prove2.me/submissions/b53107f4-3647-44ea-a2e6-bd17da9631da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolFam_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_comp


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
open GlobalTheory GlobalTheory.AnVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.AnVal
namespace AnFr
theorem _root_.solution {n m : ℕ} (a : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ : A ⟶ A) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hT : ∀ z, Φ.e (T z) = Φ.e z ≫ φ) (ha : Φ.JetMap m a.left Λ) : Φ.JetMap m (a ≫ φ).left (T ∘ₗ Λ) := by
  obtain ⟨hol, ha⟩ := ha
  have hc : ∀ v : Fin (n * g) → ℂ, (Φ.e (Λ (colsOf n g v))).left ≫ φ.left =
      (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left := fun v => by
    rw [LinearMap.comp_apply, hT, Over.comp_left]
  have hol' : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left) := by
    rw [← funext hc]; exact isHolFam_comp _ hol _
  refine ⟨hol', ?_⟩
  rw [Over.comp_left, ha, Category.assoc, jetPt_comp _ hol _ _ hol' hc]
end AnFr
end GlobalTheory.AnVal
