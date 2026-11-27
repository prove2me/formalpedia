-- Prove2me | solution 1 for GlobalTheory.AnVal.AnFr.jetMap_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:07:34.707664+00:00
-- url     : https://prove2.me/submissions/a0c83683-4a59-4e95-973f-e007eba0656e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Theorems.Thm_GlobalTheory_AnVal_isHolFam_pullback_lift
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
theorem _root_.solution {n m : ℕ} (a b : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.JetMap m a.left Λ) (hb : Φ.JetMap m b.left Λ') :
    ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left),
      (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt _ hq m := by
  obtain ⟨hola, ha⟩ := ha
  obtain ⟨holb, hb⟩ := hb
  have hq : IsHolFam (fun v : Fin (n * g) → ℂ =>
      (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left) :=
    GlobalTheory.AnVal.isHolFam_pullback_lift S A.left A.left A.hom A.hom (n * g) _ _ x0 (fun v => Over.w (Φ.e (Λ (colsOf n g v))))
      (fun v => Over.w (Φ.e (Λ' (colsOf n g v)))) hola holb
  refine ⟨hq, ?_⟩
  have hf : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (fst A A).left = (Φ.e (Λ (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_fst]
  have hs : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (snd A A).left = (Φ.e (Λ' (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_snd]
  apply pullback.hom_ext
  · show (lift a b).left ≫ (fst A A).left = (_ ≫ jetPt _ hq m) ≫ (fst A A).left
    rw [← Over.comp_left, lift_fst, Category.assoc, jetPt_comp _ hq _ _ hola hf, ha]
  · show (lift a b).left ≫ (snd A A).left = (_ ≫ jetPt _ hq m) ≫ (snd A A).left
    rw [← Over.comp_left, lift_snd, Category.assoc, jetPt_comp _ hq _ _ holb hs, hb]
end AnFr
end GlobalTheory.AnVal
