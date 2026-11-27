-- Prove2me | solution 1 for GlobalTheory.JetVal.lftJ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:23.404712+00:00
-- url     : https://prove2.me/submissions/588f3273-da23-495a-a9ff-231552ce497a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsValueAtJetPointCmFrameSection
import Theorems.Thm_GlobalTheory_JetVal_lftJ_snd
import Theorems.Thm_GlobalTheory_JetVal_lftJ_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_over


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
open GlobalTheory GlobalTheory.JetVal
open AlgebraicGeometry CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] (L : LB G.left) {x0 : Sp ℂ ⟶ X} {g : ℕ}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (hol : IsHolFam e) (he : ∀ z, e z ≫ G.hom = x0)
namespace GlobalTheory.JetVal
theorem _root_.solution (holP : IsHolFam (lftJ e he)) (m : ℕ) :
    (ptSecT G (xJ e hol he m)).left ≫ (jB (x0 := x0) (g := g) m ▷ G).left = jetPt (lftJ e he) holP m := by
  have h1 : jetPt (lftJ e he) holP m ≫ (Over.mk x0 ⊗ G).hom =
      spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫ x0 :=
    jetPt_over (lftJ e he) holP _ x0 (fun z => Over.w (ptSecT G (ePt e he z))) m
  let φ : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ Over.mk x0 ⊗ G := Over.homMk (jetPt (lftJ e he) holP m) h1
  suffices hs : ptSecT G (xJ e hol he m) ≫ jB m ▷ G = φ by
    rw [← Over.comp_left, hs]
    rfl
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, whiskerRight_fst, ptSecT, lift_fst_assoc, Category.id_comp]
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    show spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) = jetPt (lftJ e he) holP m ≫ (fst (Over.mk x0) G).left
    rw [jetPt_comp (lftJ e he) holP _ (fun _ => 𝟙 (Sp ℂ)) (isHolFam_const _) (lftJ_fst e he) m, ← jetPt_const,
      Category.comp_id]
  · rw [Category.assoc, whiskerRight_snd, ptSecT, lift_snd]
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    show jetPt e hol m = jetPt (lftJ e he) holP m ≫ (snd (Over.mk x0) G).left
    rw [jetPt_comp (lftJ e he) holP _ e hol (lftJ_snd e he) m]
end GlobalTheory.JetVal
