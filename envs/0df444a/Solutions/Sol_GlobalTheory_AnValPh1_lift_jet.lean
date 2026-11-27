-- Prove2me | solution 1 for GlobalTheory.AnValPh1.lift_jet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:39:49.867047+00:00
-- url     : https://prove2.me/submissions/13cc5ae7-344e-447c-ac6c-883be6bc5763

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProductsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameFirstPartialLawTrivial
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
open GlobalTheory GlobalTheory.AnValPh1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnValPh1
theorem _root_.solution {S : Scheme.{0}} {P Q : Over S} {N m : ℕ} {R : Type} [CommRing R]
    (r : Jet ℂ (Fin 1 × Fin N) m →+* R) (u : Sp R ⟶ S) (x : Sp ℂ ⟶ S)
    (a : Over.mk u ⟶ P) (b : Over.mk u ⟶ Q) (f : (Fin N → ℂ) → (Over.mk x ⟶ P)) (h : (Fin N → ℂ) → (Over.mk x ⟶ Q))
    (hf : IsHolFam fun v => (f v).left) (hh : IsHolFam fun v => (h v).left)
    (ea : a.left = spMap r ≫ jetPt _ hf m) (eb : b.left = spMap r ≫ jetPt _ hh m) :
    ∃ hq : IsHolFam (fun v => (lift (f v) (h v)).left), (lift a b).left = spMap r ≫ jetPt _ hq m := by
  have hq : IsHolFam (fun v => (lift (f v) (h v)).left) :=
    GlobalTheory.AnVal.isHolFam_pullback_lift _ _ _ P.hom Q.hom _ _ _ x (fun v => Over.w (f v)) (fun v => Over.w (h v)) hf hh
  refine ⟨hq, ?_⟩
  have k1 := jetPt_comp _ hq (fst P Q).left _ hf (fun v => by rw [← Over.comp_left, lift_fst]) m
  have k2 := jetPt_comp _ hq (snd P Q).left _ hh (fun v => by rw [← Over.comp_left, lift_snd]) m
  have l1 : (lift a b).left ≫ (fst P Q).left = (spMap r ≫ jetPt _ hq m) ≫ (fst P Q).left := by
    rw [Category.assoc, k1, ← ea, ← Over.comp_left, lift_fst]
  have l2 : (lift a b).left ≫ (snd P Q).left = (spMap r ≫ jetPt _ hq m) ≫ (snd P Q).left := by
    rw [Category.assoc, k2, ← eb, ← Over.comp_left, lift_snd]
  exact pullback.hom_ext l1 l2
end GlobalTheory.AnValPh1
