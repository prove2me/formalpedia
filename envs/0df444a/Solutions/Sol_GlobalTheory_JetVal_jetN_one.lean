-- Prove2me | solution 1 for GlobalTheory.JetVal.jetN_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:37:07.827347+00:00
-- url     : https://prove2.me/submissions/bcc2d261-8636-4372-9c9f-5d70875b9cdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsValueAtJetPointCmFrameSection
import Theorems.Thm_GlobalTheory_JetVal_anLin_onePr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anJetMap_comp
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
open GlobalTheory GlobalTheory.JetVal
open AlgebraicGeometry CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetVal
theorem _root_.solution {g : ℕ} (m : ℕ) {f : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) :
    jetN (n := 1) m (fun w => f (w 0)) = jetOf m f := by
  have h1 : (fun v => (fun w : Fin 1 → Fin g → ℂ => f (w 0)) (colsOf 1 g v)) = f ∘ onePr g := rfl
  rw [jetN, h1, jetOf_comp_anLin m hf, renN,
    anJetMap_comp _ _ _ _ (fun p => MvPolynomial.X p) (fun _ => X_mem_orig _) (fun p => by
      obtain ⟨a, j⟩ := p
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      simp only [anLin_onePr, MvPolynomial.aeval_X, Equiv.symm_apply_apply])]
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (jetOf m f)
  rw [← hp]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval MvPolynomial.X p) = _
  rw [MvPolynomial.aeval_X_left_apply]
end GlobalTheory.JetVal
