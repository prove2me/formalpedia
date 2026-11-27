-- Prove2me | solution 1 for GlobalTheory.AnVal.jetCopy_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:16:26.403124+00:00
-- url     : https://prove2.me/submissions/96679845-5906-4ec8-8931-005e7837a56e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets

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
namespace GlobalTheory.AnVal
theorem _root_.solution (g m : ℕ) (a : Jet ℂ (Fin 1 × Fin g) m) : jetCopy (S := ℂ) g m (0 : Fin 1) a = a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  show Ideal.Quotient.mk _ (MvPolynomial.aeval (fun q : Fin 1 × Fin g =>
    (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) p) = _
  have h : (fun q : Fin 1 × Fin g => (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) =
      MvPolynomial.X := by
    funext q
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h, MvPolynomial.aeval_X_left_apply]
end GlobalTheory.AnVal
