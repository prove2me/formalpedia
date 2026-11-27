-- Prove2me | solution 1 for GlobalTheory.AnValSecondLaw.count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:44:43.935229+00:00
-- url     : https://prove2.me/submissions/2c3797d8-de58-48bc-800e-2e754435383b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProducts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameSecondPartialLawTrivial
import Theorems.Thm_GlobalTheory_AnValSecondLaw_sum_two
import Theorems.Thm_GlobalTheory_AnValSecondLaw_sum_three
import Theorems.Thm_GlobalTheory_AnValSecondLaw_psumL_pi

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
open GlobalTheory GlobalTheory.AnValSecondLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
namespace GlobalTheory.AnValSecondLaw
theorem _root_.solution {g : ℕ} (P Q R : (Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (f : ((Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) → ℤ) :
    ∑ I : thK.{0}, thε I * f (psumL 3 g I ∘ₗ LinearMap.pi ![Q, R, P]) =
      ∑ k : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)),
        Sum.elim (cε 2) (Sum.elim (fun k => - cε 2 k) (fun k => - cε 2 k)) k *
        f (Sum.elim (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![P, Q + R])
          (Sum.elim (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![P, Q]) (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![P, R])) k) := by
  rw [sum_three, Fintype.sum_sum_type, Fintype.sum_sum_type, sum_two, sum_two, sum_two]
  simp only [Sum.elim_inl, Sum.elim_inr, psumL_pi]
  simp [thε, cε, Finset.sum_insert, add_comm P, add_assoc]
  ring
end GlobalTheory.AnValSecondLaw
