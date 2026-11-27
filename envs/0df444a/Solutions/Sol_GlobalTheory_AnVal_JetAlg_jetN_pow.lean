-- Prove2me | solution 1 for GlobalTheory.AnVal.JetAlg.jetN_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:23.638457+00:00
-- url     : https://prove2.me/submissions/8b1ddd1a-5a92-4f70-a860-0f60c6424baa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_jetN_mul
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_jetN_one

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
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetAlg
namespace GlobalTheory.AnVal.JetAlg
theorem _root_.solution {n g : ℕ} (m : ℕ) {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (p : ℕ) :
    jetN m (fun w => f w ^ p) = jetN m f ^ p := by
  induction p with
  | zero =>
    simp only [pow_zero]
    exact jetN_one m
  | succ p ih =>
    have hp : AnO fun w => f w ^ p := by
      unfold AnO at hf ⊢
      exact hf.pow p
    rw [show (fun w => f w ^ (p + 1)) = fun w => f w ^ p * f w from funext fun w => pow_succ (f w) p,
      jetN_mul m hp hf, ih]
    exact (pow_succ _ _).symm
end GlobalTheory.AnVal.JetAlg
