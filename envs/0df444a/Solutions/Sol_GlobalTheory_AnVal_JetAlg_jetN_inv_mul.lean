-- Prove2me | solution 1 for GlobalTheory.AnVal.JetAlg.jetN_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:17.005559+00:00
-- url     : https://prove2.me/submissions/52d942e1-6b23-492c-9cee-7bc329a113b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_jetN_mul
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_jetN_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_taylor_multiplication


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
theorem _root_.solution {n g : ℕ} (m : ℕ) {f : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (h0 : f (colsOf n g 0) ≠ 0) :
    jetN m (fun w => (f w)⁻¹) * jetN m f = 1 := by
  have hf' : ContDiffAt ℂ ω (fun v => f (colsOf n g v)) 0 := hf
  have hinv : AnO fun w => (f w)⁻¹ := hf'.inv h0
  rw [← jetN_mul m hinv hf]
  have hev : (fun v => (f (colsOf n g v))⁻¹ * f (colsOf n g v)) =ᶠ[nhds 0] fun _ => (1 : ℂ) := by
    filter_upwards [hf'.continuousAt.eventually_ne h0] with v hv
    exact inv_mul_cancel₀ hv
  have h1 := jetN_one (n := n) (g := g) m
  simp only [jetN, jetOf] at h1 ⊢
  rw [TM.taylor_multiplication.2.2 _ _ _ hev]
  exact h1
end GlobalTheory.AnVal.JetAlg
