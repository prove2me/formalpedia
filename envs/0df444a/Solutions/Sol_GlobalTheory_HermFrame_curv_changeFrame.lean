-- Prove2me | solution 1 for GlobalTheory.HermFrame.curv_changeFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:54.843602+00:00
-- url     : https://prove2.me/submissions/50652650-e473-4f38-bdcf-fe69d7768cb2

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_mul
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_inv
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_mdel
import Theorems.Thm_GlobalTheory_HermFrame_mdel_mdbar
import Theorems.Thm_GlobalTheory_HermFrame_conn_changeFrame
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_IsPshC2On_add
import Theorems.Thm_GlobalTheory_IsPshC2On_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n]
variable {U : Set E} {H H' : E → Matrix n n ℂ} {z : E} {j k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution {A : E → Matrix n n ℂ} (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 2 A z) (hAu : IsUnit (A z).det) (hA0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar A x η = 0)
    (ξ η : E) : curv (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) z ξ η = (A z)⁻¹ * curv H z ξ η * A z := by
  have he : (fun x => conn (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) x ξ) =ᶠ[𝓝 z]
      fun x => (A x)⁻¹ * (conn H x ξ * A x + mdel A x ξ) := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu, hA.eventually_two,
      hA.eventually_isUnit hAu, hA0] with x h1 h2 h3 h4 h5
    exact conn_changeFrame (h1.of_le one_le_two) h2 (h3.of_le one_le_two) h4 h5 ξ
  have hA1 : MContDiffAt 1 A z := hA.of_le one_le_two
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have hd : MContDiffAt 1 (fun x => mdel A x ξ) z := hA.mdel (by norm_num) ξ
  have h0 : mddbar A z ξ η = 0 := by
    rw [← mdel_mdbar hA, mdel_congr (B := fun _ => 0) (hA0.mono fun x hx => hx η), mdel_const]
  rw [curv, mdbar_congr he, mdbar_mul (hA1.inv hAu) ((hc.mul hA1).add hd), mdbar_inv hA1 hAu,
    mdbar_add (hc.mul hA1) hd, mdbar_mul hc hA1, mdbar_mdel hA, h0, hA0.self_of_nhds, curv]
  simp [Matrix.mul_assoc]
end GlobalTheory.HermFrame
