-- Prove2me | solution 1 for GlobalTheory.HermFrame.conjTranspose_mdel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:00.613693+00:00
-- url     : https://prove2.me/submissions/4489b4f4-c53b-41da-b5aa-da71fd82688c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_HermFrame_mdbar_conjTranspose
import Theorems.Thm_GlobalTheory_IsPshC2On_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable {A B : E → Matrix m n ℂ} {z : E} {j k : WithTop ℕ∞}
namespace GlobalTheory.HermFrame
theorem _root_.solution {A : E → Matrix n n ℂ} (h : ∀ᶠ x in 𝓝 z, (A x).IsHermitian) (ξ : E) :
    (mdel A z ξ)ᴴ = mdbar A z ξ := by
  rw [← mdbar_conjTranspose]; exact mdbar_congr (h.mono fun x hx => hx.eq) ξ
end GlobalTheory.HermFrame
