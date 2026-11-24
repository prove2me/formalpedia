-- Prove2me | solution 1 for GlobalTheory.HermFrame.conjTranspose_mddbar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:39:44.191443+00:00
-- url     : https://prove2.me/submissions/660cc626-9a50-4d04-a084-711949617bb1

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Theorems.Thm_GlobalTheory_IsPshC2On_mono
import Theorems.Thm_GlobalTheory_ddbar_congr


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
theorem _root_.solution {A : E → Matrix n n ℂ} (h2 : MContDiffAt 2 A z)
    (h : ∀ᶠ x in 𝓝 z, (A x).IsHermitian) (ξ η : E) : (mddbar A z ξ η)ᴴ = mddbar A z η ξ := by
  ext a b
  rw [conjTranspose_apply, mddbar_apply, mddbar_apply, star_def, ← ddbar_conj (h2 b a),
    ddbar_congr (u := fun x => conj (A x b a)) (u' := fun x => A x a b)
      (h.mono fun x hx => hx.apply a b)]
end GlobalTheory.HermFrame
