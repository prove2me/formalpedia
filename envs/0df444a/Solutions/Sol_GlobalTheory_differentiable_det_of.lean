-- Prove2me | solution 1 for GlobalTheory.differentiable_det_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:19.5288+00:00
-- url     : https://prove2.me/submissions/501b3f9f-0b99-4f1f-98ad-440f3df0ff00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrameSectionSliceEqPolyDivDetPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {r : ℕ} :
    Differentiable ℂ (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det) := by
  have : (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det) =
      fun y => ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) * ∏ i, y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    simp [Matrix.of_apply]
  rw [this]
  fun_prop
end GlobalTheory
