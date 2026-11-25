-- Prove2me | solution 1 for GlobalTheory.subgroup_gaussian_tail_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:18.107953+00:00
-- url     : https://prove2.me/submissions/b0e3f974-2e07-42bd-93bd-e69682871ccc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
import Theorems.Thm_GlobalTheory_gaussian_tail_addMonoidHom_sixteen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution (G : AddSubgroup E) {g : ℕ} (hg : finrank ℝ E = 2 * g)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : 16 * (2 * (g : ℝ) + 1) ≤ R ^ 2)
    (hG : ∀ x ∈ G, x ≠ 0 → R ≤ ‖x‖) :
    Summable (fun x : {x : G // x ≠ 0} => exp (-‖(x.1 : E)‖ ^ 2 / 16)) ∧
      ∑' x : {x : G // x ≠ 0}, exp (-‖(x.1 : E)‖ ^ 2 / 16) ≤ 2 * 9 ^ g * exp (-R ^ 2 / 16) :=
  gaussian_tail_addMonoidHom_sixteen G.subtype hg hR0 hR fun y hy =>
    hG y y.2 fun h => hy (Subtype.ext h)
end GlobalTheory
