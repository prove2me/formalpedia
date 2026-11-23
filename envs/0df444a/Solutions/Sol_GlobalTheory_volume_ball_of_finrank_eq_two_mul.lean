-- Prove2me | solution 1 for GlobalTheory.volume_ball_of_finrank_eq_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:29.956124+00:00
-- url     : https://prove2.me/submissions/7d1d8d52-28bf-430b-826c-6bf784b47305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set
open scoped ENNReal Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution {D : ℕ} (hD : Module.finrank ℝ E = 2 * D) (a : E)
    {r : ℝ} (hr : 0 < r) :
    volume (ball a r) = ENNReal.ofReal (π ^ D * r ^ (2 * D) / D.factorial) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hD0 : D = 0 := by
      rw [Module.finrank_zero_of_subsingleton] at hD
      omega
    have h : ball a r = parallelepiped (stdOrthonormalBasis ℝ E) := by
      ext z
      rw [Subsingleton.elim z a]
      simp only [mem_ball_self hr, true_iff, mem_parallelepiped_iff]
      exact ⟨0, by simp, Subsingleton.elim _ _⟩
    rw [h, OrthonormalBasis.volume_parallelepiped, hD0]
    simp
  · rw [InnerProductSpace.volume_ball_of_dim_even hD, hD, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
end GlobalTheory
