-- Prove2me | solution 1 for GroundTheory.Automorphic.ArchWhittaker.wronskian_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:56.629951+00:00
-- url     : https://prove2.me/submissions/3701ef81-2a3a-4549-b380-e5568a88340a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set
namespace GroundTheory.Automorphic.ArchWhittaker
theorem _root_.solution {q f f' g g' : ℝ → ℂ}
    (hf : ∀ y > 0, HasDerivAt f (f' y) y) (hf' : ∀ y > 0, HasDerivAt f' (q y * f y) y)
    (hg : ∀ y > 0, HasDerivAt g (g' y) y) (hg' : ∀ y > 0, HasDerivAt g' (q y * g y) y)
    (hf0 : Tendsto f atTop (𝓝 0)) (hf0' : Tendsto f' atTop (𝓝 0))
    (hg0 : Tendsto g atTop (𝓝 0)) (hg0' : Tendsto g' atTop (𝓝 0)) :
    ∀ y > 0, f y * g' y - f' y * g y = 0 := by
  set W : ℝ → ℂ := fun y => f y * g' y - f' y * g y with hW
  have hWd : ∀ y > 0, HasDerivAt W 0 y := by
    intro y hy
    have := ((hf y hy).mul (hg' y hy)).sub ((hf' y hy).mul (hg y hy))
    refine this.congr_deriv ?_
    ring
  have hconst : ∀ y > 0, W y = W 1 := by
    intro y hy
    exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun z hz => (hWd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hWd z hz).deriv) hy (mem_Ioi.2 one_pos)
  have hlim : Tendsto W atTop (𝓝 0) := by
    have := (hf0.mul hg0').sub (hf0'.mul hg0)
    simpa using this
  have hlim' : Tendsto W atTop (𝓝 (W 1)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop 0] with y hy
      exact (hconst y hy).symm)
  have h1 : W 1 = 0 := tendsto_nhds_unique hlim' hlim
  intro y hy
  show W y = 0
  rw [hconst y hy, h1]
end GroundTheory.Automorphic.ArchWhittaker
