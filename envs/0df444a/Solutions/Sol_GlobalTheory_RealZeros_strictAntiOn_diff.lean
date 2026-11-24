-- Prove2me | solution 1 for GlobalTheory.RealZeros.strictAntiOn_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:07.345879+00:00
-- url     : https://prove2.me/submissions/5079ff5a-e463-477f-9734-d93aff66fe4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros
namespace GlobalTheory.RealZeros
theorem _root_.solution {σ : ℝ} (h0 : 0 < σ) :
    StrictAntiOn (fun x : ℝ => x ^ (-σ) - (x + 2) ^ (-σ)) (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => x ^ (-σ) - (x + 2) ^ (-σ))
      (-σ * x ^ (-σ - 1) - 1 * -σ * (x + 2) ^ (-σ - 1)) x := fun x hx =>
    (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).sub
      (((hasDerivAt_id x).add_const 2).rpow_const (Or.inl (by simp only [id]; linarith)))
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
  rw [interior_Ioi] at hx
  have hx' : 0 < x := hx
  rw [(hd x hx').deriv]
  have : (x + 2) ^ (-σ - 1) < x ^ (-σ - 1) :=
    Real.rpow_lt_rpow_of_neg hx' (by linarith) (by linarith)
  nlinarith
end GlobalTheory.RealZeros
