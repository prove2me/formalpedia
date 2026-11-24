-- Prove2me | solution 1 for GlobalTheory.RealZeros.hasSum_group
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:38.906461+00:00
-- url     : https://prove2.me/submissions/78358ee2-7469-4316-ae2b-bf1da84c7e23

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
theorem _root_.solution {f : ℕ → ℂ} {a : ℂ} (N : ℕ) [NeZero N] (h : HasSum f a) :
    HasSum (fun k => ∑ j : Fin N, f (N * k + j)) a := by
  have h1 := (Nat.divModEquiv N).symm.hasSum_iff.mpr h
  refine h1.prod_fiberwise (fun k => ?_)
  have := hasSum_fintype (fun j : Fin N => f (N * k + j))
  simpa [mul_comm] using this
end GlobalTheory.RealZeros
