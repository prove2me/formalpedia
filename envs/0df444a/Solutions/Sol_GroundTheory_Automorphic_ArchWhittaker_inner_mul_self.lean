-- Prove2me | solution 1 for GroundTheory.Automorphic.ArchWhittaker.inner_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:44.536573+00:00
-- url     : https://prove2.me/submissions/1ded8785-83a2-49e8-994b-4e075ebb5b3f

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
theorem _root_.solution (z q : ℂ) : inner ℝ z (q * z) = q.re * ‖z‖ ^ 2 := by
  rw [Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring
end GroundTheory.Automorphic.ArchWhittaker
