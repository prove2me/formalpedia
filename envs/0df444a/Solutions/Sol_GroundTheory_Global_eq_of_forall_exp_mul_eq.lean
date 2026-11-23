-- Prove2me | solution 1 for GroundTheory.Global.eq_of_forall_exp_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:14.295855+00:00
-- url     : https://prove2.me/submissions/fb2a9551-30ae-4d5a-932b-e296cfe70993

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex
namespace GroundTheory.Global
theorem _root_.solution {s s' : ℂ}
    (h : ∀ t : ℝ, Complex.exp (s * t) = Complex.exp (s' * t)) : s = s' := by
  have hd : ∀ u : ℂ, HasDerivAt (fun t : ℝ => Complex.exp (u * t)) u 0 := by
    intro u
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul u).cexp
    simpa using this
  have e : (fun t : ℝ => Complex.exp (s * t)) = fun t : ℝ => Complex.exp (s' * t) := funext h
  have h' : HasDerivAt (fun t : ℝ => Complex.exp (s * t)) s' 0 := by rw [e]; exact hd s'
  exact (hd s).unique h'
end GroundTheory.Global
