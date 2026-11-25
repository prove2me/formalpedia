-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.TopClose.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:54.80334+00:00
-- url     : https://prove2.me/submissions/5273cea7-2a95-4b0c-8883-295218f8f2d9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_TopClose_one
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_TopClose_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial Finset
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
namespace TopClose
theorem _root_.solution {k : ℕ} {a b : MvPolynomial (Fin n) ℂ} (h : TopClose k a b) (c : ℕ) :
    TopClose (c * k) (a ^ c) (b ^ c) := by
  induction c with
  | zero => simpa using TopClose.one
  | succ c ih =>
    rw [pow_succ, pow_succ, Nat.succ_mul]
    exact ih.mul h
end TopClose
end GroundTheory.Automorphic.HarishChandra
