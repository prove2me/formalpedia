-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ConstCoeffODE.stepMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:38:11.907127+00:00
-- url     : https://prove2.me/submissions/40584f93-6a8c-4af2-a562-692dc07ecae1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialPolynomialSolutionSpace
import Theorems.Thm_GlobalTheory_CompanionTheory_ConstCoeffODE_eq_zero_of_op_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ConstCoeffODE
namespace GlobalTheory.CompanionTheory.ConstCoeffODE
theorem _root_.solution (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) :
    Function.Injective (stepMap c S) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have h1 : op c y.1 = 0 := congrArg (fun p : S × ℂ => (p.1 : ℝ → ℂ)) hy
  have h2 : y.1 0 = 0 := congrArg Prod.snd hy
  exact Subtype.ext (eq_zero_of_op_eq_zero c y.2.1 h1 h2)
end GlobalTheory.CompanionTheory.ConstCoeffODE
