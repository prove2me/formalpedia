-- Prove2me | solution 1 for MomentComparison.complexNoise_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:23:14.633406+00:00
-- url     : https://prove2.me/submissions/388c8072-85e6-47bd-9f0b-2dc22e37b74c

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_NoisePolynomial
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_walsh_empty
attribute [local simp] MomentComparison.cubeAverage_const
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.walsh_empty



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} (w : ℂ) (f : Cube (n + 1) → ℂ) (b : Bool) (x : Cube n) :
    complexNoise w f (Fin.cons b x) =
      (complexNoise w (fun y => f (Fin.cons true y)) x +
        complexNoise w (fun y => f (Fin.cons false y)) x) / 2 +
      (if b then 1 else -1) * w *
        (complexNoise w (fun y => f (Fin.cons true y)) x -
          complexNoise w (fun y => f (Fin.cons false y)) x) / 2 := by
  simp only [complexNoise, Fin.cons_zero, Fin.tail_cons]
end MomentComparison
