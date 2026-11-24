-- Prove2me | solution 1 for MomentComparison.complexNoise_one_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:41.040932+00:00
-- url     : https://prove2.me/submissions/03e6935d-c58e-4641-a5d1-e456cadd87e9

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_NoisePolynomial
public import Theorems.Thm_MomentComparison_complexNoise_ofReal
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_walshExpansion
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
theorem _root_.solution {n : ℕ} (f : Cube n → ℝ) (x : Cube n) :
    complexNoise 1 (fun y => (f y : ℂ)) x = (f x : ℂ) := by
  rw [complexNoise_ofReal]
  simp only [one_pow, one_mul]
  exact_mod_cast walshExpansion f x
end MomentComparison
