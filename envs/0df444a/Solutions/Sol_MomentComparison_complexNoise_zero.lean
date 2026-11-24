-- Prove2me | solution 1 for MomentComparison.complexNoise_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:37:24.62941+00:00
-- url     : https://prove2.me/submissions/197a6792-bc05-472e-97c0-3f76618e7d4f

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_NoisePolynomial

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution (w : ℂ) (f : Cube 0 → ℂ) (x : Cube 0) :
    complexNoise w f x = f x := rfl
end MomentComparison
