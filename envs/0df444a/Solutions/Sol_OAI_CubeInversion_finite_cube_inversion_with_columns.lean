-- Prove2me | solution 1 for OAI.CubeInversion.finite_cube_inversion_with_columns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:17:36.393495+00:00
-- url     : https://prove2.me/submissions/0f8f9c71-d699-4cdd-904f-f7a81159a6f0

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Theorems.Thm_OAI_CubeInversion_finite_cube_inversion

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.CubeInversion
namespace OAI.CubeInversion
theorem _root_.solution {N : Type*} [DecidableEq N]
    (columns : Finset N) (S : Finset ℕ) (hS : 1 ∈ S)
    (a : N → ℂ) (c : ℕ → ℂ) (W : N → ℕ → ℂ)
    (hc : ∀ x y, c (x * y) = c x * c y) :
    (∑ n ∈ columns, a n *
      (∑ m ∈ S, ∑ h ∈ m.divisors,
        (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W n m)) =
      ∑ n ∈ columns, a n * (c 1 * W n 1) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [finite_cube_inversion S hS c (W n) hc]
end OAI.CubeInversion
