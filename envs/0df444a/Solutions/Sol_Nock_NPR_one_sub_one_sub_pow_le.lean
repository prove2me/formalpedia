-- Prove2me | solution 1 for Nock.NPR.one_sub_one_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:04.228831+00:00
-- url     : https://prove2.me/submissions/846df843-a65f-486f-8e91-8b5e908a61a5

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
namespace Nock.NPR
theorem _root_.solution (ε : ℚ) (hε : ε ≤ 2) (m : ℕ) :
    1 - (1 - ε) ^ m ≤ (m : ℚ) * ε := by
  have hb := one_add_mul_le_pow (a := -ε) (by linarith) m
  have hmul : (m : ℚ) * (-ε) = -((m : ℚ) * ε) := by ring
  have h1 : (1 : ℚ) + -ε = 1 - ε := by ring
  rw [hmul, h1] at hb
  linarith
end Nock.NPR
