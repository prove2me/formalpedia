-- Prove2me | solution 1 for Nock.NPR.epsCol_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:59.686173+00:00
-- url     : https://prove2.me/submissions/81d46c2c-0ddd-4cc2-b223-63bf678fbe47

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
omit [Field K] [DecidableEq K]
namespace Nock.NPR
theorem _root_.solution {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    epsCol (K := K) Λ = 2 * (2 * (Λ : ℚ) - 1) / (Fintype.card K) := by
  unfold epsCol
  have h1 : (1 : ℕ) ≤ 2 * Λ := by omega
  rw [Nat.cast_mul]
  congr 1
  push_cast [Nat.cast_sub h1]
  ring
end Nock.NPR
