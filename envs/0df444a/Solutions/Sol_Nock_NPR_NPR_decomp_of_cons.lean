-- Prove2me | solution 1 for Nock.NPR.NPR_decomp_of_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:55.424389+00:00
-- url     : https://prove2.me/submissions/0d98494e-aebf-4342-9d3c-bbfa6239f8aa

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_NPR_decomp

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution {n nL nR : Noun} (h : n = Noun.cell nL nR) :
    (Φ (K := K) n).1 = (Φ (K := K) nL).1 * (Φ (K := K) nR).1
    ∧ (Φ (K := K) n).2.1 = (Φ (K := K) nL).2.1 + X ^ nL.leaves * (Φ (K := K) nR).2.1
    ∧ (Φ (K := K) n).2.2 = X * (Φ (K := K) nL).2.2 + X ^ (2 * nL.leaves - 1)
        + X ^ (2 * nL.leaves) * (Φ (K := K) nR).2.2 :=
  (NPR_decomp n nL nR).mp (by rw [h])
end Nock.NPR
