-- Prove2me | solution 1 for Nock.NPR.collision_table_prob_le_epsCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:03.69164+00:00
-- url     : https://prove2.me/submissions/87cf9a5c-1c15-4ad8-b895-e46e7ff43d00

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_collision_table_prob_le

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
namespace Nock.NPR
theorem _root_.solution {ι : Type*} (Λ : ℕ)
    (s : Finset ι) (f : ι → Noun) (hf : ∀ i ∈ s, (f i).leaves ≤ Λ) :
    ((Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
        NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
        (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
          ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card : ℚ)
        / (Fintype.card K)
      ≤ epsCol (K := K) Λ * ((s.card : ℚ) * ((s.card : ℚ) - 1) / 2) :=
  collision_table_prob_le Λ s f hf
end Nock.NPR
