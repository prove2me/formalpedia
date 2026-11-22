-- Prove2me | solution 1 for Nock.NPR.collision_prob_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:45.835545+00:00
-- url     : https://prove2.me/submissions/bc540a85-ab3b-4189-af6b-0dc431833203

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_collision_card_le

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
namespace Nock.NPR
theorem _root_.solution (Λ : ℕ) (n₁ n₂ : Noun)
    (h₁ : n₁.leaves ≤ Λ) (h₂ : n₂.leaves ≤ Λ)
    (hne : (NPR.leafF (K := K) n₁, NPR.dyckBits (K := K) n₁)
         ≠ (NPR.leafF (K := K) n₂, NPR.dyckBits (K := K) n₂)) :
    ((Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card : ℚ)
        / (Fintype.card K)
      ≤ ((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K) := by
  have hpos : (0 : ℚ) < Fintype.card K := by
    have : Nonempty K := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff_of_pos_right hpos]
  exact_mod_cast collision_card_le Λ n₁ n₂ h₁ h₂ hne
end Nock.NPR
