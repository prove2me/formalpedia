-- Prove2me | solution 1 for Nock.NPR.collision_table_prob_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:46.288916+00:00
-- url     : https://prove2.me/submissions/3264376e-4b8e-4a20-a7f2-26b8c3e74925

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_listPoly_nil
public import Theorems.Thm_Nock_NPR_leafF_length
public import Theorems.Thm_P2M_Nock_NPR___fst_7ffdc8e8ea0e
public import Theorems.Thm_P2M_Nock_NPR___snd_fst_ac932a0e2667
public import Theorems.Thm_P2M_Nock_NPR___snd_snd_5ccfc40ae445
public import Theorems.Thm_Nock_NPR_leafF_cell
public import Theorems.Thm_Nock_NPR_collision_table_card_le
attribute [local simp] Nock.NPR.listPoly_nil
attribute [local simp] Nock.NPR.leafF_length
attribute [local simp] Nock.NPR.Φ_fst
attribute [local simp] Nock.NPR.Φ_snd_fst
attribute [local simp] Nock.NPR.Φ_snd_snd
attribute [local simp] Nock.NPR.leafF_cell
section
@[expose] public section
open Polynomial
namespace Nock
namespace NPR
section CPoly
variable {K : Type*} [Field K]
end CPoly
section ListPoly
variable {K : Type*} [Field K]
end ListPoly
section FnLayer
variable {K : Type*} [Field K]
end FnLayer
section Decomp
variable {K : Type*} [Field K]
end Decomp
section SchwartzZippel
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end SchwartzZippel
section Collision
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end Collision
section Table
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
private theorem natCast_mul_pred (k : ℕ) : ((k * (k - 1) : ℕ) : ℚ) = (k : ℚ) * ((k : ℚ) - 1) := by
  rcases k with _ | k
  · simp
  · push_cast; ring
end Table
end NPR
end Nock
end
end

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
      ≤ (((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K))
          * ((s.card : ℚ) * ((s.card : ℚ) - 1) / 2) := by
  have hpos : (0 : ℚ) < Fintype.card K := by
    have : Nonempty K := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  have hcard := collision_table_card_le (K := K) Λ s f hf
  have hne0 : (Fintype.card K : ℚ) ≠ 0 := ne_of_gt hpos
  rw [div_le_iff₀ hpos]
  -- the two `|K|`s cancel; both sides reduce to `k(k−1)·(2Λ−1)`
  have hrhs : (((2 * (2 * Λ - 1) : ℕ) : ℚ) / (Fintype.card K))
        * ((s.card : ℚ) * ((s.card : ℚ) - 1) / 2) * (Fintype.card K)
      = (s.card : ℚ) * ((s.card : ℚ) - 1) * ((2 * Λ - 1 : ℕ) : ℚ) := by
    field_simp
    push_cast
    ring
  rw [hrhs]
  calc ((_ : ℕ) : ℚ) ≤ ((s.card * (s.card - 1) * (2 * Λ - 1) : ℕ) : ℚ) := by exact_mod_cast hcard
    _ = (s.card : ℚ) * ((s.card : ℚ) - 1) * ((2 * Λ - 1 : ℕ) : ℚ) := by
        rw [Nat.cast_mul, natCast_mul_pred]
end Nock.NPR
