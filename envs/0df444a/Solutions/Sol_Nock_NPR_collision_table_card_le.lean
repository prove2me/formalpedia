-- Prove2me | solution 1 for Nock.NPR.collision_table_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:10.671366+00:00
-- url     : https://prove2.me/submissions/b998a26d-73c2-4c0b-9758-f0e97819185c

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
public import Theorems.Thm_Nock_NPR_collision_card_le_tight
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
private theorem sq_sub_self (k : ℕ) : k * k - k = k * (k - 1) := by
  cases k with
  | zero => rfl
  | succ n => rw [Nat.succ_sub_one, Nat.mul_succ]; omega
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
    (Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
        NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
        (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
          ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card
      ≤ s.card * (s.card - 1) * (2 * Λ - 1) := by
  classical
  set g : ι × ι → Finset K := fun ij =>
    Finset.univ.filter (fun r : K => NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
      (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
        ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2))) with hg
  have hsub : (Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
      NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
      (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
        ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2))))
      ⊆ s.offDiag.biUnion g := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨ij, hij, hcol, hdi⟩ := hr.2
    refine Finset.mem_biUnion.mpr ⟨ij, hij, ?_⟩
    simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hcol, hdi⟩
  have hcard : ∀ ij ∈ s.offDiag, (g ij).card ≤ 2 * Λ - 1 := by
    intro ij hij
    obtain ⟨hi, hj, _⟩ := Finset.mem_offDiag.mp hij
    by_cases hd : (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
        ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2))
    · -- distinct: bound by the single-pair collision count
      refine le_trans (Finset.card_le_card ?_)
        (collision_card_le_tight Λ (f ij.1) (f ij.2) (hf _ hi) (hf _ hj) hd)
      intro r hr
      simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact hr.1
    · -- equal field-nouns: the filtered set is empty
      have hempty : g ij = ∅ := by
        simp only [hg, Finset.filter_eq_empty_iff]
        intro r _
        rintro ⟨_, hdiff⟩
        exact hd hdiff
      rw [hempty]; simp
  calc (Finset.univ.filter (fun r : K => ∃ ij ∈ s.offDiag,
          NPR.fn (f ij.1) r = NPR.fn (f ij.2) r ∧
          (NPR.leafF (K := K) (f ij.1), NPR.dyckBits (K := K) (f ij.1))
            ≠ (NPR.leafF (K := K) (f ij.2), NPR.dyckBits (K := K) (f ij.2)))).card
      ≤ (s.offDiag.biUnion g).card := Finset.card_le_card hsub
    _ ≤ ∑ _ij ∈ s.offDiag, (2 * Λ - 1) :=
        le_trans Finset.card_biUnion_le (Finset.sum_le_sum hcard)
    _ = s.offDiag.card * (2 * Λ - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ = s.card * (s.card - 1) * (2 * Λ - 1) := by
        rw [Finset.offDiag_card, sq_sub_self]
end Nock.NPR
