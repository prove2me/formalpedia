-- Prove2me | solution 1 for Nock.NPR.collision_card_le_tight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:35.299911+00:00
-- url     : https://prove2.me/submissions/99fe97a0-2f90-4378-90f8-00c59447d8bc

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_listPoly_sub_ne_zero
public import Theorems.Thm_Nock_NPR_listPoly_sub_natDegree_le
public import Theorems.Thm_Nock_NPR_listPoly_nil
public import Theorems.Thm_Nock_NPR_leafF_length
public import Theorems.Thm_Nock_NPR_dyckBits_length
public import Theorems.Thm_P2M_Nock_NPR___fst_7ffdc8e8ea0e
public import Theorems.Thm_P2M_Nock_NPR___snd_fst_ac932a0e2667
public import Theorems.Thm_P2M_Nock_NPR___snd_snd_5ccfc40ae445
public import Theorems.Thm_Nock_NPR_leafF_cell
public import Theorems.Thm_Nock_NPR_card_eval_zero_le
public import Theorems.Thm_Nock_Noun_one_le_leaves

attribute [local simp] Nock.NPR.listPoly_nil
attribute [local simp] Nock.NPR.leafF_length
attribute [local simp] Nock.NPR.Φ_fst
attribute [local simp] Nock.NPR.Φ_snd_fst
attribute [local simp] Nock.NPR.Φ_snd_snd
attribute [local simp] Nock.NPR.leafF_cell

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
    (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card ≤ 2 * Λ - 1 := by
  have hΛ : 1 ≤ Λ := le_trans n₁.one_le_leaves h₁
  -- reduce to: some difference polynomial `P` is nonzero, deg ≤ 2Λ−1, and collision ⟹ root
  suffices h : ∃ P : K[X], P ≠ 0 ∧ P.natDegree ≤ 2 * Λ - 1 ∧
      (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)) ⊆
      (Finset.univ.filter (fun r : K => P.eval r = 0)) by
    obtain ⟨P, hPne, hPdeg, hPsub⟩ := h
    calc (Finset.univ.filter (fun r : K => NPR.fn n₁ r = NPR.fn n₂ r)).card
        ≤ (Finset.univ.filter (fun r : K => P.eval r = 0)).card := Finset.card_le_card hPsub
      _ ≤ P.natDegree := card_eval_zero_le P hPne
      _ ≤ 2 * Λ - 1 := hPdeg
  by_cases hlam : n₁.leaves = n₂.leaves
  · -- equal length λ: distinguished by the leaf poly or the dyck poly
    simp only [ne_eq, Prod.mk.injEq, not_and_or] at hne
    rcases hne with hd | hd
    · -- leaf arrays differ (equal length λ)
      refine ⟨listPoly (NPR.leafF n₁) - listPoly (NPR.leafF n₂), ?_, ?_, ?_⟩
      · exact NPR.listPoly_sub_ne_zero (by simp [hlam]) hd
      · refine le_trans (NPR.listPoly_sub_natDegree_le (by simp [hlam])) ?_
        rw [NPR.leafF_length]; omega
      · intro r hr
        rw [Finset.mem_filter] at hr ⊢
        refine ⟨hr.1, ?_⟩
        have := congrArg (fun x => x.2.1) hr.2
        simp only [NPR.fn] at this
        rw [eval_sub, sub_eq_zero]; exact this
    · -- dyck words differ (equal length 2(λ−1))
      refine ⟨listPoly (NPR.dyckBits n₁) - listPoly (NPR.dyckBits n₂), ?_, ?_, ?_⟩
      · refine NPR.listPoly_sub_ne_zero ?_ hd
        have e1 := NPR.dyckBits_length (K := K) n₁
        have e2 := NPR.dyckBits_length (K := K) n₂
        omega
      · refine le_trans (NPR.listPoly_sub_natDegree_le ?_) ?_
        · have e1 := NPR.dyckBits_length (K := K) n₁
          have e2 := NPR.dyckBits_length (K := K) n₂
          omega
        · have e1 := NPR.dyckBits_length (K := K) n₁
          omega
      · intro r hr
        rw [Finset.mem_filter] at hr ⊢
        refine ⟨hr.1, ?_⟩
        have := congrArg (fun x => x.2.2) hr.2
        simp only [NPR.fn] at this
        rw [eval_sub, sub_eq_zero]; exact this
  · -- lengths differ: distinguished by the first component X^{λ}
    refine ⟨X ^ n₁.leaves - X ^ n₂.leaves, ?_, ?_, ?_⟩
    · intro h
      have hcoeff := congrArg (fun q => Polynomial.coeff q n₁.leaves) h
      simp only [coeff_sub, coeff_X_pow, coeff_zero, if_neg hlam, sub_zero] at hcoeff
      exact one_ne_zero hcoeff
    · refine le_trans (natDegree_sub_le _ _) ?_
      rw [natDegree_X_pow, natDegree_X_pow, max_le_iff]; omega
    · intro r hr
      rw [Finset.mem_filter] at hr ⊢
      refine ⟨hr.1, ?_⟩
      have := congrArg (fun x => x.1) hr.2
      simp only [NPR.fn] at this
      rw [eval_sub, eval_X_pow, eval_X_pow, sub_eq_zero]; exact this
end Nock.NPR
