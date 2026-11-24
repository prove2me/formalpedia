-- Prove2me | solution 1 for GlobalTheory.StepData.mem_iter_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:15:42.516202+00:00
-- url     : https://prove2.me/submissions/87f02e59-4d16-4e87-a5b8-8c5babcdd8fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IterPrincipalSpec
import Theorems.Thm_GlobalTheory_StepData_reGL_symm_mem_KO
import Theorems.Thm_GlobalTheory_StepData_blk_ixSucc_inl
import Theorems.Thm_GlobalTheory_StepData_blk_ixSucc_inr
import Theorems.Thm_GlobalTheory_StepData_Ix_blk_le
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_Level_mem_map
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_iter_succ
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_iter_zero
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_step_J
import Theorems.Thm_GlobalTheory_StepData_exists_diag_blocks
import Theorems.Thm_GlobalTheory_StepData_mem_KOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.StepData ValuativeRel Matrix
namespace GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
private theorem mem_reindex_J_iff {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (P : TypeDatum k a) (e : a ≃ b) (g : GL b k) : g ∈ (P.reindex e).J ↔ (reGL e).symm g ∈ P.J :=
  Level.mem_map
end GlobalTheory.StepData
end

set_option autoImplicit false
open GlobalTheory.StepData ValuativeRel Matrix
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData
theorem _root_.solution (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : GL (Ix r t j) k) :
    g ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ g ∈ KO k (Ix r t j) ∧
      (∀ a b : Ix r t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧ MaxM (g.val.toBlocks₁₁ - 1) := by
  revert g
  induction j with
  | zero =>
    intro g
    rw [TypeDatum.iter_zero, mem_reindex_J_iff]
    change (reGL (ixZero r t)).symm g ∈ KOne k r ↔ _
    have e0 : ((reGL (ixZero r t)).symm g).val - 1 = g.val.toBlocks₁₁ - 1 := by
      rw [reGL_symm_val]; rfl
    constructor
    · intro hg
      refine ⟨(reGL_symm_mem_KO (ixZero r t) g).1 (KOne_le_KO hg), ?_, ?_⟩
      · intro a b hab
        exfalso
        rcases a with x | ⟨i, _⟩
        · exact Nat.not_lt_zero _ hab
        · exact i.elim0
      · rw [← e0]; exact mem_KOne.1 hg
    · rintro ⟨-, -, h1⟩
      rw [mem_KOne, e0]; exact h1
  | succ j ih =>
    intro g
    rw [TypeDatum.iter_succ, mem_reindex_J_iff, TypeDatum.step_J, TypeDatum.mem_stepJ_iff, reGL_symm_mem_KO]
    have hv : ∀ x y, ((reGL (ixSucc r t j)).symm g).val x y = g.val (ixSucc r t j x) (ixSucc r t j y) := by
      intro x y; rw [reGL_symm_val]; rfl
    constructor
    · rintro ⟨hK, ⟨g', hg', e'⟩, h21⟩
      obtain ⟨-, hlow, h11⟩ := (ih g').1 hg'
      have hg'v : ∀ x y, g'.val x y = g.val (ixSucc r t j (.inl x)) (ixSucc r t j (.inl y)) := by
        intro x y; rw [e']; exact hv (.inl x) (.inl y)
      refine ⟨hK, ?_, ?_⟩
      · intro a b hab
        obtain ⟨x, rfl⟩ := (ixSucc r t j).surjective a
        obtain ⟨y, rfl⟩ := (ixSucc r t j).surjective b
        rcases x with x | s <;> rcases y with y | s'
        · rw [← hg'v]
          rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          exact hlow x y hab
        · rw [blk_ixSucc_inr, blk_ixSucc_inl] at hab
          have := Ix.blk_le x
          omega
        · rw [← hv]; exact h21 s y
        · rw [blk_ixSucc_inr, blk_ixSucc_inr] at hab
          omega
      · have hb : g'.val.toBlocks₁₁ = g.val.toBlocks₁₁ := by
          ext i i'; exact hg'v (.inl i) (.inl i')
        rw [← hb]; exact h11
    · rintro ⟨hK, hlow, h11⟩
      have hK' : (reGL (ixSucc r t j)).symm g ∈ KO k (Ix r t j ⊕ t) := (reGL_symm_mem_KO _ g).2 hK
      have h21 : MaxM ((reGL (ixSucc r t j)).symm g).val.toBlocks₂₁ := by
        intro s y
        show valuation k (((reGL (ixSucc r t j)).symm g).val (.inr s) (.inl y)) < 1
        rw [hv]
        apply hlow
        rw [blk_ixSucc_inr, blk_ixSucc_inl]
        exact Nat.lt_succ_of_le (Ix.blk_le y)
      refine ⟨hK, ?_, h21⟩
      obtain ⟨⟨g', hg'K, e'⟩, -⟩ := exists_diag_blocks hK' h21
      refine ⟨g', (ih g').2 ⟨hg'K, ?_, ?_⟩, e'⟩
      · intro x y hxy
        rw [e']
        show valuation k (((reGL (ixSucc r t j)).symm g).val (.inl x) (.inl y)) < 1
        rw [hv]
        apply hlow
        rwa [blk_ixSucc_inl, blk_ixSucc_inl]
      · have hb : g'.val.toBlocks₁₁ = g.val.toBlocks₁₁ := by
          ext i i'
          rw [e']
          exact hv (.inl (.inl i)) (.inl (.inl i'))
        rw [hb]; exact h11
end GlobalTheory.StepData
