-- Prove2me | solution 1 for GlobalTheory.SymChain.IterPattern.step_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:49.537799+00:00
-- url     : https://prove2.me/submissions/49b15a2b-7e82-4515-9977-3cd5aadd18ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPatternStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Theorems.Thm_GlobalTheory_SymChain_IterPattern_symm_mem_KO_iff
import Theorems.Thm_GlobalTheory_SymChain_IterPattern_mem_reindex_J
import Theorems.Thm_GlobalTheory_SymChain_IterPattern_free_ll
import Theorems.Thm_GlobalTheory_SymChain_IterPattern_free_lr
import Theorems.Thm_GlobalTheory_SymChain_IterPattern_not_free_rl
import Theorems.Thm_GlobalTheory_SymChain_IterPattern_free_rr
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_step_J
import Theorems.Thm_GlobalTheory_StepData_exists_diag_blocks


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.IterPattern
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ρ κ l j : ℕ} {t : Type}
variable [Fintype t] [DecidableEq t]
namespace GlobalTheory.SymChain.IterPattern
theorem _root_.solution (Q : TypeDatum k (Ix (Fin κ ⊕ Fin l) t j)) (μ : kˣ →* ℂˣ) (hμ : IsTame μ)
    (hQ : ∀ g : GL (Ix (Fin κ ⊕ Fin l) t j) k, g ∈ Q.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (g : GL (Ix (Fin κ ⊕ Fin l) t (j + 1)) k) :
    g ∈ ((Q.step t μ hμ).reindex (ixSucc _ t j)).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  rw [mem_reindex_J, TypeDatum.step_J, TypeDatum.mem_stepJ_iff, symm_mem_KO_iff]
  constructor
  · rintro ⟨hK, ⟨g', hg', hval⟩, hC⟩
    refine ⟨hK, fun a b hab => ?_⟩
    obtain ⟨a, rfl⟩ := (ixSucc _ t j).surjective a
    obtain ⟨b, rfl⟩ := (ixSucc _ t j).surjective b
    rcases a with x | s <;> rcases b with y | s'
    ·
      have hxy : ¬ FreeIx ρ x y := fun h => hab ((free_ll x y).2 h)
      have hold := ((hQ g').1 hg').2 x y hxy
      have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by
        rw [hval, reGL_symm_val]; rfl
      rw [hentry] at hold
      simpa [Matrix.one_apply] using hold
    · exact absurd (free_lr x s') hab
    ·
      have hlow := hC s y
      simpa [Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁] using hlow
    · exact absurd (free_rr s s') hab
  · rintro ⟨hK, hfree⟩
    have hK' : (reGL (ixSucc _ t j)).symm g ∈ KO k _ := (symm_mem_KO_iff _ g).2 hK
    have hC : MaxM ((reGL (ixSucc _ t j)).symm g).val.toBlocks₂₁ := by
      intro s y
      have hnf := hfree _ _ (not_free_rl s y)
      simpa [Matrix.one_apply, reGL_symm_val, Matrix.toBlocks₂₁] using hnf
    refine ⟨hK, ?_, hC⟩
    obtain ⟨⟨g', hg'K, hg'val⟩, -⟩ := exists_diag_blocks hK' hC
    refine ⟨g', (hQ g').2 ⟨hg'K, fun x y hxy => ?_⟩, hg'val⟩
    have hnf := hfree _ _ (fun h => hxy ((free_ll x y).1 h))
    have hentry : g'.val x y = g.val (ixSucc _ t j (.inl x)) (ixSucc _ t j (.inl y)) := by
      rw [hg'val, reGL_symm_val]; rfl
    rw [hentry]
    simpa [Matrix.one_apply] using hnf
end GlobalTheory.SymChain.IterPattern
