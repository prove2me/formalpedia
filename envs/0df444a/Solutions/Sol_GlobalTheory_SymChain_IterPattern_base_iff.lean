-- Prove2me | solution 1 for GlobalTheory.SymChain.IterPattern.base_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:48.520819+00:00
-- url     : https://prove2.me/submissions/08f9d684-2aae-44a2-96c5-ff2407aaa278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPatternStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Theorems.Thm_GlobalTheory_SymChain_IterPattern_symm_mem_KO_iff
import Theorems.Thm_GlobalTheory_SymChain_IterPattern_mem_reindex_J

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
theorem _root_.solution (P : TypeDatum k (Fin κ ⊕ Fin l))
    (hP : ∀ g : GL (Fin κ ⊕ Fin l) k, g ∈ P.J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1)
    (g : GL (Ix (Fin κ ⊕ Fin l) t 0) k) :
    g ∈ (P.reindex (ixZero _ t)).J ↔
      g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  have hz : ∀ a b : Fin κ ⊕ Fin l, FreeIx ρ (ixZero _ t a) (ixZero _ t b) ↔ FreeTop ρ a b := fun _ _ => Iff.rfl
  rw [mem_reindex_J, hP, symm_mem_KO_iff]
  simp only [reGL_symm_val]
  refine and_congr_right fun _ => ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩
  · obtain ⟨a, rfl⟩ := (ixZero _ t).surjective a
    obtain ⟨b, rfl⟩ := (ixZero _ t).surjective b
    have := h a b (fun hf => hab ((hz a b).2 hf))
    simpa [Matrix.one_apply] using this
  · have := h _ _ (fun hf => hab ((hz a b).1 hf))
    simpa [Matrix.one_apply] using this
end GlobalTheory.SymChain.IterPattern
