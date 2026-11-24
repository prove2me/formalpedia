-- Prove2me | solution 1 for GlobalTheory.JacquetBlocks.mem_unipRad_iff_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:00:05.18974+00:00
-- url     : https://prove2.me/submissions/8db1aa60-8381-4472-85ad-466405af23fc

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacquetBlocks
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.JacquetBlocks
theorem _root_.solution {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ g ∈ parab R e ∧
      ∀ i j, blk e i = blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  refine and_congr_right fun _ => ⟨fun h i j hij => ?_, fun h a x y => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    subst hij
    rw [h a x y]
    simp [Matrix.one_apply, e.injective.eq_iff]
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply, e.injective.eq_iff]
end GlobalTheory.JacquetBlocks
