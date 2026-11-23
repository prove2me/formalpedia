-- Prove2me | solution 1 for GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:06.933321+00:00
-- url     : https://prove2.me/submissions/40a8280b-e505-468a-a52a-0e59575d0fa4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.CuspMax
variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL.CuspMax
theorem _root_.solution {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases (not_lt.1 hij).lt_or_eq with h | h
    · rw [mem_parab.1 h1 i j h, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ h
    · obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
      obtain rfl : b = a := by simpa using h
      rw [h2]
      simp [Matrix.one_apply]
  · intro h
    refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
    · rw [h i j hij.not_gt, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp)]
      simp [Matrix.one_apply]
end GlobalTheory.SmGL.CuspMax
