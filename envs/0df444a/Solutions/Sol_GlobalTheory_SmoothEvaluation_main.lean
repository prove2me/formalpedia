-- Prove2me | solution 1 for GlobalTheory.SmoothEvaluation.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:11:36.878895+00:00
-- url     : https://prove2.me/submissions/66f74c78-ba7d-46c9-82d6-1636be3a1f00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ImportsTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmoothEvaluation
namespace GlobalTheory.SmoothEvaluation
theorem _root_.solution : ∀ {A R : Type} [inst : CommRing A] [inst_1 : CommRing R] [inst_2 : Algebra A R] {r : ℕ} (b : Fin r → R), (∀ (f : R), ∃! cf : Fin r → A, f = ∑ i : Fin r, (Algebra.algebraMap A R : A → R) (cf i) * b i) → ∃ (e : Module.Basis (Fin r) A R), ∀ (i : Fin r), (e : Fin r → R) i = b i := by
  intro A R _ _ _ r b h
  have hli : LinearIndependent A b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨c, _, hc⟩ := h 0
    have h1 := hc g (by simp only [Algebra.smul_def] at hg; exact hg.symm)
    have h2 := hc 0 (by simp)
    intro i
    rw [h1, ← h2]
    rfl
  have hsp : ⊤ ≤ Submodule.span A (Set.range b) := by
    intro f _
    obtain ⟨c, hc, _⟩ := h f
    rw [hc]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩
end GlobalTheory.SmoothEvaluation
