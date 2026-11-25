-- Prove2me | solution 1 for GlobalTheory.HasTriangularWeight.poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:36.281006+00:00
-- url     : https://prove2.me/submissions/5d3409da-a02f-42fd-b92d-22d03bbbcddd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Theorems.Thm_GlobalTheory_frameMul_frameMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {K : Type*} [Field K]
namespace GlobalTheory
namespace HasTriangularWeight
theorem _root_.solution {V : ι → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
    {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → K} (hP : HasTriangularWeight K a P)
    (w : ∀ s, Fin (r s) → V s)
    {p : MvPolynomial (EntryIndex (fun s => Fin (r s)) (fun s => Fin (r s))) K}
    (hp : ∀ ξ : ∀ s, Matrix (Fin (r s)) (Fin (r s)) K,
      P (frameMul w ξ) = MvPolynomial.eval (entries ξ) p) : HasTriangularWeightPoly a p := by
  intro x b hb hb0
  rw [← hp, ← hp, ← frameMul_frameMul, hP _ b hb hb0, smul_eq_mul]
end HasTriangularWeight
end GlobalTheory
