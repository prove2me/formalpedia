-- Prove2me | solution 1 for GlobalTheory.HasTriangularWeightPoly.hasTriangularWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:23.971208+00:00
-- url     : https://prove2.me/submissions/4c39d1ca-cafe-46ce-b575-c95b7bf28d6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero

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
namespace HasTriangularWeightPoly
theorem _root_.solution {V : ι → Type*} [∀ s, AddCommGroup (V s)]
    [∀ s, Module K (V s)] {a : ∀ s, Fin (r s) → ℕ}
    {p : MvPolynomial (EntryIndex (fun s => Fin (r s)) (fun s => Fin (r s))) K}
    (hp : HasTriangularWeightPoly a p) (L : ∀ s, Fin (r s) → Module.Dual K (V s)) :
    HasTriangularWeight K a fun y : ∀ s, Fin (r s) → V s =>
      MvPolynomial.eval (entries fun s => Matrix.of fun i j => L s i (y s j)) p := by
  intro y b hb hb0
  have : (fun s => Matrix.of fun i j => L s i (frameMul y b s j)) =
      fun s => (Matrix.of fun i j => L s i (y s j)) * b s := by
    funext s
    ext i j
    simp [frameMul, Matrix.mul_apply, mul_comm]
  exact (congrArg (fun z => MvPolynomial.eval (entries z) p) this).trans (hp _ b hb hb0)
end HasTriangularWeightPoly
end GlobalTheory
