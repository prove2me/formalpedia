-- Prove2me | solution 1 for GlobalTheory.HasTriangularWeight.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:45.799671+00:00
-- url     : https://prove2.me/submissions/18ff136d-7903-4e57-9ff8-406247f9d861

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Theorems.Thm_GlobalTheory_frameMul_diagonal

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
variable {ι : Type*} {K : Type*} {V : ι → Type*}
variable [Fintype ι] {r : ι → ℕ} [Field K] [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
  {W : Type*} [AddCommGroup W] [Module K W]
namespace GlobalTheory
namespace HasTriangularWeight
theorem _root_.solution {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → W}
    (hP : HasTriangularWeight K a P) (x : ∀ s, Fin (r s) → V s) (d : ∀ s, Fin (r s) → K)
    (hd : ∀ s i, d s i ≠ 0) :
    P (fun s i => d s i • x s i) = (∏ s, ∏ i, d s i ^ a s i) • P x := by
  rw [← frameMul_diagonal, hP x _ (fun s => Matrix.blockTriangular_diagonal _)
    (fun s i => by simpa using hd s i)]
  simp
end HasTriangularWeight
end GlobalTheory
