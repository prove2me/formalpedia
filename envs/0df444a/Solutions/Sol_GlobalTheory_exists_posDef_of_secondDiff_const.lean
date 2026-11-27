-- Prove2me | solution 1 for GlobalTheory.exists_posDef_of_secondDiff_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:37:36.612825+00:00
-- url     : https://prove2.me/submissions/0679448d-a7cd-4d4e-9ff3-f8046ec3684f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_HasConstSecondDiff_bilin_apply
import Theorems.Thm_GlobalTheory_HasConstSecondDiff_bilin_comm
import Theorems.Thm_GlobalTheory_HasConstSecondDiff_polar_quadraticMap
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
import Theorems.Thm_GlobalTheory_polar_realExt_one_tmul
import Theorems.Thm_GlobalTheory_posDef_of_posDef_realExt
import Theorems.Thm_GlobalTheory_HasConstSecondDiff_posDef_realExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul

set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution [Module.Free ℤ X] [Module.Finite ℤ X] (f : X → ℝ)
    (h : ∀ a a' μ ν : X, f (a + μ + ν) - f (a + μ) - f (a + ν) + f a =
      f (a' + μ + ν) - f (a' + μ) - f (a' + ν) + f a')
    (he : ∀ x, f (-x) = f x) (ht : Tendsto f cofinite atTop) :
    ∃ (B : X →+ X →+ ℝ) (Q : QuadraticForm ℝ (ℝ ⊗[ℤ] X)),
      (∀ a μ ν, B μ ν = f (a + μ + ν) - f (a + μ) - f (a + ν) + f a) ∧
      (∀ μ ν, B μ ν = B ν μ) ∧ (∀ x, f x - f 0 = B x x / 2) ∧ (∀ x, x ≠ 0 → 0 < f x - f 0) ∧
      Q.PosDef ∧ (∀ x, Q (1 ⊗ₜ x) = f x - f 0) ∧
      ∀ μ ν, QuadraticMap.polar Q (1 ⊗ₜ μ) (1 ⊗ₜ ν) = B μ ν := by
  have h' : HasConstSecondDiff f := h
  have hp := h'.posDef_realExt he ht
  refine ⟨LinearMap.toAddMonoidHom'.comp h'.bilin.toAddMonoidHom, realExt (h'.quadraticMap he),
    h'.bilin_apply, h'.bilin_comm, fun x => ?_, posDef_of_posDef_realExt hp, hp,
    fun x => by simp, fun μ ν => ?_⟩
  · change _ = h'.bilin x x / 2
    rw [h'.bilin_self he, two_smul]
    ring
  · exact (polar_realExt_one_tmul _ μ ν).trans (h'.polar_quadraticMap he μ ν)
end GlobalTheory
