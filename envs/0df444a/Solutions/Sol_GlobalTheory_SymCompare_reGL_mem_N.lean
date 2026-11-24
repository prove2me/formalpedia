-- Prove2me | solution 1 for GlobalTheory.SymCompare.reGL_mem_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:21:18.287045+00:00
-- url     : https://prove2.me/submissions/4079d7e8-0a95-4794-8011-fa7650fa2c6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_StepData_reGL_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}
namespace GlobalTheory.SymCompare
theorem _root_.solution (e : n ≃ m) {p : ℕ} {g : GL (n ⊕ Fin c) k} : reGL (sE e c) g ∈ N k m c p ↔ g ∈ N k n c p := by
  have hl : ∀ r, lev p (sE e c r) = lev p r := by rintro (r | r) <;> rfl
  rw [Model.mem_N_iff, Model.mem_N_iff]
  constructor
  · intro h r s hrs
    have := h (sE e c r) (sE e c s) (by rwa [hl, hl])
    simpa only [reGL_val, submatrix_apply, Equiv.symm_apply_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq] using this
  · intro h r s hrs
    obtain ⟨r, rfl⟩ := (sE e c).surjective r
    obtain ⟨s, rfl⟩ := (sE e c).surjective s
    have := h r s (by rwa [hl, hl] at hrs)
    simpa only [reGL_val, submatrix_apply, Equiv.symm_apply_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq] using this
end GlobalTheory.SymCompare
