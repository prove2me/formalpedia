-- Prove2me | solution 1 for GlobalTheory.ThetaDivisionPoints.eq_zero_of_im_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:33:01.927711+00:00
-- url     : https://prove2.me/submissions/21d85cc8-f5a1-4d6f-89c8-7f0d73d14487

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThetaFunctionNeZeroAtDivisionPointSelfDual
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open Complex Matrix
open GlobalTheory GlobalTheory.ThetaDivisionPoints
namespace GlobalTheory.ThetaDivisionPoints
theorem _root_.solution {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) {S : Set (Fin g → ℂ)}
    (hS : Submodule.span ℝ S = ⊤) {z : Fin g → ℂ}
    (hz : ∀ m ∈ S, (z ⬝ᵥ Hm.mulVec (star m)).im = 0) : z = 0 := by
  have h : ∀ m, (z ⬝ᵥ Hm.mulVec (star m)).im = 0 := by
    intro m
    have hm : m ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm => exact hz m hm
    | zero => simp
    | add a b _ _ ha hb => rw [star_add, mulVec_add, dotProduct_add, add_im, ha, hb, add_zero]
    | smul t a _ ha =>
      rw [star_smul, mulVec_smul, dotProduct_smul, smul_im, ha, smul_zero]
  by_contra hne
  have h1 := hpos z hne
  have h2 := h (I • z)
  rw [star_smul, mulVec_smul, dotProduct_smul] at h2
  simp at h2
  linarith
end GlobalTheory.ThetaDivisionPoints
