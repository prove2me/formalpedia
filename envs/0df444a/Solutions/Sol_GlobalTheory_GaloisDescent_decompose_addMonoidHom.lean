-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.decompose_addMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:11:06.572751+00:00
-- url     : https://prove2.me/submissions/cb90c613-05c3-4556-88e3-17fc852b0118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_rationalPart
import Theorems.Thm_GlobalTheory_GaloisDescent_rationalPart_baseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.contract_smul
attribute [local simp] GlobalTheory.GaloisDescent.mem_rationalPart
attribute [local simp] GlobalTheory.GaloisDescent.rationalPart_baseChange



set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {ι M M' σ τ : Type*} [DecidableEq ι] [AddCommMonoid M] [AddCommMonoid M']
  [SetLike σ M] [AddSubmonoidClass σ M] [SetLike τ M'] [AddSubmonoidClass τ M']
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (ℳ : ι → σ) (ℳ' : ι → τ) [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition ℳ'] (φ : M →+ M') (hφ : ∀ i, ∀ x ∈ ℳ i, φ x ∈ ℳ' i) (x : M) (i : ι) :
    (DirectSum.decompose ℳ' (φ x) i : M') = φ (DirectSum.decompose ℳ x i) := by
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous j x =>
    by_cases h : j = i
    · subst h
      rw [DirectSum.decompose_of_mem_same ℳ' (hφ j _ x.2), DirectSum.decompose_of_mem_same ℳ x.2]
    · rw [DirectSum.decompose_of_mem_ne ℳ' (hφ j _ x.2) h, DirectSum.decompose_of_mem_ne ℳ x.2 h,
        map_zero]
  | add x y hx hy => simp [hx, hy]
end GlobalTheory.GaloisDescent
