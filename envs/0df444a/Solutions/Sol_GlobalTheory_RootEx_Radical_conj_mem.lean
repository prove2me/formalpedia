-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:54.463849+00:00
-- url     : https://prove2.me/submissions/71d18b8c-ef7a-439a-bc5f-252d14c03074

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff
import Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___of_mem_fe0d9551bf6c
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.Radical
theorem _root_.solution (x : GL n k) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    embX c x * g * (embX c x)⁻¹ ∈ N k n c p := by
  have h11 := toBlocks₁₁_of_mem hg
  rw [mem_N_iff] at hg ⊢
  intro r s hrs
  rw [conj_val, h11, Matrix.mul_one, Units.mul_inv]
  rcases r with r | r <;> rcases s with s | s
  · simp [Matrix.one_apply]
  · rw [fromBlocks_apply₁₂, Matrix.mul_apply, Matrix.one_apply_ne (by simp)]
    refine Finset.sum_eq_zero fun t _ => ?_
    have := hg (Sum.inl t) (Sum.inr s) hrs
    rw [Matrix.one_apply_ne (by simp)] at this
    simp [Matrix.toBlocks₁₂, this]
  · rw [fromBlocks_apply₂₁, Matrix.mul_apply, Matrix.one_apply_ne (by simp)]
    refine Finset.sum_eq_zero fun t _ => ?_
    have := hg (Sum.inr r) (Sum.inl t) hrs
    rw [Matrix.one_apply_ne (by simp)] at this
    simp [Matrix.toBlocks₂₁, this]
  · rw [fromBlocks_apply₂₂]
    exact hg _ _ hrs
end GlobalTheory.RootEx.Radical
