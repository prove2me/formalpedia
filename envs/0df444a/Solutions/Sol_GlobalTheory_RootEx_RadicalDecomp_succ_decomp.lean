-- Prove2me | solution 1 for GlobalTheory.RootEx.RadicalDecomp.succ_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:05.313627+00:00
-- url     : https://prove2.me/submissions/a8bb1908-d791-4a06-b9e0-15017104bed7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentSubgroupSuccDecomposition
import Theorems.Thm_GlobalTheory_RootEx_RadicalDecomp_mem_N_of_succ
import Theorems.Thm_GlobalTheory_RootEx_RadicalDecomp_inv_rowE_val
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff
import Theorems.Thm_GlobalTheory_RootEx_Radical_rowE_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.RadicalDecomp
open GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.RadicalDecomp
theorem _root_.solution : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), ∀ g ∈ N k n c (p + 1), ∃ g₁ ∈ N k n c p ⊓ N k n c (p + 1), ∃ u : n → k, g = g₁ * rowE c p u := by
  intro k _ n _ _ c p g hg
  set u : n → k := fun s => ∑ l : Fin c, if l.val + 1 = p then g.val (Sum.inr l) (Sum.inl s) else 0
    with hu
  have hE : rowE c p u ∈ N k n c (p + 1) := rowE_mem u (Nat.lt_succ_self p)
  have h1 : g * (rowE c p u)⁻¹ ∈ N k n c (p + 1) := Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hE)
  refine ⟨g * (rowE c p u)⁻¹, ⟨?_, h1⟩, u, by simp⟩
  refine mem_N_of_succ h1 ?_
  intro l s hl
  have hg' := (mem_N_iff g).1 hg
  have key : ∀ l' : Fin c, (l'.val + 1 = p ↔ l' = l) :=
    fun l' => ⟨fun h => Fin.ext (by omega), fun h => h ▸ hl⟩
  have hd : g.val (Sum.inr l) (Sum.inr l) = 1 := by
    have := hg' (Sum.inr l) (Sum.inr l) le_rfl
    simpa using this
  have hus : u s = g.val (Sum.inr l) (Sum.inl s) := by
    simp only [hu, key, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Units.val_mul, inv_rowE_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.one_apply, Matrix.neg_apply,
    Matrix.of_apply, key, mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, hus]
  simp only [Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hd]
  ring
end GlobalTheory.RootEx.RadicalDecomp
