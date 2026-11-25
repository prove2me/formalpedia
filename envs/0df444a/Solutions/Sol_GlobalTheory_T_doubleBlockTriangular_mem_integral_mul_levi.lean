-- Prove2me | solution 1 for GlobalTheory.T.doubleBlockTriangular_mem_integral_mul_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:59.075733+00:00
-- url     : https://prove2.me/submissions/bf2739ab-33dd-4308-9f2f-d4cb229132f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DoubleBlockTriangularMemIntegralMulLevi
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DoubleBlockTriangularMemIntegralMulLeviStatement
import Theorems.Thm_GlobalTheory_PClassAlg_blockDiag_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) → (∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k]) → ∃ γ : GL n k, A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)) ∈ KO k (n ⊕ Fin c) := by
  first | exact @GlobalTheory.PClassAlg.blockDiag_mem_KO | exact GlobalTheory.PClassAlg.blockDiag_mem_KO | (intros; apply GlobalTheory.PClassAlg.blockDiag_mem_KO <;> assumption)
end _root_.GlobalTheory.T
