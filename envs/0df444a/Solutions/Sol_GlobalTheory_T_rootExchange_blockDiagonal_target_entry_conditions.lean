-- Prove2me | solution 1 for GlobalTheory.T.rootExchange_blockDiagonal_target_entry_conditions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:35.136196+00:00
-- url     : https://prove2.me/submissions/e25a6c35-3e6a-4b80-80fc-1faed89c5a3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeBlockDiagonalTargetEntryConditions
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeBlockDiagonalTargetEntryConditionsStatement
import Theorems.Thm_GlobalTheory_PosEntries_entries


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], HasConductor ψ 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → ∀ (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), (∀ x, Ψ x ≠ 0 → IntM (A.val * x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val)) → (∀ x z, MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) → Ψ (x + z) = Ψ x) → opE ψ ν p Ψ ≠ 0 → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) ∧ ∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] := by
  first | exact @GlobalTheory.PosEntries.entries | exact GlobalTheory.PosEntries.entries | (intros; apply GlobalTheory.PosEntries.entries <;> assumption)
end _root_.GlobalTheory.T
