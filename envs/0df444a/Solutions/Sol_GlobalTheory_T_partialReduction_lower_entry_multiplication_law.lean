-- Prove2me | solution 1 for GlobalTheory.T.partialReduction_lower_entry_multiplication_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:34:39.226337+00:00
-- url     : https://prove2.me/submissions/9d482cfa-ae55-44ae-900b-009c9b747bed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLaw
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLawStatement
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_evalLaw_low


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∀ (l : Fin c) (i : Fin (c + 1)), ρ < i.val → i.val ≤ l.val → ∀ E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))), GlobalTheory.PartRed.fixSet ρ ⊆ E → (GlobalTheory.PartRed.lowSet ρ).filter (fun e => GlobalTheory.PartRed.colIx e < i.val) ⊆ E → E ⊆ GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ → (Sum.inr l, Sum.inr i) ∉ E → GlobalTheory.PartRed.EvalLaw L ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) E (GlobalTheory.PartRed.transSet ρ) (Sum.inr l, Sum.inr i) := by
  first | exact @GlobalTheory.PartRed.LowLaw.evalLaw_low | exact GlobalTheory.PartRed.LowLaw.evalLaw_low | (intros; apply GlobalTheory.PartRed.LowLaw.evalLaw_low <;> assumption)
end _root_.GlobalTheory.T
