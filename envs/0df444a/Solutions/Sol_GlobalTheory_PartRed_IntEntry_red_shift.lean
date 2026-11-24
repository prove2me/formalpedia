-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.red_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:59.411357+00:00
-- url     : https://prove2.me/submissions/66031e4d-b77c-4197-a847-2e07063f1b32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation
import Theorems.Thm_GlobalTheory_PartRed_IntEntry_fill_add_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.IntEntry
namespace GlobalTheory.PartRed.IntEntry
theorem _root_.solution : ∀ (k : Type) [Field k] [TopologicalSpace k] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (u : k), (∀ t, Φ (t + Matrix.single e.1 e.2 u) = Φ t) → ψ (u * w (Matrix.single e.1 e.2 1)) = 1 → ∀ x, red ψ ν w β E I Φ (x + Matrix.single e.1 e.2 u) = red ψ ν w β E I Φ x := by
  intro k _ _ _ ψ ν R Q _ _ _ _ w β E I e hE hI Φ u hΦ hψ x
  have hw : w (Matrix.single e.1 e.2 u) = u * w (Matrix.single e.1 e.2 1) := by
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have h1 : ψ (-w (Matrix.single e.1 e.2 u)) = 1 := by rw [AddChar.map_neg_eq_inv, hw, hψ, inv_one]
  unfold red
  simp only [fill_add_single β E I x _ e hI hE u, hΦ, map_add, neg_add, AddChar.map_add_eq_mul, h1, mul_one]
end GlobalTheory.PartRed.IntEntry
