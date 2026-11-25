-- Prove2me | solution 1 for GlobalTheory.T.exists_factor_through_flatMapFourierJacobiColumn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:03:31.328495+00:00
-- url     : https://prove2.me/submissions/cf5de647-ba38-485c-9a5f-b6ecedc13169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFactorThroughFlatMapFourierJacobiColumn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFactorThroughFlatMapFourierJacobiColumnStatement
import Theorems.Thm_GlobalTheory_LocFlat_flCol_factor


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), (∀ x, GlobalTheory.LocFlat.flCol ψ ν p Φ.1 x = 0) → L Φ = 0) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν p Φ.1 → L Φ = L₀ Ψ := by
  first | exact @GlobalTheory.LocFlat.flCol_factor | exact GlobalTheory.LocFlat.flCol_factor | (intros; apply GlobalTheory.LocFlat.flCol_factor <;> assumption)
end _root_.GlobalTheory.T
