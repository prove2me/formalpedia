-- Prove2me | solution 1 for GlobalTheory.T.partialReduction_eq_zero_of_flatMapColumn_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:04:44.492602+00:00
-- url     : https://prove2.me/submissions/e64ad2a9-53ea-44bf-93c0-05cbbc6aca7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqZeroOfFlatMapColumnZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqZeroOfFlatMapColumnZeroStatement
import Theorems.Thm_GlobalTheory_FlatRed_red_eq_zero_of_flCol


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ → ∀ Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, (∀ x, GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ x = 0) → ∀ t, GlobalTheory.FlatFactor.red ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) (fun t => (ψ (-ch t) : ℂ) * Φ t) t = 0 := by
  first | exact @GlobalTheory.FlatRed.red_eq_zero_of_flCol | exact GlobalTheory.FlatRed.red_eq_zero_of_flCol | (intros; apply GlobalTheory.FlatRed.red_eq_zero_of_flCol <;> assumption)
end _root_.GlobalTheory.T
