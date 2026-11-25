-- Prove2me | solution 1 for GlobalTheory.T.flatFactorReduction_kernel_all_nonFreeUnread_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:32.677512+00:00
-- url     : https://prove2.me/submissions/991034ca-6f2e-4c50-9d09-a97f4c88195f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelAllNonFreeUnreadEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelAllNonFreeUnreadEntriesStatement
import Theorems.Thm_GlobalTheory_FlatFactor_LowStage_kerRed_evAll


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → GlobalTheory.FlatFactor.TwLaw ρ ψ l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evC n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l := by
  first | exact @GlobalTheory.FlatFactor.LowStage.kerRed_evAll | exact GlobalTheory.FlatFactor.LowStage.kerRed_evAll | (intros; apply GlobalTheory.FlatFactor.LowStage.kerRed_evAll <;> assumption)
end _root_.GlobalTheory.T
