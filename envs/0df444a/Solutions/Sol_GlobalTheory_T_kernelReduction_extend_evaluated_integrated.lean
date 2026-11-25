-- Prove2me | solution 1 for GlobalTheory.T.kernelReduction_extend_evaluated_integrated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:44.358811+00:00
-- url     : https://prove2.me/submissions/0d7f08c7-c2c2-40e2-9dad-c3eb14683cc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegratedStatement
import Theorems.Thm_GlobalTheory_FlatFactor_KerRedStep_kerRed_extend


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it ev' it' : Finset (m × m')), ev ⊆ ev' → it ⊆ it' → Disjoint ev' it' → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ ev', e ∉ ev → ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ e ∈ it', e ∉ it → ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev' it' β l := by
  first | exact @GlobalTheory.FlatFactor.KerRedStep.kerRed_extend | exact GlobalTheory.FlatFactor.KerRedStep.kerRed_extend | (intros; apply GlobalTheory.FlatFactor.KerRedStep.kerRed_extend <;> assumption)
end _root_.GlobalTheory.T
