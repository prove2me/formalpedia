-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.kerRed_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:18:05.8329+00:00
-- url     : https://prove2.me/submissions/302b56a8-8013-4bae-ac1a-342cf9b8c893

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FlatFactor_continuous_fill
import Theorems.Thm_GlobalTheory_FlatFactor_hasCompactSupport_comp_fill
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.UpStage
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.FlatFactor.UpStage
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (ν : Measure k) [ν.IsAddHaarMeasure]
    (ev it : Finset (m × m')) (β : Matrix m m' k) (l : SB (Matrix m m' k) →ₗ[ℂ] M) (hK : KerRed ν ev it β l)
    (Θ Θ' : SB (Matrix m m' k)) (h : ∀ t, red ν ev it β Θ.1 t = red ν ev it β Θ'.1 t) : l Θ = l Θ' := by
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have hint : ∀ (Φ : SB (Matrix m m' k)) t,
      Integrable (fun x => Φ.1 (fill ev it β t x)) (Measure.pi fun _ => ν) := by
    intro Φ t
    have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
    exact (hΦ.1.continuous.comp (continuous_fill ev it β t)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_fill ev it β t _ hΦ.2)
  have h0 : l (Θ - Θ') = 0 := by
    apply hK
    intro t
    change ∫ x, (Θ.1 - Θ'.1) (fill ev it β t x) ∂(Measure.pi fun _ => ν) = 0
    simp only [Pi.sub_apply]
    rw [integral_sub (hint Θ t) (hint Θ' t)]
    exact sub_eq_zero.2 (h t)
  rw [map_sub] at h0
  exact sub_eq_zero.1 h0
end GlobalTheory.FlatFactor.UpStage
