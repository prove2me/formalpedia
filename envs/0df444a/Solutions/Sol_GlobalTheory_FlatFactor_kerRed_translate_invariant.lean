-- Prove2me | solution 1 for GlobalTheory.FlatFactor.kerRed_translate_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:53:05.197738+00:00
-- url     : https://prove2.me/submissions/c0e8d91c-c4ad-49c8-95a9-1f48605c88c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatLinearFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Theorems.Thm_GlobalTheory_FlatFactor_fill_add_single
import Theorems.Thm_GlobalTheory_FlatFactor_continuous_fill
import Theorems.Thm_GlobalTheory_FlatFactor_hasCompactSupport_comp_fill
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.FlatFactor
namespace GlobalTheory.FlatFactor
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it : Finset (m × m')), Disjoint ev it → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ it, ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) := by
  intro k _ _ _ _ _ _ ψ ν _ _ hν m m' _ _ _ _ M _ _ l β ev it _ hK e he a Θ Θ' hΘ'
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  rw [← sub_eq_zero, ← map_sub]
  apply hK
  intro t
  have hint : Integrable (fun x => Θ.1 (fill ev it β t x)) (Measure.pi fun _ : {e : m × m' // e ∈ it} => ν) :=
    ((Θ.2.1.continuous).comp (continuous_fill ev it β t)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_fill ev it β t Θ.1 Θ.2.2)
  have hint' : Integrable (fun x => Θ.1 (fill ev it β t (x + Pi.single ⟨e, he⟩ a)))
      (Measure.pi fun _ : {e : m × m' // e ∈ it} => ν) :=
    hint.comp_add_right _
  unfold red
  simp only [Submodule.coe_sub, Pi.sub_apply]
  have h1 : ∀ x, Θ'.1 (fill ev it β t x) = Θ.1 (fill ev it β t (x + Pi.single ⟨e, he⟩ a)) := by
    intro x; rw [hΘ', fill_add_single]
  simp_rw [h1]
  rw [integral_sub hint' hint, integral_add_right_eq_self (fun x => Θ.1 (fill ev it β t x)), sub_self]
end GlobalTheory.FlatFactor
