-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.red_rowAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:25:54.926021+00:00
-- url     : https://prove2.me/submissions/ff65a2a7-b051-4fb3-9b1e-e6f7a5e8cde8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_measurePreserving_shear
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
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
theorem _root_.solution (ν : Measure k) [ν.IsAddHaarMeasure] (ev it : Finset (m × m')) (β t t' : Matrix m m' k)
    (r₀ r₁ : m) (hr : r₁ ≠ r₀) (a : k) (Θ : Matrix m m' k → ℂ) (hΘ : Continuous Θ)
    (h : ∀ α r q, (r, q) ∉ it → rowAdd r₀ r₁ a (fill ev it β t α) r q = fill ev it β t' α r q) :
    red ν ev it β (fun x => Θ (rowAdd r₀ r₁ a x)) t = red ν ev it β Θ t' := by
  classical
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  let v : ({e : m × m' // e ∈ it} → k) → {e : m × m' // e ∈ it} → k := fun α e =>
    if e.1.1 = r₀ then a * fill ev it β t α r₁ e.1.2 else 0
  have hfm : ∀ q, Measurable fun α : {e : m × m' // e ∈ it} → k => fill ev it β t α r₁ q := by
    intro q
    simp only [fill, Matrix.of_apply]
    split_ifs with h1
    · exact measurable_pi_apply _
    · exact measurable_const
    · exact measurable_const
  have hvm : Measurable v := by
    refine measurable_pi_lambda _ fun e => ?_
    show Measurable fun α => if e.1.1 = r₀ then a * fill ev it β t α r₁ e.1.2 else 0
    split_ifs
    · exact (hfm e.1.2).const_mul a
    · exact measurable_const
  have h0' : ∀ (α : {e : m × m' // e ∈ it} → k) (e : {e : m × m' // e ∈ it}), e.1.1 ≠ r₀ → v α e = 0 := by
    intro α e he
    simp [v, he]
  have hdep : ∀ α α' : {e : m × m' // e ∈ it} → k,
      (∀ e : {e : m × m' // e ∈ it}, e.1.1 ≠ r₀ → α e = α' e) → v α = v α' := by
    intro α α' hα
    have hfe : ∀ q, fill ev it β t α r₁ q = fill ev it β t α' r₁ q := by
      intro q
      simp only [fill, Matrix.of_apply]
      split_ifs with h1
      · exact hα ⟨(r₁, q), h1⟩ hr
      · rfl
      · rfl
    funext e
    simp only [v, hfe]
  have hv_add : ∀ α, v (α + v α) = v α := fun α =>
    hdep _ _ fun e he => by simp [h0' α e he]
  have hv_sub : ∀ α, v (α - v α) = v α := fun α =>
    hdep _ _ fun e he => by simp [h0' α e he]
  let φ : ({e : m × m' // e ∈ it} → k) ≃ᵐ ({e : m × m' // e ∈ it} → k) :=
    { toFun := fun α => α + v α
      invFun := fun α => α - v α
      left_inv := fun α => by
        show (α + v α) - v (α + v α) = α
        rw [hv_add, add_sub_cancel_right]
      right_inv := fun α => by
        show (α - v α) + v (α - v α) = α
        rw [hv_sub, sub_add_cancel]
      measurable_toFun := measurable_id.add hvm
      measurable_invFun := measurable_id.sub hvm }
  have hmp : MeasurePreserving φ (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) :=
    measurePreserving_shear ν (fun e : {e : m × m' // e ∈ it} => e.1.1 ≠ r₀) v hvm h0' hdep
  have hfill : ∀ α, rowAdd r₀ r₁ a (fill ev it β t α) = fill ev it β t' (φ α) := by
    intro α
    ext r q
    by_cases hq : (r, q) ∈ it
    · simp [rowAdd, fill, hq, v, φ]
    · rw [h α r q hq]
      simp [fill, hq]
  unfold red
  simp only [hfill]
  exact hmp.integral_comp' (fun α => Θ (fill ev it β t' α))
end GlobalTheory.FlatFactor.UpStage
