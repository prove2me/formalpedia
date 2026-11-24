-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.integral_embX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:47.550644+00:00
-- url     : https://prove2.me/submissions/4adda41f-503e-44b3-813d-0e29487a8926

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Theorems.Thm_GlobalTheory_SplitWeil_linear_change_of_variables


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  (ν : Measure k) [ν.IsAddHaarMeasure] {A : Type} [AddCommGroup A] [Module ℂ A]
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution {P : Type} [AddCommGroup P] [Module ℂ P] {π : Representation ℂ (GL n k) P}
    {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} {b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ} (E : (n → k) → GL (n ⊕ Fin c) k)
    (g m : GL n k) (z : ℝ) (φ : P) (hb : ∀ v, b (π g φ) (σ (embX c g) v) = (z : ℂ) * b φ v)
    (hE : ∀ u, E u * embX c g = embX c g * E (m.val.mulVec u)) (v : A) :
    ∫ u, b (π g φ) (σ (E u) (σ (embX c g) v)) ∂(Measure.pi fun _ => ν) =
      ((z * (nabs k (Matrix.GeneralLinearGroup.det m))⁻¹ : ℝ) : ℂ) *
        ∫ u, b φ (σ (E u) v) ∂(Measure.pi fun _ => ν) := by
  have : ∀ u, b (π g φ) (σ (E u) (σ (embX c g) v)) = (z : ℂ) * b φ (σ (E (m.val.mulVec u)) v) := fun u => by
    rw [← Module.End.mul_apply, ← map_mul, hE, map_mul, Module.End.mul_apply, hb]
  simp only [this]
  rw [integral_const_mul, (GlobalTheory.SplitWeil.linear_change_of_variables k n n ν).1 m (fun u => b φ (σ (E u) v))]
  simp [mul_assoc]
end GlobalTheory.RootEx.Exchange
