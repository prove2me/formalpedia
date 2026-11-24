-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.isNEquiv_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:57:49.242011+00:00
-- url     : https://prove2.me/submissions/d88609cb-12d7-40e4-8693-2dcf707ad4ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


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
theorem _root_.solution {ψ : AddChar k Circle} {p q : ℕ} {σ : Representation ℂ (GL (n ⊕ Fin c) k) A}
    {l : A → ℂ} (hl : IsNEquiv ψ p σ l) (E : (n → k) → GL (n ⊕ Fin c) k)
    (hE : ∀ g ∈ N k n c q, ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c p, simpleSum h = simpleSum g ∧
      E u * g = h * E (u + w)) :
    IsNEquiv ψ q σ fun v => ∫ u, l (σ (E u) v) ∂(Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  intro g hg v
  obtain ⟨w, hw⟩ := hE g hg
  have : ∀ u, l (σ (E u) (σ g v)) = (ψ (simpleSum g) : ℂ) * l (σ (E (u + w)) v) := fun u => by
    obtain ⟨h, hN, hs, he⟩ := hw u
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hl h hN, hs]
  simp only [this]
  rw [integral_const_mul, integral_add_right_eq_self (fun u => l (σ (E u) v)) w]
end GlobalTheory.RootEx.Exchange
