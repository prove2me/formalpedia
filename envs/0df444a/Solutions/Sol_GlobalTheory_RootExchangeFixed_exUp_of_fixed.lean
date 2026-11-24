-- Prove2me | solution 1 for GlobalTheory.RootExchangeFixed.exUp_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:56:04.006024+00:00
-- url     : https://prove2.me/submissions/e517d22f-0aa6-4029-a064-9e911f35ba63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space
import Theorems.Thm_GlobalTheory_RootExchangeFixed_nonarchimedeanLocalField_secondCountable_t2Space
import Theorems.Thm_GlobalTheory_RootExchangeFixed_vanish
import Theorems.Thm_GlobalTheory_RootExchangeFixed_meas_ball
import Theorems.Thm_GlobalTheory_RootExchangeFixed_vol_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
open GlobalTheory GlobalTheory.RootExchangeFixed
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.RootExchangeFixed
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ} (h1 : 1 ≤ p) (hc : p < c)
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k) (hν : IsUnitVol ν)
    {A : Type} [AddCommGroup A] [Module ℂ A]
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A →ₗ[ℂ] ℂ) (hl : IsNEquiv ψ p σ l) (v : A)
    (s : kˣ) (hβ : ∀ β : n → k, (∀ r, valuation k (β r * s) ≤ 1) → σ (colE c (p + 1) β) v = v)
    (hu : ∀ u : n → k, (∀ r, valuation k (u r) ≤ valuation k (s : k)) → σ (rowE c p u) v = v) :
    exUp ν p σ l v = ((nabs k s ^ Fintype.card n : ℝ) : ℂ) * l v := by
  haveI := hν.1
  obtain ⟨_, _⟩ := nonarchimedeanLocalField_secondCountable_t2Space (k := k)
  let S : Set (n → k) := Set.univ.pi fun _ => {x : k | valuation k x ≤ valuation k (s : k)}
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ => meas_ball s
  have hf : (fun u : n → k => l (σ (rowE c p u) v)) = S.indicator fun _ => l v := by
    funext u
    by_cases h : u ∈ S
    · rw [Set.indicator_of_mem h, hu u fun r => h r trivial]
    · rw [Set.indicator_of_notMem h]
      simp only [S, Set.mem_pi, Set.mem_univ, true_imp_iff, not_forall] at h
      obtain ⟨r, hr⟩ := h
      exact vanish h1 hc hψ σ l hl v s hβ u r hr
  have hn : 0 ≤ nabs k s := NNReal.coe_nonneg _
  unfold exUp
  rw [hf, integral_indicator_const _ hS, Measure.real, Measure.pi_pi]
  simp [vol_ball ν hν s, hn]
end GlobalTheory.RootExchangeFixed
