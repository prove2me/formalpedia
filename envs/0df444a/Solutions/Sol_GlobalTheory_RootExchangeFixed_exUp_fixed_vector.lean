-- Prove2me | solution 1 for GlobalTheory.RootExchangeFixed.exUp_fixed_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:41.169295+00:00
-- url     : https://prove2.me/submissions/56fa7222-c6ee-4037-90b6-3044498061ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space
import Theorems.Thm_GlobalTheory_RootExchangeFixed_lowU_mem_KO
import Theorems.Thm_GlobalTheory_RootExchangeFixed_upU_mem_KO
import Theorems.Thm_GlobalTheory_RootExchangeFixed_exUp_of_fixed

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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A →ₗ[ℂ] ℂ) (_ : IsNEquiv ψ p σ l) (v : A), (∀ s : kˣ, (∀ β : n → k, (∀ r, valuation k (β r * s) ≤ 1) → σ (colE c (p + 1) β) v = v) → (∀ u : n → k, (∀ r, valuation k (u r) ≤ valuation k (s : k)) → σ (rowE c p u) v = v) → exUp ν p σ l v = ((nabs k s ^ Fintype.card n : ℝ) : ℂ) * l v) ∧ ((∀ g ∈ KO k (n ⊕ Fin c), σ g v = v) → exUp ν p σ l v = l v) := by
  intro k _ _ _ _ _ _ n _ _ c p h1 hc ψ hψ ν hν A _ _ σ l hl v
  refine ⟨fun s hβ hu => exUp_of_fixed h1 hc hψ ν hν σ l hl v s hβ hu, fun hK => ?_⟩
  rw [exUp_of_fixed h1 hc hψ ν hν σ l hl v 1]
  · simp [nabs]
  · intro β h
    refine hK _ (upU_mem_KO _ fun r i => ?_)
    rw [Matrix.of_apply]
    split_ifs
    · simpa using h r
    · simp
  · intro u h
    refine hK _ (lowU_mem_KO _ fun r i => ?_)
    rw [Matrix.of_apply]
    split_ifs
    · simpa using h i
    · simp
end GlobalTheory.RootExchangeFixed
