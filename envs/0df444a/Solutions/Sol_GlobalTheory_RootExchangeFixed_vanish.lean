-- Prove2me | solution 1 for GlobalTheory.RootExchangeFixed.vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:41:12.586655+00:00
-- url     : https://prove2.me/submissions/6567ed1a-ccd5-416e-9fa3-7496c2b8591a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space
import Theorems.Thm_GlobalTheory_RootExchangeFixed_exists_conj

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
namespace GlobalTheory.RootExchangeFixed
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ} (h1 : 1 ≤ p) (hc : p < c)
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {A : Type} [AddCommGroup A] [Module ℂ A]
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A →ₗ[ℂ] ℂ) (hl : IsNEquiv ψ p σ l) (v : A)
    (s : kˣ) (hβ : ∀ β : n → k, (∀ r, valuation k (β r * s) ≤ 1) → σ (colE c (p + 1) β) v = v)
    (u : n → k) (r : n) (hr : ¬ valuation k (u r) ≤ valuation k (s : k)) :
    l (σ (rowE c p u) v) = 0 := by
  have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
  have hu : 0 < valuation k (u r) := hs.trans (not_le.1 hr)
  have hu0 : u r ≠ 0 := by rintro h; simp [h] at hu
  have hx : ¬ valuation k (u r / s) ≤ valuation k ((1 : kˣ) : k) := by
    rw [map_div₀, div_le_iff₀ hs]; simpa using hr
  rw [← hψ] at hx
  push Not at hx
  obtain ⟨y, hy, hy1⟩ := hx
  obtain ⟨g, hg, hsum, hmul⟩ := exists_conj h1 hc u (Pi.single r (y / u r))
  have hfix := hβ (Pi.single r (y / u r)) (by
    intro t
    by_cases ht : t = r
    · subst ht
      rw [map_div₀, le_div_iff₀ hs] at hy
      rw [Pi.single_eq_same, map_mul, map_div₀, div_mul_eq_mul_div, div_le_iff₀ hu, one_mul]
      exact hy
    · simp [Pi.single_eq_of_ne ht])
  have hy' : simpleSum g = y := by
    rw [hsum, Finset.sum_eq_single r]
    · simp only [Pi.single_eq_same]; field_simp
    · intro t _ ht; simp [Pi.single_eq_of_ne ht]
    · simp
  have key : l (σ (rowE c p u) v) = (ψ y : ℂ) * l (σ (rowE c p u) v) := by
    conv_lhs => rw [← hfix]
    rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply, hl g hg, hy']
  by_contra hne
  apply hy1
  have : (ψ y : ℂ) = 1 := by
    have h2 : (ψ y : ℂ) * l (σ (rowE c p u) v) = 1 * l (σ (rowE c p u) v) := by
      rw [one_mul]; exact key.symm
    exact mul_right_cancel₀ hne h2
  exact Circle.ext (by simpa using this)
end GlobalTheory.RootExchangeFixed
