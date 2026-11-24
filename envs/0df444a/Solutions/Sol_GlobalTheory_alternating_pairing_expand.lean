-- Prove2me | solution 1 for GlobalTheory.alternating_pairing_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:15.968609+00:00
-- url     : https://prove2.me/submissions/7952129f-81a2-43c1-bad7-c23576287995

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlternatingFormLatticeIntegrality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F V : Type} [Field F] [NumberField F] [AddCommGroup V]
    [Module F V] (L : Set V)
    (hadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hsm : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (Q : V → V → F)
    (halt : ∀ x ∈ L, ∀ x' ∈ L, Q x x' = -Q x' x)
    (hQadd : ∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, Q (x₁ + x₂) x' = Q x₁ x' + Q x₂ x')
    (hQsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, Q ((a : F) • x) x' = (a : F) * Q x x')
    {x x' : V} (hx : x ∈ L) (hx' : x' ∈ L) (r₀ r₁ s₀ s₁ : 𝓞 F) :
    Q ((r₀ : F) • x + (r₁ : F) • x') ((s₀ : F) • x + (s₁ : F) • x') =
      ((r₀ : F) * s₁ - (r₁ : F) * s₀) * Q x x' := by
  have hself : ∀ y ∈ L, Q y y = 0 := by
    intro y hy
    have h := halt y hy y hy
    have h2 : (2 : F) * Q y y = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hadd2 : ∀ y ∈ L, ∀ y₁ ∈ L, ∀ y₂ ∈ L, Q y (y₁ + y₂) = Q y y₁ + Q y y₂ := by
    intro y hy y₁ hy₁ y₂ hy₂
    have e1 := halt y hy _ (hadd _ hy₁ _ hy₂)
    have e2 := hQadd _ hy₁ _ hy₂ _ hy
    have e3 := halt y hy y₁ hy₁
    have e4 := halt y hy y₂ hy₂
    linear_combination e1 - e2 - e3 - e4
  have hsmul2 : ∀ y ∈ L, ∀ (a : 𝓞 F), ∀ y' ∈ L, Q y ((a : F) • y') = (a : F) * Q y y' := by
    intro y hy a y' hy'
    have e1 := halt y hy _ (hsm a y' hy')
    have e2 := hQsmul a y' hy' y hy
    have e3 := halt y hy y' hy'
    linear_combination e1 - e2 - (a : F) * e3
  have hu := hsm r₀ x hx
  have hv := hsm r₁ x' hx'
  have hp := hsm s₀ x hx
  have hq := hsm s₁ x' hx'
  rw [hQadd _ hu _ hv _ (hadd _ hp _ hq), hadd2 _ hu _ hp _ hq, hadd2 _ hv _ hp _ hq,
    hQsmul r₀ x hx _ hp, hQsmul r₀ x hx _ hq, hQsmul r₁ x' hx' _ hp, hQsmul r₁ x' hx' _ hq,
    hsmul2 x hx s₀ x hx, hsmul2 x hx s₁ x' hx', hsmul2 x' hx' s₀ x hx, hsmul2 x' hx' s₁ x' hx',
    hself x hx, hself x' hx', halt x' hx' x hx]
  ring
end GlobalTheory
