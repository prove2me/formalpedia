-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLen.excess_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:05:13.583812+00:00
-- url     : https://prove2.me/submissions/0f98f9a1-0690-4c4a-bf3e-0ad121f11c61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenberg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLen
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertLen
theorem _root_.solution {ι : Type} (R : ι → WithZero (Multiplicative ℤ)) (T : WithZero (Multiplicative ℤ)) (A Y e j : ℕ)
    (hAY : A ≤ Y) (hY : ∀ i, R i ≤ WithZero.exp (Y : ℤ)) (hYs : Y = A ∨ ∃ i, R i = WithZero.exp (Y : ℤ))
    (he₁ : ∀ i, R i ≤ WithZero.exp ((A + e : ℕ) : ℤ)) (he₂ : T ≤ WithZero.exp ((A + Y + e : ℕ) : ℤ))
    (he₃ : e = 0 ∨ (∃ i, R i = WithZero.exp ((A + e : ℕ) : ℤ)) ∨ T = WithZero.exp ((A + Y + e : ℕ) : ℤ)) :
    Y + e ≤ A + j ↔ (∀ i, R i ≤ WithZero.exp ((A + j / 2 : ℕ) : ℤ)) ∧ T ≤ WithZero.exp ((2 * A + j : ℕ) : ℤ) := by
  have key : ∀ a b : ℕ, WithZero.exp (a : ℤ) ≤ WithZero.exp (b : ℤ) ↔ a ≤ b := fun a b => by
    rw [WithZero.exp_le_exp]
    exact Nat.cast_le
  constructor
  · intro h
    have hY2 : Y ≤ A + j / 2 := by
      rcases hYs with rfl | ⟨i₀, hi₀⟩
      · omega
      · have := (key _ _).1 (hi₀.symm.le.trans (he₁ i₀))
        omega
    exact ⟨fun i => (hY i).trans ((key _ _).2 hY2), he₂.trans ((key _ _).2 (by omega))⟩
  · rintro ⟨hR, hT⟩
    have hY2 : Y ≤ A + j / 2 := by
      rcases hYs with rfl | ⟨i₀, hi₀⟩
      · omega
      · exact (key _ _).1 (hi₀.symm.le.trans (hR i₀))
    rcases he₃ with rfl | ⟨i₁, hi₁⟩ | hT'
    · omega
    · have := (key _ _).1 (hi₁.symm.le.trans (hR i₁))
      omega
    · have := (key _ _).1 (hT'.symm.le.trans hT)
      omega
end GlobalTheory.CompanionTheory.InertLen
