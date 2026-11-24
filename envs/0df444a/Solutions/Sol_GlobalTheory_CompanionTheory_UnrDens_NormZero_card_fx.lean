-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormZero.card_fx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:52:05.241082+00:00
-- url     : https://prove2.me/submissions/3e4badbf-00d7-4420-baa6-55387da7b899

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormZero
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormZero
theorem _root_.solution (h : ResAlg E τ q ε) : Nat.card (Fx τ) = q := by
  obtain ⟨u, hu, hb⟩ := h.basis
  let φ : Fx τ × Fx τ → E := fun p => (p.1 : E) + (p.2 : E) * u
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
      have h1 : x + y * u = x' + y' * u := hxy
      have h2 : x + y * τ u = x' + y' * τ u := by
        have := congrArg τ h1
        simpa [hx, hy, hx', hy'] using this
      have h3 : (y - y') * (u - τ u) = 0 := by linear_combination h1 - h2
      have h4 : y = y' := sub_eq_zero.1 (hu.mul_left_eq_zero.1 h3)
      have h5 : x = x' := by
        subst h4
        exact add_right_cancel h1
      subst h4 h5
      rfl
    · intro a
      obtain ⟨x, y, hx, hy, rfl⟩ := hb a
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have h1 : Nat.card (Fx τ × Fx τ) = Nat.card E := Nat.card_congr (Equiv.ofBijective φ hφ)
  rw [Nat.card_prod, h.card] at h1
  have h2 : Nat.card (Fx τ) ^ 2 = q ^ 2 := by rw [← h1]; ring
  exact (Nat.pow_left_inj (by norm_num)).1 h2
end GlobalTheory.CompanionTheory.UnrDens.NormZero
