-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLen.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:05:14.221867+00:00
-- url     : https://prove2.me/submissions/5f70f71f-90ce-4ad9-8457-3100b1cfcd2d

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
theorem _root_.solution {ι : Type} [Fintype ι] [Nonempty ι] (ρ : ι → L) :
    ∃ e : ℕ, (∀ i, Valued.v (ρ i) ≤ WithZero.exp (e : ℤ)) ∧ (e = 0 ∨ ∃ i, Valued.v (ρ i) = WithZero.exp (e : ℤ)) := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (ρ i)) Finset.univ_nonempty
  by_cases h : Valued.v (ρ i₀) ≤ WithZero.exp ((0 : ℕ) : ℤ)
  · exact ⟨0, fun i => (hi₀ i (Finset.mem_univ _)).trans h, Or.inl rfl⟩
  · push_neg at h
    have hne : Valued.v (ρ i₀) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' h)
    have hk : WithZero.exp (WithZero.log (Valued.v (ρ i₀))) = Valued.v (ρ i₀) := WithZero.exp_log hne
    have hk0 : (0 : ℤ) < WithZero.log (Valued.v (ρ i₀)) := by
      rw [← hk, WithZero.exp_lt_exp] at h
      exact_mod_cast h
    refine ⟨(WithZero.log (Valued.v (ρ i₀))).toNat, fun i => ?_, Or.inr ⟨i₀, ?_⟩⟩
    · rw [Int.toNat_of_nonneg hk0.le, hk]
      exact hi₀ i (Finset.mem_univ _)
    · rw [Int.toNat_of_nonneg hk0.le, hk]
end GlobalTheory.CompanionTheory.InertLen
