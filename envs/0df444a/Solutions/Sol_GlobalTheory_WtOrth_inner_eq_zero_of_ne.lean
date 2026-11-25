-- Prove2me | solution 1 for GlobalTheory.WtOrth.inner_eq_zero_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:37.61567+00:00
-- url     : https://prove2.me/submissions/afccf377-9871-4d77-887f-7a63b42631f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearOrthDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.WtOrth
namespace GlobalTheory.WtOrth
theorem _root_.solution {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsUnitary ε E) {ω ω' : Fin n → ℝ} {x y : M}
    (hx : IsWeight E ω x) (hy : IsWeight E ω' y) (hne : ω ≠ ω') : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have h := hU a a x y
  rw [hx a, hy a, inner_smul_left, inner_smul_right] at h
  simp only [Formalism.REAL.sgn, if_true, Complex.ofReal_one, one_mul, Complex.conj_ofReal] at h
  have h2 : ((ω a : ℂ) - (ω' a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (Complex.ofReal_injective (sub_eq_zero.mp h3)) ha
  · exact h3
end GlobalTheory.WtOrth
