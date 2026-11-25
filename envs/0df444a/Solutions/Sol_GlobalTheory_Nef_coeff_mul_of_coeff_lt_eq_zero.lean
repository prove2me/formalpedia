-- Prove2me | solution 1 for GlobalTheory.Nef.coeff_mul_of_coeff_lt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:54.211644+00:00
-- url     : https://prove2.me/submissions/5af7f2f4-85d6-4f27-ac0c-7abe4a2601fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomPowerSeriesEqOfRescale
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution {R : Type} [CommRing R] (φ δ : PowerSeries R) (j : ℕ)
    (h : ∀ i < j, PowerSeries.coeff i δ = 0) :
    PowerSeries.coeff j (φ * δ) = PowerSeries.constantCoeff φ * PowerSeries.coeff j δ := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, j)]
  · simp
  · rintro ⟨a, b⟩ hp hne
    have hp : a + b = j := by simpa using hp
    have hb : b < j := by
      by_contra hb
      have ha : a = 0 := by omega
      have hb' : b = j := by omega
      subst ha hb'
      exact hne rfl
    rw [h _ hb, mul_zero]
  · intro hn
    exact absurd (by simp) hn
end GlobalTheory.Nef
