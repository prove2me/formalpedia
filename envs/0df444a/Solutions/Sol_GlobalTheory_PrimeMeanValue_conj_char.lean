-- Prove2me | solution 1 for GlobalTheory.PrimeMeanValue.conj_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:30:53.765525+00:00
-- url     : https://prove2.me/submissions/6abb61b7-738c-4eb6-9b1f-a3e45288ef8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BrunTitchmarshExistsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeMeanValueCharactersTwistIntegralLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.PrimeMeanValue
namespace GlobalTheory.PrimeMeanValue
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {u : ZMod q} (hu : IsUnit u) :
    (starRingEnd ℂ) (χ u) = χ u⁻¹ := by
  have h1 : χ u * χ u⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
  have h2 : ‖χ u‖ = 1 := by
    obtain ⟨v, rfl⟩ := hu
    exact χ.unit_norm_eq_one v
  have h3 : χ u * (starRingEnd ℂ) (χ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]; simp
  have h0 : χ u ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact mul_left_cancel₀ h0 (h3.trans h1.symm)
end GlobalTheory.PrimeMeanValue
