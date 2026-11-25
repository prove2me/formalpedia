-- Prove2me | solution 1 for GlobalTheory.log_translate_sub_const_of_quasiPeriodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:20.926908+00:00
-- url     : https://prove2.me/submissions/c141c86c-0b00-46ef-8085-89a3e4d399b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_EntireEqZeroOrEqZeroOfMulEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FactorCommutatorEqOfNonvanishing
import Theorems.Thm_GlobalTheory_entire_eq_zero_or_eq_zero_of_mul_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {g : ℕ} {θ ρ q : (Fin g → ℂ) → ℂ}
    {la : Fin g → ℂ} {A B : (Fin g → ℂ) →ₗ[ℂ] ℂ} {a b : ℂ} (hθ : Differentiable ℂ θ) (hθ0 : θ ≠ 0)
    (hρ : Differentiable ℂ ρ) (hq : Continuous q) (hqρ : ∀ z, Complex.exp (q z) = ρ z)
    (ha : a ≠ 0) (h1 : ∀ z, θ (z + la) = a * Complex.exp (A z) * θ z)
    (h2 : ∀ z, θ (z + la) * ρ (z + la) = b * Complex.exp (B z) * (θ z * ρ z)) (z w) :
    q (z + la) - q z - (B z - A z) = q (w + la) - q w - (B w - A w) := by
  have hA : Differentiable ℂ A := (LinearMap.toContinuousLinearMap A).differentiable
  have hB : Differentiable ℂ B := (LinearMap.toContinuousLinearMap B).differentiable
  have hρ' : Differentiable ℂ fun z => ρ (z + la) := hρ.comp (differentiable_id.add_const la)
  have hF : Differentiable ℂ fun z =>
      a * Complex.exp (A z) * ρ (z + la) - b * Complex.exp (B z) * ρ z :=
    ((hA.cexp.const_mul a).mul hρ').sub ((hB.cexp.const_mul b).mul hρ)
  have key : ∀ z, a * Complex.exp (A z) * ρ (z + la) - b * Complex.exp (B z) * ρ z = 0 := by
    rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero θ _ hθ hF (fun z => by
      have := h2 z
      rw [h1 z] at this
      linear_combination this) with h | h
    · exact absurd (funext h) hθ0
    · exact h
  have hexp : ∀ z, Complex.exp (q (z + la) - q z - (B z - A z)) = b / a := by
    intro z
    have hk := key z
    rw [← hqρ, ← hqρ] at hk
    have e1 := Complex.exp_ne_zero (q z)
    have e2 := Complex.exp_ne_zero (A z)
    have e3 := Complex.exp_ne_zero (B z)
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_sub]
    field_simp
    linear_combination hk
  have hc : Continuous fun z => q (z + la) - q z - (B z - A z) :=
    ((hq.comp (continuous_id.add continuous_const)).sub hq).sub
      (hB.continuous.sub hA.continuous)
  exact Complex.isCoveringMap_exp.const_of_comp hc
    (fun u v => Subtype.ext ((hexp u).trans (hexp v).symm)) z w
end GlobalTheory
