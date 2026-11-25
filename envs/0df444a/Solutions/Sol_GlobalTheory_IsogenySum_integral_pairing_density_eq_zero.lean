-- Prove2me | solution 1 for GlobalTheory.IsogenySum.integral_pairing_density_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:37.239891+00:00
-- url     : https://prove2.me/submissions/cfb60675-1072-4c55-af11-eb841d0d3edd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Theorems.Thm_GlobalTheory_IsogenySum_mem_lattice_of_int
import Theorems.Thm_GlobalTheory_IsogenySum_pairing_density_add
import Theorems.Thm_GlobalTheory_setIntegral_fundamentalDomain_add_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open GlobalTheory.IsogenySum
open FockTranslation
variable {ι : Type} [Fintype ι]
variable (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
  (hU : ∀ (q : ℕ) a F v, U q a F v =
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
include hU
namespace GlobalTheory.IsogenySum
theorem _root_.solution (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ Y.Sec 1) {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ (EuclideanSpace ℂ ι))
    (hb : lat b ≤ lat Y.b) (y y' : EuclideanSpace ℂ ι)
    (hint : ∀ x ∈ lat b, ∃ k : ℤ, (Hf x (y - y')).im = k) (hne : y - y' ∉ lat Y.b) :
    ∫ v in ZSpan.fundamentalDomain b,
      U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v)) = 0 := by
  obtain ⟨x, hx, hx'⟩ : ∃ x ∈ lat Y.b, cexp (2 * Real.pi * I * (Hf x (y - y')).im) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hne (mem_lattice_of_int Y fun x hx => ?_)
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 (hcon x hx)
    refine ⟨k, ?_⟩
    rw [mul_comm (k : ℂ)] at hk
    have := mul_left_cancel₀ Complex.two_pi_I_ne_zero hk
    exact_mod_cast this
  have h := setIntegral_fundamentalDomain_add_right volume b
    (fun v => U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v)))
    (fun γ hγ v => by
      obtain ⟨k, hk⟩ := hint γ hγ
      simp only [pairing_density_add U hU Y hF y y' (hb hγ), hk]
      rw [mul_comm _ ((k : ℝ) : ℂ), Complex.ofReal_intCast, Complex.exp_int_mul_two_pi_mul_I,
        one_mul]) x
  simp only [pairing_density_add U hU Y hF y y' hx] at h
  rw [integral_const_mul] at h
  have h2 := sub_eq_zero.2 h
  rw [← sub_one_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hx')
end GlobalTheory.IsogenySum
