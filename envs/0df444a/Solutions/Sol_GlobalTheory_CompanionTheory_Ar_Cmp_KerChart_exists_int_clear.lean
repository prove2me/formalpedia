-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.KerChart.exists_int_clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:35:59.081077+00:00
-- url     : https://prove2.me/submissions/511c6554-3eb7-488c-a1cd-58425d08435c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MapMemChartIdealOfAevalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
open MvPolynomial ReciprocityTheory.AnForm.R
variable {σ : Type}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
theorem _root_.solution (G : MvPolynomial σ ℚ) :
    ∃ (n : ℤ) (G₀ : MvPolynomial σ ℤ), n ≠ 0 ∧
      map (Int.castRingHom ℚ) G₀ = C (n : ℚ) * G := by
  induction G using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, C a.num, by exact_mod_cast a.den_nz, ?_⟩
    rw [map_C, ← C_mul]
    congr 1
    simp [Rat.den_mul_eq_num]
  | add f g hf hg =>
    obtain ⟨n₁, F, h₁, e₁⟩ := hf
    obtain ⟨n₂, F', h₂, e₂⟩ := hg
    refine ⟨n₁ * n₂, C n₂ * F + C n₁ * F', mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add, map_mul, map_C, e₁, e₂]
    simp only [eq_intCast, Int.cast_mul, C_mul]
    ring
  | mul_X f i hf =>
    obtain ⟨n, F, h, e⟩ := hf
    exact ⟨n, F * X i, h, by rw [map_mul, map_X, e, mul_assoc]⟩
end GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
