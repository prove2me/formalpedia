-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.sameOrbit_of_proj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:20:37.910137+00:00
-- url     : https://prove2.me/submissions/ccba0529-0167-4522-a4de-5f52b8859c3d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndCone
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_blockNorm_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
theorem _root_.solution {z z' : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : proj z = proj z') : SameOrbit z z' := by
  have key : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ ∀ i, z ⟨k, i⟩ = c * z' ⟨k, i⟩ := by
    intro k
    obtain ⟨j, hj⟩ := hz k
    obtain ⟨j', hj'⟩ := hz' k
    have hN := blockNorm_ne_zero hj
    have hN' := blockNorm_ne_zero hj'
    have hp : ∀ a b, z ⟨k, a⟩ * starRingEnd ℂ (z ⟨k, b⟩) / ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) =
        z' ⟨k, a⟩ * starRingEnd ℂ (z' ⟨k, b⟩) / ((∑ l, ‖z' ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) :=
      fun a b => congrFun h ⟨k, a, b⟩
    have hcj : starRingEnd ℂ (z ⟨k, j⟩) ≠ 0 := (map_ne_zero _).2 hj
    have hw : z' ⟨k, j⟩ ≠ 0 := by
      intro h0
      have := hp j j
      rw [h0, zero_mul, zero_div, div_eq_zero_iff] at this
      rcases this with h1 | h1
      · exact (mul_ne_zero hj hcj) h1
      · exact hN h1
    have hcw : starRingEnd ℂ (z' ⟨k, j⟩) ≠ 0 := (map_ne_zero _).2 hw
    refine ⟨starRingEnd ℂ (z' ⟨k, j⟩) * ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) /
      (((∑ l, ‖z' ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (z ⟨k, j⟩)),
      div_ne_zero (mul_ne_zero hcw hN) (mul_ne_zero hN' hcj), fun i => ?_⟩
    have := hp i j
    rw [div_eq_div_iff hN hN'] at this
    field_simp
    linear_combination this
  choose c hc hci using key
  exact ⟨c, hc, funext fun q => hci q.1 q.2⟩
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
