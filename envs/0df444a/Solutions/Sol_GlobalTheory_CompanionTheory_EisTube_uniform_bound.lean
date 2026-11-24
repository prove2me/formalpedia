-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:17.595088+00:00
-- url     : https://prove2.me/submissions/5b641a40-2612-4c8e-8d6a-7d09d9a5b84b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {ι : Type} [Fintype ι] {P : Type u} {h : P → ℝ} (hh : ∀ p, 0 ≤ h p)
    {ψ : P → (ι → ℝ) → ℂ}
    (hψ : ∀ v : ι → ℝ, ∃ C : ℝ, ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i)))
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * (R * ∑ i, |t i|))) := by
  classical
  choose Cf hCf using hψ
  let vec : (ι → Bool) → ι → ℝ := fun σ i => R * (if σ i then 1 else -1)
  refine ⟨∑ σ : ι → Bool, |Cf (vec σ)|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun p t => ?_⟩
  let σ : ι → Bool := fun i => decide (0 ≤ t i)
  have hs : ∑ i, vec σ i * t i = R * ∑ i, |t i| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : 0 ≤ t i
    · simp [vec, σ, hi, abs_of_nonneg hi]
    · have hi' : t i < 0 := not_le.mp hi
      simp [vec, σ, hi, abs_of_neg hi']
  have h1 := hCf (vec σ) p t
  rw [hs] at h1
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_right ?_ (hh p)
  exact (le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ : ι → Bool => |Cf (vec σ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ σ))
end GlobalTheory.CompanionTheory.EisTube
