-- Prove2me | solution 1 for GlobalTheory.PlaneTheta.theta_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:23:25.78071+00:00
-- url     : https://prove2.me/submissions/9e0a9af6-7c08-4b46-b00b-d3e6542c3b0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptotics
import Theorems.Thm_GlobalTheory_PlaneTheta_atTop_bound
import Theorems.Thm_GlobalTheory_PlaneTheta_zero_bound
import Theorems.Thm_GlobalTheory_PlaneTheta_covolume_lattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open scoped RealInnerProductSpace
open GlobalTheory GlobalTheory.PlaneTheta
namespace GlobalTheory.PlaneTheta
theorem _root_.solution : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) =O[atTop] (fun t => Real.exp (-c * t)) ∧ (fun t : ℝ => (∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) - 1 / (t * |(starRingEnd ℂ w₁ * w₂).im|)) =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  intro w₁ w₂ x₀ hw hx
  let L : PeriodPair := ⟨w₁, w₂, by
    rw [LinearIndependent.pair_iff]
    intro s t e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 hw
    constructor
    · apply mul_left_cancel₀ hw
      linear_combination w₂.im * e1 - w₂.re * e2
    · apply mul_left_cancel₀ hw
      linear_combination w₁.re * e2 - w₁.im * e1⟩
  have hsum : ∀ t : ℝ, ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2) =
      ∑' x : L.lattice, Real.exp (-Real.pi * t * ‖(x : ℂ) + x₀‖ ^ 2) := by
    intro t
    rw [← L.latticeEquivProd.symm.toEquiv.tsum_eq]
    refine tsum_congr fun p => ?_
    have := L.latticeEquiv_symm_apply p
    have e : ((L.latticeEquivProd.symm.toEquiv p : L.lattice) : ℂ) + x₀
        = x₀ + p.1 * w₁ + p.2 * w₂ := by
      change (L.latticeEquivProd.symm p).1 + x₀ = _
      rw [this]
      ring
    rw [e]
  have hu : ∀ x : L.lattice, (x : ℂ) + x₀ ≠ 0 := by
    intro x h
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 x.2
    apply hx m n
    rw [← h, ← hmn]
    ring
  obtain ⟨c₁, hc₁, h₁⟩ := atTop_bound L.lattice x₀ hu
  obtain ⟨c₂, hc₂, h₂⟩ := zero_bound L.lattice Complex.finrank_real_complex x₀
  rw [covolume_lattice] at h₂
  simp only [hsum]
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, h₁.trans (IsBigO.of_bound' ?_), h₂.trans (IsBigO.of_bound' ?_)⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_le_exp]
    nlinarith [min_le_left c₁ c₂]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : 0 < t := ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_le_exp]
    gcongr
    exact min_le_right _ _
end GlobalTheory.PlaneTheta
