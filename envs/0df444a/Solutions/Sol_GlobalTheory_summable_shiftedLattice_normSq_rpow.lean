-- Prove2me | solution 1 for GlobalTheory.summable_shiftedLattice_normSq_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:57.529441+00:00
-- url     : https://prove2.me/submissions/6dcc00fc-839e-4dbf-9a10-e3787647e5ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptoticsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open GlobalTheory
open Set MeasureTheory
open scoped Topology
namespace GlobalTheory
theorem _root_.solution (w₁ w₂ x₀ : ℂ)
    (h : (starRingEnd ℂ w₁ * w₂).im ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : ℤ × ℤ => (‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) ^ (-σ) := by
  have hli : ∀ a b : ℝ, a • w₁ + b • w₂ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 := congrArg Complex.re hab
    have h2 := congrArg Complex.im hab
    simp at h1 h2 h
    have h' : w₁.re * w₂.im - w₁.im * w₂.re ≠ 0 := by
      intro h0; apply h; linarith
    constructor
    · apply mul_right_cancel₀ h'
      linear_combination w₂.im * h1 - w₂.re * h2
    · apply mul_right_cancel₀ h'
      linear_combination w₁.re * h2 - w₁.im * h1
  let L : PeriodPair := ⟨w₁, w₂, LinearIndependent.pair_iff.mpr hli⟩
  have hs := ZLattice.summable_norm_sub_rpow L.lattice (-(2 * σ)) (by simp; linarith) (-x₀)
  let φ : ℤ × ℤ → L.lattice := fun p =>
    ⟨p.1 * w₁ + p.2 * w₂, PeriodPair.mem_lattice.mpr ⟨p.1, p.2, rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro p q hpq
    have e : (p.1 * w₁ + p.2 * w₂ : ℂ) = q.1 * w₁ + q.2 * w₂ := congrArg Subtype.val hpq
    have := hli (p.1 - q.1) (p.2 - q.2) (by simp; linear_combination e)
    simp only [sub_eq_zero, Int.cast_inj] at this
    exact Prod.ext this.1 this.2
  refine (hs.comp_injective hφ).congr fun p => ?_
  simp only [Function.comp, φ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  · congr 1; ring
  · push_cast; ring
end GlobalTheory
