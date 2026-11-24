-- Prove2me | solution 1 for GlobalTheory.ThetaRational.growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:33:06.953159+00:00
-- url     : https://prove2.me/submissions/bfa08e33-aff1-4c0b-a5c1-1bab586ceb96

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
import Theorems.Thm_GlobalTheory_ThetaRational_exists_rep
import Theorems.Thm_GlobalTheory_ThetaRational_exists_lower_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {θ : V → W} {f : V → ℂ} {d : ℕ} {Λ K : Set V}
omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [NormedSpace ℂ V]
namespace GlobalTheory.ThetaRational
theorem _root_.solution (hK : IsCompact K) (hθ : Continuous θ) (hf : Continuous f) (hN : ∀ z, θ z ≠ 0)
    (hP : ∀ z, ∃ k ∈ K, z - k ∈ Λ)
    (hL : ∀ l ∈ Λ, ∃ κ : V → ℂ, Continuous κ ∧ ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧
      f (z + l) = κ z ^ d * f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : ℂ × V, ‖e.1 ^ d * f e.2‖ ≤ C * ‖e.1 • θ e.2‖ ^ d := by
  obtain ⟨ε, hε, hεK⟩ := exists_lower_bound hK hθ hN
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B 0 / ε ^ d, by positivity, fun e => ?_⟩
  obtain ⟨e', he', h1, h2⟩ := exists_rep hP hL e
  rw [← h1, ← h2, norm_mul, norm_smul, norm_pow, mul_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h3 := (hB _ he').trans (le_max_left B 0)
  have h4 := hεK _ he'
  calc ‖e'.1‖ ^ d * ‖f e'.2‖ * ε ^ d ≤ ‖e'.1‖ ^ d * max B 0 * ‖θ e'.2‖ ^ d := by gcongr
    _ = _ := by ring
end GlobalTheory.ThetaRational
