-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.aesm_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:33.753706+00:00
-- url     : https://prove2.me/submissions/58bad76c-098d-4a30-8016-9f3a8cee2eb4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {U : Set ℂ}
namespace GlobalTheory.CompanionTheory.HolMean
theorem _root_.solution (hU : IsOpen U) (G : ℂ → Ω → ℂ)
    (hd : ∀ ω, DifferentiableOn ℂ (fun z => G z ω) U) {z : ℂ} (hz : z ∈ U)
    (hm : ∀ x : ℝ, z + x ∈ U → AEStronglyMeasurable (G (z + x)) μ) :
    AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) z) μ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨t, htpos, htlt, ht0⟩ : ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧ (∀ n, t n < δ) ∧
      Tendsto t atTop (𝓝 0) :=
    ⟨fun n => δ / ((n : ℝ) + 2), fun n => div_pos hδ (by positivity),
     fun n => div_lt_self hδ (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith),
     tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)⟩
  have hmem : ∀ n, z + (t n : ℂ) ∈ U := by
    intro n
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (htpos n)]
    exact htlt n
  have hz0 : AEStronglyMeasurable (G z) μ := by simpa using hm 0 (by simpa using hz)
  have htc : Tendsto (fun n => (t n : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 0).comp ht0
      rw [Complex.ofReal_zero] at this
      exact this
    · exact Set.mem_compl_singleton_iff.mpr (Complex.ofReal_ne_zero.mpr (htpos n).ne')
  refine aestronglyMeasurable_of_tendsto_ae
    (f := fun n ω => ((t n : ℂ))⁻¹ • (G (z + t n) ω - G z ω)) atTop (fun n => ?_)
    (ae_of_all μ fun ω => ?_)
  · exact ((hm (t n) (hmem n)).sub hz0).const_smul ((t n : ℂ))⁻¹
  · have hda : HasDerivAt (fun w => G w ω) (deriv (fun w => G w ω) z) z :=
      (((hd ω) z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
    exact hda.tendsto_slope_zero.comp htc
end GlobalTheory.CompanionTheory.HolMean
