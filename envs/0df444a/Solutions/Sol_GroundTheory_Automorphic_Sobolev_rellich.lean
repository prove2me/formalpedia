-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.rellich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:32.954052+00:00
-- url     : https://prove2.me/submissions/ba4fdc11-6c38-460a-b16a-baabefe7aec6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_cutoff_eq_self
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_isCompactOperator_rellichOp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_bessel_inclusion_eq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_inclusion_sub_eq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_inclusion_le_interpolation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open Filter Topology
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s t : ℝ} (hts : t < s) {K : Set E} (hK : IsCompact K)
    (u : ℕ → SobolevSpace E ℂ s) {M : ℝ} (hM : ∀ j, ‖u j‖ ≤ M)
    (hsupp : ∀ j, Distribution.IsVanishingOn (SobolevSpace.toDistribution (u j)) Kᶜ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : SobolevSpace E ℂ t,
      Tendsto (fun j ↦ SobolevSpace.inclusion hts.le (u (φ j))) atTop (𝓝 v) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  set χ := cutoff (E := E) R
  have hu : ∀ j, smulLeftCLM ℂ (χ : E → ℂ) (SobolevSpace.toDistribution (u j)) =
      SobolevSpace.toDistribution (u j) := fun j ↦
    smulLeftCLM_cutoff_eq_self _ ((hsupp j).mono (Set.compl_subset_compl.2 hR))
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  set N : ℝ := max n (s - t) + 1
  have hN : n < 2 * N := by
    have : n ≤ max n (s - t) := le_max_left _ _
    have hn : 0 ≤ n := Nat.cast_nonneg _
    linarith
  have hN0 : 0 ≤ N := by
    have : s - t ≤ max n (s - t) := le_max_right _ _
    linarith
  have hrt : s - N < t := by
    have : s - t ≤ max n (s - t) := le_max_right _ _
    linarith
  have hrs : s - N ≤ s := by linarith
  set T := rellichOp (s := s) χ hN
  set G : ℕ → Lp ℂ 2 (volume : Measure E) := fun j ↦ 𝓕 (SobolevSpace.bessel s (u j))
  set M' := max M 0
  have hG : ∀ j, G j ∈ Metric.closedBall (0 : Lp ℂ 2 (volume : Measure E)) M' := fun j ↦ by
    rw [Metric.mem_closedBall, dist_zero_right, Lp.norm_fourier_eq, ← SobolevSpace.norm_def]
    exact (hM j).trans (le_max_left _ _)
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompactOperator_rellichOp (s := s) χ hN).isCompact_closure_image_closedBall
    M' |>.tendsto_subseq (x := fun j ↦ T (G j)) fun j ↦ subset_closure ⟨G j, hG j, rfl⟩
  refine ⟨φ, hφ, ?_⟩

  have hC : CauchySeq (fun j ↦ T (G (φ j))) := hlim.cauchySeq
  have hdist : ∀ i j, dist (SobolevSpace.inclusion hrs (u (φ i)))
      (SobolevSpace.inclusion hrs (u (φ j))) = dist (T (G (φ i))) (T (G (φ j))) := by
    intro i j
    rw [dist_eq_norm, dist_eq_norm, norm_inclusion_sub_eq,
      fourier_bessel_inclusion_eq χ hN _ (hu _), fourier_bessel_inclusion_eq χ hN _ (hu _)]

  set θ := (s - t) / (s - (s - N))
  set α := (t - (s - N)) / (s - (s - N))
  have hθ : 0 < θ := div_pos (by linarith) (by linarith)
  have hα : 0 ≤ α := (div_pos (by linarith) (by linarith)).le
  have hinterp : ∀ i j, dist (SobolevSpace.inclusion hts.le (u (φ i)))
      (SobolevSpace.inclusion hts.le (u (φ j))) ≤
        (2 * M') ^ α * dist (T (G (φ i))) (T (G (φ j))) ^ θ := by
    intro i j
    have h := norm_inclusion_le_interpolation hrt hts (u (φ i) - u (φ j))
    rw [map_sub, map_sub] at h
    rw [dist_eq_norm, ← hdist, dist_eq_norm]
    refine h.trans ?_
    gcongr
    calc ‖u (φ i) - u (φ j)‖ ≤ ‖u (φ i)‖ + ‖u (φ j)‖ := norm_sub_le _ _
      _ ≤ M' + M' := add_le_add ((hM _).trans (le_max_left _ _)) ((hM _).trans (le_max_left _ _))
      _ = 2 * M' := by ring
  have hcauchy : CauchySeq (fun j ↦ SobolevSpace.inclusion hts.le (u (φ j))) := by
    rw [Metric.cauchySeq_iff] at hC ⊢
    intro ε hε
    set c := (2 * M') ^ α + 1
    have hc : 0 < c := by positivity
    obtain ⟨K₀, hK₀⟩ := hC ((ε / c) ^ (1 / θ)) (by positivity)
    refine ⟨K₀, fun i hi j hj ↦ ?_⟩
    have h1 := hK₀ i hi j hj
    have h2 : dist (T (G (φ i))) (T (G (φ j))) ^ θ < ε / c := by
      calc dist (T (G (φ i))) (T (G (φ j))) ^ θ < ((ε / c) ^ (1 / θ)) ^ θ :=
            Real.rpow_lt_rpow dist_nonneg h1 hθ
        _ = ε / c := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hθ.ne', Real.rpow_one]
    calc dist _ _ ≤ (2 * M') ^ α * dist (T (G (φ i))) (T (G (φ j))) ^ θ := hinterp i j
      _ ≤ c * dist (T (G (φ i))) (T (G (φ j))) ^ θ := by
          gcongr; linarith
      _ < c * (ε / c) := by gcongr
      _ = ε := by field_simp
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨v, hv⟩
end GroundTheory.Automorphic.Sobolev
