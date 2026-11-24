-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatSum.pt_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:38.542827+00:00
-- url     : https://prove2.me/submissions/28ccf7d9-f2a2-499b-8db8-c01a3e0879a4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum
namespace GlobalTheory.CompanionTheory.SW.LatSum
theorem _root_.solution {t u y : ℝ} (ht : 0 < t) (hy : t ≤ y) (hu : y ≤ u) (m : ℕ) :
    (u ^ (m + 2))⁻¹ ≤ (1 + 1 / t) * (y ^ m)⁻¹ * (1 / u - 1 / (u + 1)) := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 < u := by linarith
  have h1 : 1 / u - 1 / (u + 1) = (u * (u + 1))⁻¹ := by
    field_simp
    ring
  have h2 : (u ^ 2)⁻¹ ≤ (1 + 1 / t) * (u * (u + 1))⁻¹ := by
    have h5 : 1 / u ≤ 1 / t := one_div_le_one_div_of_le ht (by linarith)
    have h3 : (u ^ 2)⁻¹ = (1 + 1 / u) * (u * (u + 1))⁻¹ := by
      field_simp
    rw [h3]
    have : 0 ≤ (u * (u + 1))⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) this
  have h4 : (u ^ m)⁻¹ ≤ (y ^ m)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ hy0.le hu m
  calc (u ^ (m + 2))⁻¹ = (u ^ m)⁻¹ * (u ^ 2)⁻¹ := by rw [pow_add, mul_inv]
    _ ≤ (y ^ m)⁻¹ * ((1 + 1 / t) * (u * (u + 1))⁻¹) :=
        mul_le_mul h4 h2 (by positivity) (by positivity)
    _ = (1 + 1 / t) * (y ^ m)⁻¹ * (1 / u - 1 / (u + 1)) := by rw [h1]; ring
end GlobalTheory.CompanionTheory.SW.LatSum
