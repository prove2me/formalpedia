-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatSum.hasSum_tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:36.471883+00:00
-- url     : https://prove2.me/submissions/02973a2b-8bba-4b94-89b3-284362b0ad9b

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
theorem _root_.solution {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + y + 1)) (1 / y) := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + y + 1) := by
    intro n
    have h0 : 0 < (n : ℝ) + y := by positivity
    have : 1 / ((n : ℝ) + y + 1) ≤ 1 / ((n : ℝ) + y) :=
      one_div_le_one_div_of_le h0 (by linarith)
    linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + y) - 1 / ((i : ℝ) + y + 1))
      = 1 / y - 1 / ((n : ℝ) + y) := by
    intro n
    have := Finset.sum_range_sub' (fun i : ℕ => 1 / ((i : ℝ) + y)) n
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ring
  simp_rw [hpart]
  have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + y)) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right _ y tendsto_natCast_atTop_atTop)
  simpa using tendsto_const_nhds.sub h0
end GlobalTheory.CompanionTheory.SW.LatSum
