-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.exists_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:17:26.940034+00:00
-- url     : https://prove2.me/submissions/92d17f13-f7dd-46cb-9444-a9c0aaab0c29

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianSumOfCounting

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
namespace GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
theorem _root_.solution {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    ∃ j : ℕ, u ≤ 2 ^ j ∧ Real.exp (-(c * u ^ 2)) ≤ wt c j := by
  classical
  have hex : ∃ j : ℕ, u ≤ 2 ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt u (one_lt_two : (1 : ℝ) < 2)
    exact ⟨j, hj.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases hj : Nat.find hex with _ | k
  · simp only [wt, if_true]
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c * u ^ 2 := by positivity
    linarith
  · have hlt : ¬ u ≤ 2 ^ k := Nat.find_min hex (by omega)
    push_neg at hlt
    have hsq : (4 : ℝ) ^ k ≤ u ^ 2 := by
      have h1 : ((2 : ℝ) ^ k) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hlt.le 2
      have h2 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      linarith
    simp only [wt, Nat.succ_ne_zero, if_false]
    apply Real.exp_le_exp.mpr
    have h3 : c * 4 ^ (k + 1) / 4 = c * 4 ^ k := by rw [pow_succ]; ring
    rw [h3]
    have := mul_le_mul_of_nonneg_left hsq hc.le
    linarith
end GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
