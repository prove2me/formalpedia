-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.exists_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:50.29313+00:00
-- url     : https://prove2.me/submissions/953c9011-3e97-4539-b134-5971c46c580c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_Om3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution (N r : ℝ) (x : ℝ × ℝ) :
    ∃ a ∈ coneI r, ∃ b ∈ Om3 N r, x = midpoint ℝ a b := by
  obtain ⟨u, v⟩ := x
  set B : ℝ := |r| + 1 with hB
  set A : ℝ := |r| + |r + 1 - 2 * N + 2 * u| + |r + 1 - 2 * N + 2 * u + 4 * v - 2 * B| + 1 with hA
  have h₀ := le_abs_self r
  have h₁ := le_abs_self (r + 1 - 2 * N + 2 * u)
  have h₂ := le_abs_self (r + 1 - 2 * N + 2 * u + 4 * v - 2 * B)
  have h₃ := abs_nonneg r
  have h₄ := abs_nonneg (r + 1 - 2 * N + 2 * u)
  have h₅ := abs_nonneg (r + 1 - 2 * N + 2 * u + 4 * v - 2 * B)
  refine ⟨(A, B), ?_, (2 * u - A, 2 * v - B), ?_, ?_⟩
  · simp only [coneI, Set.mem_setOf_eq]
    constructor <;> linarith
  · rw [mem_Om3]
    simp only
    constructor <;> linarith
  · rw [midpoint_eq_smul_add]
    ext <;> simp <;> ring
end GlobalTheory.CompanionTheory.RgEisGal
