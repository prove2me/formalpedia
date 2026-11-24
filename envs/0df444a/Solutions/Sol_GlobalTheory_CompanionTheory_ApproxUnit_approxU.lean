-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ApproxUnit.approxU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:33:20.124209+00:00
-- url     : https://prove2.me/submissions/65865ad2-da15-4915-a93d-7b0780efac74

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CvAdjEqAvg
import Theorems.Thm_GlobalTheory_CompanionTheory_ApproxUnit_avg_le
import Theorems.Thm_GlobalTheory_CompanionTheory_ApproxUnit_cv_eq_avg
import Theorems.Thm_GlobalTheory_CompanionTheory_ApproxUnit_cv_adj_eq_avg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ApproxUnit
namespace GlobalTheory.CompanionTheory.ApproxUnit
theorem _root_.solution : CvTest → TwoUnif → ApproxU := by
  intro hcv htu X φ ε hφ hε
  obtain ⟨W₀, hW₀, hW⟩ := htu X φ ε hφ hε
  refine ⟨W₀ ∩ W₀⁻¹, Filter.inter_mem hW₀ (inv_mem_nhds_one _ hW₀), ?_⟩
  intro ψ hb hsub y
  have hsupp : ∀ w, ‖ψ w⁻¹‖ ≠ 0 → w ∈ W₀ ∧ w⁻¹ ∈ W₀ := by
    intro w hw
    have h1 : w⁻¹ ∈ tsupport ψ := subset_tsupport _ (norm_ne_zero_iff.1 hw)
    have h2 := hsub h1
    exact ⟨by simpa using h2.2, h2.1⟩
  have hb0 : ∀ w, 0 ≤ ‖ψ w⁻¹‖ := fun w => norm_nonneg _
  have key : ∀ z ∈ W₀, ‖cv X.μ φ ψ (z * y) - φ y‖ ≤ ε := by
    intro z hz
    rw [cv_eq_avg X φ ψ hb]
    refine avg_le X.μ (fun w => ‖ψ w⁻¹‖) (fun w => φ (z * y * w)) (φ y) ε hb0 hb.2.2
      (Continuous.aestronglyMeasurable (hφ.1.comp (by fun_prop))) ?_
    intro w hw
    exact hW z hz w (hsupp w hw).1 y
  refine ⟨?_, ?_⟩
  · simpa using key 1 (mem_of_mem_nhds hW₀)
  · rw [cv_adj_eq_avg X _ ψ hb]
    have hc : Continuous (cv X.μ φ ψ) := (hcv X φ ψ hφ hb.1).1.1
    refine avg_le X.μ (fun w => ‖ψ w⁻¹‖) (fun z => cv X.μ φ ψ (z⁻¹ * y)) (φ y) ε hb0 hb.2.2
      (Continuous.aestronglyMeasurable (hc.comp (by fun_prop))) ?_
    intro z hz
    exact key z⁻¹ (hsupp z hz).2
end GlobalTheory.CompanionTheory.ApproxUnit
