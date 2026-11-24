-- Prove2me | solution 1 for GlobalTheory.SCV.differentiableOn_tsum_of_normal_on_compacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:40.312026+00:00
-- url     : https://prove2.me/submissions/39ade1ee-2252-450f-837c-504e7cbb8247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_hasSumLocallyUniformlyOn_iteratedFDeriv
import Theorems.Thm_GlobalTheory_SCV_hasSumLocallyUniformlyOn_of_locally_normal
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_tsum_of_locally_normal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} {l : Filter ι} {F : ι → E → V} {f : E → V} {U : Set E}
namespace GlobalTheory.SCV
theorem _root_.solution (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ K, ‖F i z‖ ≤ u i) :
    DifferentiableOn ℂ (fun z => ∑' i, F i z) U ∧
      ∀ k : ℕ, HasSumLocallyUniformlyOn (fun i => iteratedFDeriv ℂ k (F i))
        (iteratedFDeriv ℂ k (fun w => ∑' i, F i w)) U := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i := by
    intro x hx
    obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
    exact ⟨K, hKx, hle K hKU hK⟩
  exact ⟨differentiableOn_tsum_of_locally_normal hU hF h, fun k =>
    hasSumLocallyUniformlyOn_iteratedFDeriv hU
      (hasSumLocallyUniformlyOn_of_locally_normal h) hF k⟩
end GlobalTheory.SCV
