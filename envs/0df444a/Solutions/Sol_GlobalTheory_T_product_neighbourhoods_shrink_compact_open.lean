-- Prove2me | solution 1 for GlobalTheory.T.product_neighbourhoods_shrink_compact_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:25:36.50109+00:00
-- url     : https://prove2.me/submissions/71114cf6-8868-435b-a934-e6087aa81cdc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductNeighbourhoodsShrinkCompactOpen
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductNeighbourhoodsShrinkCompactOpenStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_BigCell_preimage_box_shrinking


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [Finite ι] (e : G ≃ₜ+ (ι → A)) (U : ℕ → Set A), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : A) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : A)).smallSets → (∀ k, IsCompact (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ IsOpen (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ (0 : G) ∈ e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ Filter.Tendsto (fun k => e ⁻¹' Set.pi Set.univ (fun _ => U k)) Filter.atTop (nhds (0 : G)).smallSets := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking | exact GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking | (intros; apply GlobalTheory.CompanionTheory.BigCell.preimage_box_shrinking <;> assumption)
end _root_.GlobalTheory.T
