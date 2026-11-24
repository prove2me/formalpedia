-- Prove2me | solution 1 for GlobalTheory.UpqExpChart.exists_ball_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:49:44.51524+00:00
-- url     : https://prove2.me/submissions/86fb3e4b-5c71-46e1-bc15-e45c47ef0dd0

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.UpqExpChart
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.UpqExpChart
theorem _root_.solution {W : Set (Matrix n n ℂ)} (hW : W ∈ 𝓝 (0 : Matrix n n ℂ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Z : Matrix n n ℂ, ∑ i, ∑ j, ‖Z i j‖ < δ → Z ∈ W := by
  open scoped Matrix.Norms.Elementwise in
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hW
  refine ⟨δ, hδ, fun Z hZ => h ?_⟩
  open scoped Matrix.Norms.Elementwise in
  rw [mem_ball_zero_iff, Matrix.norm_lt_iff hδ]
  intro i j
  refine lt_of_le_of_lt ?_ hZ
  calc ‖Z i j‖ ≤ ∑ j, ‖Z i j‖ :=
        Finset.single_le_sum (f := fun j => ‖Z i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, ‖Z i j‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
end GlobalTheory.UpqExpChart
