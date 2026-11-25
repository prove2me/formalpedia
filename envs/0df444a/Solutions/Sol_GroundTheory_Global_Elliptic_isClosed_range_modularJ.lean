-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.isClosed_range_modularJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:59.954296+00:00
-- url     : https://prove2.me/submissions/3410df17-eeb7-4b74-90a2-b60af279a2bb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantSurjective
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_le_norm_modularJ
import Theorems.Thm_GroundTheory_Global_Elliptic_modularJC_coe
import Theorems.Thm_GroundTheory_Global_Elliptic_differentiableOn_modularJC
import Theorems.Thm_GroundTheory_Global_Elliptic_im_pos_of_mem_fdBelow
import Theorems.Thm_GroundTheory_Global_Elliptic_isCompact_fdBelow
import Theorems.Thm_GroundTheory_Global_Elliptic_modularJ_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology Set
open scoped PeriodPair Real Modular
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution : IsClosed (range modularJ) := by
  refine closure_subset_iff_isClosed.1 fun w hw ↦ ?_
  obtain ⟨A, hA⟩ := exists_le_norm_modularJ (‖w‖ + 1)
  have hK : IsCompact (modularJC '' fdBelow A) :=
    (isCompact_fdBelow A).image_of_continuousOn
      (differentiableOn_modularJC.continuousOn.mono fun z hz ↦ im_pos_of_mem_fdBelow hz)
  have hsub : range modularJ ⊆ modularJC '' fdBelow A ∪ {y | ‖w‖ + 1 ≤ ‖y‖} := by
    rintro _ ⟨τ, rfl⟩
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    rw [← modularJ_smul g τ]
    by_cases him : A ≤ (g • τ).im
    · exact Or.inr (hA _ him)
    · refine Or.inl ⟨(g • τ : ℍ), ⟨hg.1, hg.2, (g • τ).im_pos.le, ?_⟩, modularJC_coe _⟩
      exact (not_le.1 him).le
  have hclosed : IsClosed (modularJC '' fdBelow A ∪ {y : ℂ | ‖w‖ + 1 ≤ ‖y‖}) :=
    hK.isClosed.union (isClosed_le continuous_const continuous_norm)
  rcases closure_minimal hsub hclosed hw with h | h
  · obtain ⟨z, hz, rfl⟩ := h
    exact ⟨ofComplex z, rfl⟩
  · have h' : ‖w‖ + 1 ≤ ‖w‖ := h
    linarith
end GroundTheory.Global.Elliptic
