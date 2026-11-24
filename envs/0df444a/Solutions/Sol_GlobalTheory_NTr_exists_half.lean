-- Prove2me | solution 1 for GlobalTheory.NTr.exists_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:44.103002+00:00
-- url     : https://prove2.me/submissions/0539effd-6bad-41d5-9890-7b8a66b924ec

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
import Theorems.Thm_GlobalTheory_NTr_exists_diff_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
namespace GlobalTheory.NTr
theorem _root_.solution (F : Type) {E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] : ∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1 := by
  haveI := hU.ultraF
  haveI := hU.charZero
  by_cases h2 : ‖(2 : F)‖ = 1
  · refine ⟨algebraMap F E (1 / 2), ?_, ?_⟩
    · rw [norm_algebraMap', norm_div, h2, norm_one]; norm_num
    · rw [hU.star_fix, ← map_add]; norm_num
  · have h2' : ‖(2 : F)‖ < 1 := by
      refine lt_of_le_of_ne ?_ h2
      have := IsUltrametricDist.norm_add_le_max (1 : F) 1
      norm_num at this ⊢
      simpa [one_add_one_eq_two] using this
    obtain ⟨w, hw, hd⟩ := exists_diff_one (E := E) h2'
    have hd0 : w - star w ≠ 0 := by
      intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
    refine ⟨w / (w - star w), ?_, ?_⟩
    · rw [norm_div, hd, div_one]; exact hw
    · rw [star_div₀, star_sub, star_star]
      have : star w - w = -(w - star w) := by ring
      rw [this, div_neg, ← sub_eq_add_neg, ← sub_div, div_self hd0]
end GlobalTheory.NTr
