-- Prove2me | solution 1 for GlobalTheory.NTr.exists_far
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:02:44.6728+00:00
-- url     : https://prove2.me/submissions/d86dd324-e744-464c-ba76-af70f9d1ea1b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
import Theorems.Thm_GlobalTheory_NTr_um_sub

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
theorem _root_.solution : ∃ w : E, ‖w‖ = 1 ∧ ∀ c : F, 1 ≤ ‖w - algebraMap F E c‖ := by
  haveI := hU.ultraE
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨y, hy⟩ := hU.star_ne
  have hyF : ∀ c : F, y - algebraMap F E c ≠ 0 := by
    intro c hc
    apply hy
    rw [sub_eq_zero.mp hc, hU.star_fix]
  obtain ⟨c0, -, hmin⟩ := (isCompact_closedBall (0 : F) ‖y‖).exists_isMinOn
    ⟨0, by simp⟩ (f := fun c => ‖y - algebraMap F E c‖)
    (by fun_prop)
  have hall : ∀ c : F, ‖y - algebraMap F E c0‖ ≤ ‖y - algebraMap F E c‖ := by
    intro c
    by_cases hc : ‖c‖ ≤ ‖y‖
    · exact hmin (by simpa using hc)
    · push_neg at hc
      have h0 : ‖y - algebraMap F E c0‖ ≤ ‖y‖ := by simpa using hmin (a := 0) (by simp)
      have : ‖c‖ ≤ max ‖y‖ ‖y - algebraMap F E c‖ := by
        have := um_sub y (y - algebraMap F E c)
        simpa [norm_algebraMap'] using this
      have : ‖y‖ < ‖y - algebraMap F E c‖ := by
        rcases le_max_iff.mp this with h | h
        · exact absurd (hc.trans_le h) (lt_irrefl _)
        · exact hc.trans_le h
      linarith
  set z := y - algebraMap F E c0 with hzdef
  have hz0 : z ≠ 0 := hyF c0
  obtain ⟨x, hx⟩ := hU.unram z
  have hxpos : 0 < ‖x‖ := by rw [← hx]; exact norm_pos_iff.mpr hz0
  have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
  have hX0 : algebraMap F E x ≠ 0 := by simpa using hx0
  refine ⟨z / algebraMap F E x, ?_, ?_⟩
  · rw [norm_div, norm_algebraMap', ← hx, div_self (norm_pos_iff.mpr hz0).ne']
  · intro c
    have : z / algebraMap F E x - algebraMap F E c
        = (y - algebraMap F E (c0 + x * c)) / algebraMap F E x := by
      rw [hzdef]; field_simp; rw [map_add, map_mul]; ring
    rw [this, norm_div, norm_algebraMap', le_div_iff₀ hxpos, one_mul, ← hx]
    exact hall _
end GlobalTheory.NTr
