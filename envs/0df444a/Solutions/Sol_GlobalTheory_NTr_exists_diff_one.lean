-- Prove2me | solution 1 for GlobalTheory.NTr.exists_diff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:51:48.296679+00:00
-- url     : https://prove2.me/submissions/e4d0e279-f68b-4495-881f-31661d2c0dad

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
import Theorems.Thm_GlobalTheory_NTr_um_sub
import Theorems.Thm_GlobalTheory_NTr_exists_sq_close
import Theorems.Thm_GlobalTheory_NTr_fixed_eq
import Theorems.Thm_GlobalTheory_NTr_exists_far

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
theorem _root_.solution (h2 : ‖(2 : F)‖ < 1) : ∃ w : E, ‖w‖ ≤ 1 ∧ ‖w - star w‖ = 1 := by
  haveI := hU.ultraE
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨w, hw, hfar⟩ := exists_far (F := F) (E := E)
  refine ⟨w, hw.le, le_antisymm ?_ ?_⟩
  · exact (um_sub _ _).trans (by rw [hU.norm_star, hw, max_self])
  · by_contra hlt
    push_neg at hlt
    set N := w * star w with hN
    have hNs : star N = N := by rw [hN, star_mul, star_star, mul_comm]
    set n := Algebra.trace F E N / 2
    have hn : algebraMap F E n = N := fixed_eq hNs
    have hnn : ‖n‖ = 1 := by
      rw [← norm_algebraMap' E n, hn, hN, norm_mul, hU.norm_star, hw, one_mul]
    obtain ⟨s, hs1, hs⟩ := exists_sq_close h2 n hnn.le
    set S := algebraMap F E s
    have hS : ‖S‖ ≤ 1 := by rw [norm_algebraMap']; exact hs1
    have hsq : ‖w ^ 2 - S ^ 2‖ < 1 := by
      have : w ^ 2 - S ^ 2 = w * (w - star w) + (N - algebraMap F E (s ^ 2)) := by
        rw [hN, map_pow]; ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul, hw, one_mul]; exact hlt
      · rw [← hn, ← map_sub, norm_algebraMap']; exact hs
    have hm : ‖w - S‖ = 1 :=
      le_antisymm ((um_sub _ _).trans (max_le hw.le hS)) (hfar s)
    have h2S : ‖2 * S‖ < 1 := by
      rw [show (2 : E) * S = algebraMap F E (2 * s) by rw [map_mul, map_ofNat], norm_algebraMap', norm_mul]
      calc ‖(2 : F)‖ * ‖s‖ ≤ ‖(2 : F)‖ * 1 := mul_le_mul_of_nonneg_left hs1 (norm_nonneg _)
        _ < 1 := by simpa using h2
    have hp : ‖w + S‖ = 1 := by
      have : w + S = (w - S) + 2 * S := by ring
      rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hm]; exact h2S.ne'), hm]
      exact max_eq_left h2S.le
    have : w ^ 2 - S ^ 2 = (w - S) * (w + S) := by ring
    rw [this, norm_mul, hm, hp] at hsq
    norm_num at hsq
end GlobalTheory.NTr
