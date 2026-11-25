-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.prefixLe_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:32.879972+00:00
-- url     : https://prove2.me/submissions/f70ee7f6-4748-4be9-92c0-73aad2e7ac0d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_PrefixLe_mono
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_PrefixLe_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_iff_exists
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_exists_prefix_max
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_mem_span_of_prefixLe_zero
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_of_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {x : Γ} {n : ℕ} {b : ℝ} (hx : T.PrefixLe x n b) : T.PrefixLe (-x) n b := by
  obtain ⟨c, hc₁, hc₂⟩ := T.exists_prefix_max x n
  by_cases hc : c = 0
  · subst hc
    rw [norm_zero] at hc₁
    exact T.prefixLe_of_mem_span (neg_mem (T.mem_span_of_prefixLe_zero hc₁)) hx.nonneg
  · obtain ⟨u, hu, hxu⟩ := (T.prefixLe_iff_exists hc).1 hc₁
    refine ((T.prefixLe_iff_exists hc).2 ⟨-u, neg_mem hu, ?_⟩).mono (hc₂ b hx)
    have := neg_mem hxu
    rwa [show -(x - T.teich c * u) = -x - T.teich c * (-u) by ring] at this
end GroundTheory.PAdicHodge.TeichLift
