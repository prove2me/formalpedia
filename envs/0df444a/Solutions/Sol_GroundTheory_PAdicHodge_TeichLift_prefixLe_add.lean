-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.prefixLe_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:30.392725+00:00
-- url     : https://prove2.me/submissions/acb7ae66-e5d1-46c6-aa81-f860c6f49aa0

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
theorem _root_.solution {x y : Γ} {n : ℕ} {b : ℝ} (hx : T.PrefixLe x n b) (hy : T.PrefixLe y n b) :
    T.PrefixLe (x + y) n b := by
  obtain ⟨c₁, h₁, h₁'⟩ := T.exists_prefix_max x n
  obtain ⟨c₂, h₂, h₂'⟩ := T.exists_prefix_max y n
  obtain ⟨c, hcx, hcy, hcb⟩ : ∃ c : L, T.PrefixLe x n ‖c‖ ∧ T.PrefixLe y n ‖c‖ ∧ ‖c‖ ≤ b := by
    rcases le_total ‖c₁‖ ‖c₂‖ with h | h
    · exact ⟨c₂, h₁.mono h, h₂, h₂' b hy⟩
    · exact ⟨c₁, h₁, h₂.mono h, h₁' b hx⟩
  by_cases hc : c = 0
  · subst hc
    rw [norm_zero] at hcx hcy
    exact T.prefixLe_of_mem_span (add_mem (T.mem_span_of_prefixLe_zero hcx)
      (T.mem_span_of_prefixLe_zero hcy)) hx.nonneg
  · obtain ⟨u, hu, hxu⟩ := (T.prefixLe_iff_exists hc).1 hcx
    obtain ⟨v, hv, hyv⟩ := (T.prefixLe_iff_exists hc).1 hcy
    refine ((T.prefixLe_iff_exists hc).2 ⟨u + v, add_mem hu hv, ?_⟩).mono hcb
    have := add_mem hxu hyv
    rwa [show x - T.teich c * u + (y - T.teich c * v) = x + y - T.teich c * (u + v) by ring] at this
end GroundTheory.PAdicHodge.TeichLift
