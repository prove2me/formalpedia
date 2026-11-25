-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.teich_mem_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:39.192289+00:00
-- url     : https://prove2.me/submissions/4c55a708-0e8e-4950-98f2-95df4d85b7d2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_span_pow_anti
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_sub_pow_mem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_norm_iterate_frobeniusEquiv_symm_le_one

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
theorem _root_.solution {a : L} (ha : ‖a‖ ≤ 1) : T.teich a ∈ T.int := by
  refine T.mem_int_of_approx _ fun N => ?_
  obtain ⟨z, hz, hzb⟩ := T.exists_mem_int _ (norm_iterate_frobeniusEquiv_symm_le_one ha N)
  exact ⟨z ^ p ^ N, pow_mem hz _, T.span_pow_anti (Nat.le_succ N) (T.teich_sub_pow_mem a N z hzb)⟩
end GroundTheory.PAdicHodge.TeichLift
