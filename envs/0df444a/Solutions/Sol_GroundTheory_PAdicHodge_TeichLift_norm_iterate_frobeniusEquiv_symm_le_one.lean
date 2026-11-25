-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.norm_iterate_frobeniusEquiv_symm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:58.115145+00:00
-- url     : https://prove2.me/submissions/5766858b-88ef-499b-b7c6-4a6cc617df6e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_norm_iterate_frobeniusEquiv_symm_pow

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
theorem _root_.solution {a : L} (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖((((frobeniusEquiv L p).symm : L →+* L))^[n] a)‖ ≤ 1 := by
  have h := norm_iterate_frobeniusEquiv_symm_pow a n
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero)).1 (h ▸ ha)
end GroundTheory.PAdicHodge.TeichLift
