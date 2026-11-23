-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.finSum_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:13.561559+00:00
-- url     : https://prove2.me/submissions/61ea5b1a-e380-4d1f-8468-b91ba6345306

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich

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
theorem _root_.solution {a b : ℕ → L} {n : ℕ} (h : ∀ i < n, a i = b i) :
    T.finSum a n = T.finSum b n :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]
end GroundTheory.PAdicHodge.TeichLift
