-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.span_pow_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:50.293029+00:00
-- url     : https://prove2.me/submissions/ba43fa85-828c-41aa-b26b-a9e57147d738

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
theorem _root_.solution {m n : ℕ} (h : n ≤ m) : Ideal.span {T.π ^ m} ≤ Ideal.span {T.π ^ n} := by
  intro x hx
  obtain ⟨y, rfl⟩ := T.mem_span_pow.1 hx
  exact T.π_pow_mul_mem h y
end GroundTheory.PAdicHodge.TeichLift
