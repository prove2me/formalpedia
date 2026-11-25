-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.coeff_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:46:35.104303+00:00
-- url     : https://prove2.me/submissions/4c25b7a5-0b1b-43f5-9f96-366dd9178c0b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___pow_mul_of_lt_398143255abf

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
theorem _root_.solution {x : Γ} {n : ℕ} (h : x ∈ Ideal.span {T.π ^ (n + 1)}) :
    ∀ m ≤ n, T.coeff x m = 0 := by
  intro m hm
  obtain ⟨y, rfl⟩ := T.mem_span_pow.1 h
  exact T.coeff_π_pow_mul_of_lt y (by omega)
end GroundTheory.PAdicHodge.TeichLift
