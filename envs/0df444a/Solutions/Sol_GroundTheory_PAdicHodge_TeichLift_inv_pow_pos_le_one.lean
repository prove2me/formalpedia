-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.inv_pow_pos_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:39.021683+00:00
-- url     : https://prove2.me/submissions/2cceb4c4-d721-4617-98dc-069fdb6884ea

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
theorem _root_.solution (k : ℕ) : 0 < ((p ^ k : ℕ) : ℝ)⁻¹ ∧ ((p ^ k : ℕ) : ℝ)⁻¹ ≤ 1 := by
  have h1 : (1 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow k p hp.out.pos
  exact ⟨inv_pos.2 (by linarith), inv_le_one_of_one_le₀ h1⟩
end GroundTheory.PAdicHodge.TeichLift
