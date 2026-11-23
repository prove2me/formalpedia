-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.sub_partialSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:51.259834+00:00
-- url     : https://prove2.me/submissions/e91b47e6-65f8-495d-950f-f101997a2950

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_sub_teich_eq___mul_tail_219974f30227
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_succ
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_finSum_succ__591efcd7936f

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
theorem _root_.solution (x : Γ) (n : ℕ) : x - T.partialSum x n = T.π ^ n * T.tail^[n] x := by
  induction n generalizing x with
  | zero => simp [partialSum]
  | succ n ih =>
    have h1 : T.partialSum x (n + 1) = T.teich (T.red x) + T.π * T.partialSum (T.tail x) n := by
      simp only [partialSum, finSum_succ', coeff_zero, coeff_succ]
    rw [h1, Function.iterate_succ_apply, pow_succ', mul_assoc, ← ih]
    calc x - (T.teich (T.red x) + T.π * T.partialSum (T.tail x) n)
        = (x - T.teich (T.red x)) - T.π * T.partialSum (T.tail x) n := by ring
      _ = T.π * T.tail x - T.π * T.partialSum (T.tail x) n := by rw [T.sub_teich_eq_π_mul_tail]
      _ = T.π * (T.tail x - T.partialSum (T.tail x) n) := by ring
end GroundTheory.PAdicHodge.TeichLift
