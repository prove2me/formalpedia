-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.mk_sub_finSum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:12.620593+00:00
-- url     : https://prove2.me/submissions/ab2abea8-04a6-45ff-9d37-2ca35f87045f

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
theorem _root_.solution (a : ℕ → L) (n : ℕ) : T.ofCoeff a - T.finSum a n ∈ Ideal.span {T.π ^ n} := by
  haveI := T.isAdicComplete
  have := (IsPrecomplete.prec' (I := T.I) (T.finSum a) fun {m n} hmn => by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow, ← neg_sub]
    exact neg_mem (T.finSum_sub_finSum_mem a hmn)).choose_spec n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow, ← neg_sub] at this
  simpa [ofCoeff] using neg_mem this
end GroundTheory.PAdicHodge.TeichLift
