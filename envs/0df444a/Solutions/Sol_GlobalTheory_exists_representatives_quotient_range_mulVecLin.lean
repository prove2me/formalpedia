-- Prove2me | solution 1 for GlobalTheory.exists_representatives_quotient_range_mulVecLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:00:13.722974+00:00
-- url     : https://prove2.me/submissions/ca49ec17-fecd-4c6a-b8a2-26fb2e3b1959

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Theorems.Thm_GlobalTheory_natCard_quotient_range_mulVecLin
import Theorems.Thm_GlobalTheory_finite_quotient_range_mulVecLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {b d : Matrix n n ℤ}
namespace GlobalTheory
theorem _root_.solution (hd : d.det ≠ 0) :
    ∃ r : Fin d.det.natAbs → n → ℤ, Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (n → ℤ) ⧸ LinearMap.range d.mulVecLin) := by
  haveI := finite_quotient_range_mulVecLin hd
  let e := (Finite.equivFinOfCardEq (natCard_quotient_range_mulVecLin hd)).symm
  refine ⟨fun k => (e k).out, ?_⟩
  convert e.bijective using 2
  exact Submodule.Quotient.mk_out _
end GlobalTheory
