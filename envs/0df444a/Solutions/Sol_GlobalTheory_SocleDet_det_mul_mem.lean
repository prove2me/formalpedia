-- Prove2me | solution 1 for GlobalTheory.SocleDet.det_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:39.535789+00:00
-- url     : https://prove2.me/submissions/8886f4ca-c9a2-4aa1-98ec-975feb482d70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Theorems.Thm_GlobalTheory_SocleDet_det_mul_sub_adjugate_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SocleDet
open Matrix
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.SocleDet
theorem _root_.solution (I : Ideal R) (M : Matrix n n R) (x : n → R) (l : n)
    (h : ∀ r, (M *ᵥ x) r ∈ I) : M.det * x l ∈ I := by
  have := det_mul_sub_adjugate_mul_mem I M x l l fun r _ => h r
  have h2 := I.add_mem this (I.mul_mem_left (M.adjugate l l) (h l))
  simpa using h2
end GlobalTheory.SocleDet
