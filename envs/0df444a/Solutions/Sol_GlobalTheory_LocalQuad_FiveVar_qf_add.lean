-- Prove2me | solution 1 for GlobalTheory.LocalQuad.FiveVar.qf_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:45.107433+00:00
-- url     : https://prove2.me/submissions/7d684542-0798-4aa3-9421-5984d829064e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.FiveVar
variable {K : Type*} [Field K] {n : Type*} [Fintype n]
namespace GlobalTheory.LocalQuad.FiveVar
theorem _root_.solution (a x y : n → K) : qf a (x + y) = qf a x + bf a x y + qf a y := by
  simp only [qf, bf, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.LocalQuad.FiveVar
