-- Prove2me | solution 1 for GlobalTheory.LocalQuad.FiveVar.bf_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:49:06.877741+00:00
-- url     : https://prove2.me/submissions/2f8e5cc2-3730-4c5b-8ab2-07e51f761591

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
theorem _root_.solution (a x y z : n → K) : bf a (x + y) z = bf a x z + bf a y z := by
  simp only [bf, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.LocalQuad.FiveVar
