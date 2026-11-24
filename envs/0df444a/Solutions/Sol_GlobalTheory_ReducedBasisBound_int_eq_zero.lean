-- Prove2me | solution 1 for GlobalTheory.ReducedBasisBound.int_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:09.653623+00:00
-- url     : https://prove2.me/submissions/f3b29530-6d07-4b66-8233-9da5a8a1d893

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.ReducedBasisBound
namespace GlobalTheory.ReducedBasisBound
theorem _root_.solution {x : ℤ} (h : |(x : ℝ)| < 1) : x = 0 := by
  have : |x| < 1 := by exact_mod_cast h
  exact Int.abs_lt_one_iff.mp this
end GlobalTheory.ReducedBasisBound
