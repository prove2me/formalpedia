-- Prove2me | solution 1 for GlobalTheory.JetTest.X_pow_succ_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:24:54.638797+00:00
-- url     : https://prove2.me/submissions/17e856d7-a5a0-4d86-8630-fc41bc5872ed

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_JetTruncNotInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JetTest
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}
namespace GlobalTheory.JetTest
theorem _root_.solution (i : ι) :
    (Ideal.Quotient.mk _ (X i ^ (m + 1)) : Jet R ι m) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (X_mem_orig i) _)
end GlobalTheory.JetTest
