-- Prove2me | solution 1 for GlobalTheory.JetTest.jetTan_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:48.798282+00:00
-- url     : https://prove2.me/submissions/d8da517f-e75d-4f85-94d2-f590dbb1bcda

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
theorem _root_.solution [DecidableEq ι] (l i : ι) :
    (jetTan l : Jet R ι (m + 1) →ₐ[R] DualNumber R) (Ideal.Quotient.mk _ (X i)) =
      if i = l then DualNumber.eps else 0 := by
  change aeval _ (X i) = _
  rw [aeval_X]
end GlobalTheory.JetTest
