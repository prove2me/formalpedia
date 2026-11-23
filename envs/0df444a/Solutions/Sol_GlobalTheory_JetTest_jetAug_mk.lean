-- Prove2me | solution 1 for GlobalTheory.JetTest.jetAug_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:08.855898+00:00
-- url     : https://prove2.me/submissions/4057eb91-e98a-4861-8f25-748ce525a85b

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
theorem _root_.solution (p : MvPolynomial ι R) :
    (jetAug : Jet R ι m →ₐ[R] R) (Ideal.Quotient.mk _ p) = constantCoeff p := by
  change aeval (fun _ => (0 : R)) p = _
  simp
end GlobalTheory.JetTest
