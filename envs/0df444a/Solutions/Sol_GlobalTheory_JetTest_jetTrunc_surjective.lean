-- Prove2me | solution 1 for GlobalTheory.JetTest.jetTrunc_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:53.509746+00:00
-- url     : https://prove2.me/submissions/244c80d5-de01-40b9-bb9d-207788b0fa71

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
theorem _root_.solution :
    Function.Surjective (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) := by
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩
end GlobalTheory.JetTest
