-- Prove2me | solution 1 for GlobalTheory.JetTest.jetScale_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:56:19.80526+00:00
-- url     : https://prove2.me/submissions/c197ec7e-096d-4925-9739-3b1eb8ce21d4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_JetTruncNotInjective
import Theorems.Thm_GlobalTheory_JetTest_jetMap_mk

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
theorem _root_.solution (c : ι → R) (i : ι) :
    (jetScale c : Jet R ι m →ₐ[R] Jet R ι m) (Ideal.Quotient.mk _ (X i)) =
      c i • (Ideal.Quotient.mk _ (X i) : Jet R ι m) := by
  rw [jetScale, jetMap_mk, aeval_X, Algebra.smul_def, map_mul]
  rfl
end GlobalTheory.JetTest
