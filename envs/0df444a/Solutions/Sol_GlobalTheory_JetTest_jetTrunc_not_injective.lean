-- Prove2me | solution 1 for GlobalTheory.JetTest.jetTrunc_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:50.353459+00:00
-- url     : https://prove2.me/submissions/a79697f9-4ddd-40f2-bce5-27d271792e21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_JetTruncNotInjective
import Theorems.Thm_GlobalTheory_JetTest_X_pow_ne_zero
import Theorems.Thm_GlobalTheory_JetTest_X_pow_succ_eq_zero

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
theorem _root_.solution [Nontrivial R] (i : ι) :
    ¬ Function.Injective (jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m) := by
  intro h
  apply X_pow_ne_zero (R := R) (m := m + 1) i
  apply h
  rw [map_zero]
  exact X_pow_succ_eq_zero i
end GlobalTheory.JetTest
