-- Prove2me | solution 1 for GlobalTheory.JetTest.X_pow_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:56:48.214261+00:00
-- url     : https://prove2.me/submissions/a4df046b-8887-45a0-9c74-2d1fe593a98f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_JetTruncNotInjective
import Theorems.Thm_GlobalTheory_JetTest_mk_eq_zero_iff

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
    (Ideal.Quotient.mk _ (X i ^ m) : Jet R ι m) ≠ 0 := by
  classical
  rw [Ne, mk_eq_zero_iff]
  intro h
  have := h (Finsupp.single i m) (by simp)
  simp [X_pow_eq_monomial] at this
end GlobalTheory.JetTest
