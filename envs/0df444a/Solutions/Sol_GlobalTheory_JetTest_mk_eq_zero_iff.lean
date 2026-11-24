-- Prove2me | solution 1 for GlobalTheory.JetTest.mk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:41:38.116835+00:00
-- url     : https://prove2.me/submissions/5bd7fc8d-656e-4563-b9c7-3b96887b5414

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_JetTruncNotInjective
import Theorems.Thm_GlobalTheory_JetTest_orig_eq

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
    (Ideal.Quotient.mk _ p : Jet R ι m) = 0 ↔ ∀ e : ι →₀ ℕ, e.degree ≤ m → p.coeff e = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, orig_eq, MvPolynomial.mem_pow_idealOfVars_iff']
  simp [Nat.lt_succ_iff]
end GlobalTheory.JetTest
