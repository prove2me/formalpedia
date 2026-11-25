-- Prove2me | solution 1 for GlobalTheory.AinfChecks.nonempty_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:28:28.417202+00:00
-- url     : https://prove2.me/submissions/ed39fc57-a95e-4d7c-bd20-b804ad050cde

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_NonemptyAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WittVector Ideal ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.AinfChecks
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
omit [IsAdicComplete (span {(p : O)}) O]
namespace GlobalTheory.AinfChecks
theorem _root_.solution (pflat : PreTilt O p) :
    Nonempty (Algebra (ZMod (p ^ 2)) (WittVector p (PreTilt O p) ⧸
      span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat})) := by
  refine ⟨((ZMod.castHom (ringChar.dvd ?_) _)).toAlgebra⟩
  push_cast
  rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact subset_span (by simp)
end GlobalTheory.AinfChecks
