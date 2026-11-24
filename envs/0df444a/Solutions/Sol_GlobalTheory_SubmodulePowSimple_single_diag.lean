-- Prove2me | solution 1 for GlobalTheory.SubmodulePowSimple.single_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:58:44.553057+00:00
-- url     : https://prove2.me/submissions/339846b5-e353-4a48-b10a-c264013d9968

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open GlobalTheory GlobalTheory.SubmodulePowSimple
variable {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type}
namespace GlobalTheory.SubmodulePowSimple
theorem _root_.solution {m : ℕ} (b : Module.End ℂ P) (p : P) :
    (Pi.single (Fin.last m) (b p) : Fin (m+1) → P) = fun j => b ((Pi.single (Fin.last m) p : Fin (m+1) → P) j) := by
  funext j
  by_cases h : j = Fin.last m
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]
end GlobalTheory.SubmodulePowSimple
