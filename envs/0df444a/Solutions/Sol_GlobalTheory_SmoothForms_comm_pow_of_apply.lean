-- Prove2me | solution 1 for GlobalTheory.SmoothForms.comm_pow_of_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:51:55.983864+00:00
-- url     : https://prove2.me/submissions/0e67ad86-b474-486a-9b73-79e8dd4ec611

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PowEntryCommutator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Theorems.Thm_GlobalTheory_PowEntryCommutator_target


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
variable {A : Type} [Ring A] {n : ℕ}
namespace GlobalTheory.SmoothForms
theorem _root_.solution (E : Fin n → Fin n → A) (hE : Formalism.REAL.GlRel E) (a b : Fin n) (m : ℕ)
    (c e : Fin n) : E a b * (Matrix.of E ^ m) c e - (Matrix.of E ^ m) c e * E a b =
      (if b = c then (Matrix.of E ^ m) a e else 0) - (if e = a then (Matrix.of E ^ m) c b else 0) := by
  first
  | exact @_root_.GlobalTheory.PowEntryCommutator.target
  | exact _root_.GlobalTheory.PowEntryCommutator.target
  | (apply _root_.GlobalTheory.PowEntryCommutator.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowEntryCommutator.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowEntryCommutator.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowEntryCommutator.target ..)
end GlobalTheory.SmoothForms
