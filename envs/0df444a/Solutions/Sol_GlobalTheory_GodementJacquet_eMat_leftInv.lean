-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.eMat_leftInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:15.225386+00:00
-- url     : https://prove2.me/submissions/dd341c13-d103-44c4-9b84-69dbf3064ac6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableZetaIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet Matrix
open GlobalTheory GlobalTheory.GodementJacquet
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.GodementJacquet
theorem _root_.solution (r t : ℕ) :
    (Matrix.of fun (i : Fin r) (j : Fin (r + t)) => if (j : ℕ) = i then (1 : k) else 0) * eMat k r t = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castAdd t i)]
  · simp [eMat, Matrix.one_apply, Fin.ext_iff]
  · intro b _ hb
    rw [Matrix.of_apply, if_neg, zero_mul]
    intro hh; exact hb (Fin.ext (by simpa using hh))
  · simp
end GlobalTheory.GodementJacquet
