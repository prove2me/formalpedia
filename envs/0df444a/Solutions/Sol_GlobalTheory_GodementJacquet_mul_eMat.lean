-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.mul_eMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:45:40.069773+00:00
-- url     : https://prove2.me/submissions/a4237fa8-385b-419c-b79b-8e4ef44d071e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel GlobalTheory.RootEx
open scoped TensorProduct Topology
open GlobalTheory GlobalTheory.GodementJacquet
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
local notation "e₀" => stdSum (rfl : _ + _ = _ + _)
variable {α β : Type} [Fintype α]
namespace GlobalTheory.GodementJacquet
theorem _root_.solution (X : Matrix α (Fin (r + t)) k) (i : α) (j : Fin r) :
    (X * eMat k r t) i j = X i (stdSum (rfl : r + t = r + t) (Sum.inl j)) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (stdSum (rfl : r + t = r + t) (Sum.inl j))]
  · simp [eMat]
  · intro l _ hl
    have : (l : ℕ) ≠ j := fun h => hl (Fin.ext (by simp [h]))
    simp [eMat, this]
  · simp
end GlobalTheory.GodementJacquet
