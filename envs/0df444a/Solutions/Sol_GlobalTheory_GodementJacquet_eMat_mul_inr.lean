-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.eMat_mul_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:45:34.529788+00:00
-- url     : https://prove2.me/submissions/510f35ef-7f38-4606-948b-31c9e300937a

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
theorem _root_.solution (Y : Matrix (Fin r) β k) (i : Fin t) (j : β) :
    (eMat k r t * Y) (stdSum (rfl : r + t = r + t) (Sum.inr i)) j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  have : r + (i : ℕ) ≠ l := by omega
  simp [eMat, this]
end GlobalTheory.GodementJacquet
