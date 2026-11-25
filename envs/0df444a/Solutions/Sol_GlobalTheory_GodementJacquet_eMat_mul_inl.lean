-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.eMat_mul_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:53:11.961944+00:00
-- url     : https://prove2.me/submissions/0c019b93-c99a-49e4-82ae-870b8bad49b4

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
theorem _root_.solution (Y : Matrix (Fin r) β k) (i : Fin r) (j : β) :
    (eMat k r t * Y) (stdSum (rfl : r + t = r + t) (Sum.inl i)) j = Y i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [eMat]
  · intro l _ hl
    have : (i : ℕ) ≠ l := fun h => hl (Fin.ext h.symm)
    simp [eMat, this]
  · simp
end GlobalTheory.GodementJacquet
