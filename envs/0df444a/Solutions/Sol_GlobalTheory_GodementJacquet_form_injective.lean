-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.form_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:50.918837+00:00
-- url     : https://prove2.me/submissions/3e8471e0-9134-4a9a-a36f-0a2a94db019e

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
variable {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
namespace GlobalTheory.GodementJacquet
theorem _root_.solution (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (a b : V) (h : ∀ w, Bf a w = Bf b w) :
    a = b := by
  by_contra hab
  have h1 := hp (a - b) (sub_ne_zero.2 hab)
  have h2 : Bf (a - b) (a - b) = 0 := by
    rw [Bf.map_sub a b, LinearMap.sub_apply, h, sub_self]
  rw [h2] at h1
  simp at h1
end GlobalTheory.GodementJacquet
