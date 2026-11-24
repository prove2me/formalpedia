-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.abstract_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:50.815839+00:00
-- url     : https://prove2.me/submissions/c978cbc3-46a4-4917-b409-ef043f7e4e83

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
theorem _root_.solution {H A X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup A] [Module ℂ A] [AddCommGroup X] [Module ℂ X]
    (I : Representation ℂ H A) (π : Representation ℂ H X) (Ψ : I.Equiv (contra π)) :
    ∃ P : A →ₗ[ℂ] X →ₗ[ℂ] ℂ, (∀ h a f, P (I h a) (π h f) = P a f) ∧
      ∀ a, (∀ f, P a f = 0) → a = 0 := by
  refine ⟨(smoothPart π.dual).subtype ∘ₗ Ψ.toLinearEquiv.toLinearMap, fun h a f => ?_, fun a h => ?_⟩
  · have e1 : Ψ.toLinearEquiv (I h a) = contra π h (Ψ.toLinearEquiv a) :=
      LinearMap.congr_fun (Ψ.isIntertwining' h) a
    show (Ψ.toLinearEquiv (I h a)).1 _ = (Ψ.toLinearEquiv a).1 f
    rw [e1]
    show (Ψ.toLinearEquiv a).1 (π h⁻¹ _) = _
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · have : Ψ.toLinearEquiv a = 0 := Subtype.ext (LinearMap.ext h)
    exact (LinearEquiv.map_eq_zero_iff _).1 this
end GlobalTheory.GodementJacquet
