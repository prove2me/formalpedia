-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.abstract_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:18.116695+00:00
-- url     : https://prove2.me/submissions/71e423a8-6275-446c-b895-4ec3a43a0d69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist
import Theorems.Thm_GlobalTheory_GodementJacquet_form_injective

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
theorem _root_.solution {S A X : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup X] [Module ℂ X] (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (P : A →ₗ[ℂ] X →ₗ[ℂ] ℂ) (F : S → V → A)
    (h1 : ∀ Φ Φ' w, F (Φ + Φ') w = F Φ w + F Φ' w) (h2 : ∀ (c : ℂ) Φ w, F (c • Φ) w = c • F Φ w)
    (h3 : ∀ Φ w w', F Φ (w + w') = F Φ w + F Φ w')
    (h4 : ∀ (c : ℂ) Φ w, F Φ (c • w) = starRingEnd ℂ c • F Φ w)
    (hR : ∀ Φ f (L : V →ₗ⋆[ℂ] ℂ), (∀ w, L w = P (F Φ w) f) → ∃ u, ∀ w, L w = Bf u w) :
    ∃ B : S →ₗ[ℂ] X →ₗ[ℂ] V, ∀ Φ f w, Bf (B Φ f) w = P (F Φ w) f := by
  have hL : ∀ Φ f, ∃ u : V, ∀ w, P (F Φ w) f = Bf u w := fun Φ f =>
    hR Φ f { toFun := fun w => P (F Φ w) f
             map_add' := fun w w' => by simp [h3]
             map_smul' := fun c w => by simp [h4] } fun _ => rfl
  choose u hu' using hL
  have huniq := form_injective hp
  refine ⟨LinearMap.mk₂ ℂ u
      (fun Φ Φ' f => huniq _ _ fun w => ?_) (fun c Φ f => huniq _ _ fun w => ?_)
      (fun Φ f f' => huniq _ _ fun w => ?_) (fun c Φ f => huniq _ _ fun w => ?_),
    fun Φ f w => (hu' Φ f w).symm⟩
  · simp [← hu', h1]
  · simp [← hu', h2]
  · simp [← hu']
  · simp [← hu']
end GlobalTheory.GodementJacquet
