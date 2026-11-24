-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.gjInt_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:48.969779+00:00
-- url     : https://prove2.me/submissions/bb4497c2-6690-498d-a256-4f07524a2ad7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul


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
variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
namespace GlobalTheory.GodementJacquet
theorem _root_.solution [m.IsMulRightInvariant] (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
    (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ) (h : GL (Fin (r + t)) k) (g₀ : GL (Fin r) k) (v w : V) :
    gjInt m μ σ Bf (om μ g₀ 1 Φ) h v w = gjInt m μ σ Bf Φ h v (σ g₀⁻¹ w) := by
  simp only [gjInt]
  rw [← integral_mul_right_eq_self (μ := m)
    (fun x => om μ x h Φ (eMat k r t) * coef σ Bf v (σ g₀⁻¹ w) x) g₀]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  have h1 := om_mul μ g g₀ h 1 Φ
  rw [mul_one] at h1
  simp only [h1, coef]
  rw [mul_inv_rev, map_mul, Module.End.mul_apply, hu]
end GlobalTheory.GodementJacquet
