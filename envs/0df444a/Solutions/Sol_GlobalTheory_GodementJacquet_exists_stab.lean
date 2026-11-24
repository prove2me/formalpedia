-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.exists_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:51.728351+00:00
-- url     : https://prove2.me/submissions/3bf351a5-d376-47b4-ad80-5551da93c1b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_one
import Theorems.Thm_GlobalTheory_SplitWeil_om_isSmoothRepresentation
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_one


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
  [m.IsMulLeftInvariant] [m.IsMulRightInvariant] (hσ : IsSmooth σ)
  (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
  (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
  (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
    Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
    Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)
omit [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
namespace GlobalTheory.GodementJacquet
theorem _root_.solution (hμ : IsSmoothChar μ) (Φ : SB (Matrix (Fin (r + t)) (Fin r) k)) :
    ∃ S : Subgroup (GL (Fin r) k), IsOpen (S : Set (GL (Fin r) k)) ∧ ∀ s ∈ S, om μ s 1 Φ.1 = Φ.1 := by
  have h := (om_isSmoothRepresentation k (Fin r) (Fin (r + t)) μ hμ).2.2.2.2 Φ.1 Φ.2
  have hc : Continuous fun g : GL (Fin r) k => (g, (1 : GL (Fin (r + t)) k)) :=
    continuous_id.prodMk continuous_const
  refine ⟨{ carrier := {g | om μ g 1 Φ.1 = Φ.1}
            one_mem' := om_one μ Φ.1
            mul_mem' := fun {x y} hx hy => ?_
            inv_mem' := fun {x} hx => ?_ }, h.preimage hc, fun s hs => hs⟩
  · have := om_mul μ x y (1 : GL (Fin (r + t)) k) 1 Φ.1
    rw [mul_one] at this
    show om μ (x * y) 1 Φ.1 = Φ.1
    rw [this, show om μ y 1 Φ.1 = Φ.1 from hy]
    exact hx
  · have := om_mul μ x⁻¹ x (1 : GL (Fin (r + t)) k) 1 Φ.1
    rw [mul_one, inv_mul_cancel, om_one, show om μ x 1 Φ.1 = Φ.1 from hx] at this
    exact this.symm
end GlobalTheory.GodementJacquet
