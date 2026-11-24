-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.gjInt_smul_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:21.488838+00:00
-- url     : https://prove2.me/submissions/00d5e708-94fc-472b-9ee8-47665b573530

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
variable [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  {m : Measure (GL (Fin r) k)} {μ : kˣ →* ℂˣ} {σ : Representation ℂ (GL (Fin r) k) V}
  {Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
variable (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
include hσ hs hp hu
omit hσ hs hp hu [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
namespace GlobalTheory.GodementJacquet
theorem _root_.solution (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ) (h : GL (Fin (r + t)) k) (c : ℂ) (v w : V) :
    gjInt m μ σ Bf (c • Φ) h v w = c * gjInt m μ σ Bf Φ h v w := by
  simp only [gjInt]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [om, Pi.smul_apply, smul_eq_mul]
  ring
end GlobalTheory.GodementJacquet
