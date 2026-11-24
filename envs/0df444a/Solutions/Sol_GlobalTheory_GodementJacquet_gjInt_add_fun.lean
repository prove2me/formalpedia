-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.gjInt_add_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:47.37392+00:00
-- url     : https://prove2.me/submissions/530f80a6-8d83-4711-9756-ef64574822c0

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
namespace GlobalTheory.GodementJacquet
theorem _root_.solution {Φ Ψ : Matrix (Fin (r + t)) (Fin r) k → ℂ} {h : GL (Fin (r + t)) k}
    (hf : Integrable (fun g => om μ g h Φ (eMat k r t)) m)
    (hg : Integrable (fun g => om μ g h Ψ (eMat k r t)) m) (v w : V) :
    gjInt m μ σ Bf (Φ + Ψ) h v w = gjInt m μ σ Bf Φ h v w + gjInt m μ σ Bf Ψ h v w := by
  simp only [gjInt]
  rw [← integral_add (integrable_mul_coef hσ hs hp hu hf _ _) (integrable_mul_coef hσ hs hp hu hg _ _)]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only [om, Pi.add_apply]
  ring
end GlobalTheory.GodementJacquet
