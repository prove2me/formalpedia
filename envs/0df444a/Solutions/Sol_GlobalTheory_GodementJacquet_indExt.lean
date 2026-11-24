-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.indExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:31:24.394399+00:00
-- url     : https://prove2.me/submissions/f1957951-74ad-42b2-b079-f1bc0287da7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HermitianFormNormSqLeReMulReStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwist
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two


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
variable [m.IsMulLeftInvariant] (hσ : IsSmooth σ) (hs : ∀ v w, Bf w v = starRingEnd ℂ (Bf v w))
    (hp : ∀ v, v ≠ 0 → 0 < (Bf v v).re) (hu : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w)
    (hI : ∀ (h : GL (Fin (r + t)) k) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ),
      Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) →
      Integrable (fun g : GL (Fin r) k => om μ g h Φ (eMat k r t)) m)
omit [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] [SecondCountableTopology (GL (Fin r) k)]
  [m.IsMulLeftInvariant]
namespace GlobalTheory.GodementJacquet
theorem _root_.solution {F₁ F₂ : IndSp (two (stdSum (rfl : r + t = r + t))) (contra (leviRep t μ σ))}
    (H : ∀ h x, (F₁.1.1 h).1 x = (F₂.1.1 h).1 x) : F₁ = F₂ :=
  Subtype.ext (Subtype.ext (funext fun h => Subtype.ext (LinearMap.ext (H h))))
end GlobalTheory.GodementJacquet
