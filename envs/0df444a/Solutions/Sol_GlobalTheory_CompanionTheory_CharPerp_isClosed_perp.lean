-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharPerp.isClosed_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:22:52.996352+00:00
-- url     : https://prove2.me/submissions/57a9e273-f5f8-4420-be2d-6a7b2b318233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorOpenCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharPerp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CharPerp
theorem _root_.solution {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (A : AddSubgroup (Fin n → k)) : IsClosed (perp ψ A : Set (Fin n → k)) := by
  have : (perp ψ A : Set (Fin n → k)) =
      ⋂ a ∈ A, (fun ξ : Fin n → k => ψ (ξ ⬝ᵥ a)) ⁻¹' {1} := by
    ext ξ
    simp [perp]
  rw [this]
  refine isClosed_biInter fun a _ => isClosed_singleton.preimage ?_
  exact hψ.comp (continuous_id.dotProduct continuous_const)
end GlobalTheory.CompanionTheory.CharPerp
